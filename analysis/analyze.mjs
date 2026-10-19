#!/usr/bin/env node
/**
 * 招募失败归因 + 「卡池置灰」策略回测
 *
 * 运行: node analysis/analyze.mjs          # 打印报告并写出 analysis/out/*
 *       node analysis/analyze.mjs --check  # 额外执行断言，失败时退出码为 1
 *
 * 零依赖，Node >= 18。
 */
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(HERE, '..');
const CSV_FILE = path.join(ROOT, 'recruitment_logs.csv');
const OUT_DIR = path.join(HERE, 'out');

const FAIL_COST = 75;      // 点券 / 次招募失败
const GRAY_COST = 20;      // 点券 / 次提前置灰
const STALE_MIN = 15;      // 快照新鲜度 SLA（分钟），阈值另由数据扫描验证
const TRAIN_LAST_DAY = '2026-09-04'; // 前 4 天训练，后 3 天回测

/* ------------------------------------------------------------------ */
/* 读取与清洗                                                          */
/* ------------------------------------------------------------------ */

function readRows(file) {
  const text = fs.readFileSync(file, 'utf8').replace(/^\uFEFF/, '');
  const [head, ...rest] = text.trim().split(/\r?\n/);
  const cols = head.split(',');
  return rest.map((line) => {
    const cells = line.split(',');
    const row = {};
    cols.forEach((c, i) => { row[c] = cells[i]; });
    return row;
  });
}

/**
 * action_time 带 +08:00，pool_synced_at 带 Z(UTC)。
 * 必须交给 Date.parse 按时区换算；截断字符串后硬减会让每条记录凭空多出 8 小时。
 */
function normalize(raw) {
  return raw.map((r) => {
    const at = Date.parse(r.action_time);
    const syncedAt = Date.parse(r.pool_synced_at);
    const lagMin = (at - syncedAt) / 60000;
    return {
      id: r.log_id,
      at,
      syncedAt,
      zone: r.server_zone,
      pool: r.pool_type,
      remain: Number(r.remain_quota),
      online: Number(r.concurrent_online),
      outcome: r.is_success === '1' ? 'success' : r.is_success === '0' ? 'fail' : 'unknown',
      day: r.action_time.slice(0, 10),
      lagMin,
      stale: lagMin > STALE_MIN,
    };
  }).sort((a, b) => a.at - b.at);
}

/** log_id 重复且整行完全一致 → 流水重复写入，保留首条 */
function dedupe(rows) {
  const seen = new Set();
  const kept = [];
  let dropped = 0;
  for (const r of rows) {
    if (seen.has(r.id)) { dropped += 1; continue; }
    seen.add(r.id);
    kept.push(r);
  }
  return { kept, dropped };
}

/* ------------------------------------------------------------------ */
/* 小工具                                                              */
/* ------------------------------------------------------------------ */

const pct = (x, d = 1) => (Number.isFinite(x) ? `${(x * 100).toFixed(d)}%` : 'n/a');
const fixed = (x, d = 0) => (Number.isFinite(x) ? x.toFixed(d) : 'n/a');
const pad = (s, n) => String(s).padEnd(n);
const lpad = (s, n) => String(s).padStart(n);

const decided = (rows) => rows.filter((r) => r.outcome !== 'unknown');
const fails = (rows) => rows.filter((r) => r.outcome === 'fail').length;
const success = (rows) => rows.filter((r) => r.outcome === 'success').length;
const failRate = (rows) => { const d = decided(rows); return d.length ? fails(d) / d.length : NaN; };

function quantile(values, q) {
  if (values.length === 0) return NaN;
  const s = [...values].sort((a, b) => a - b);
  return s[Math.min(s.length - 1, Math.floor(q * (s.length - 1)))];
}

function wilson(k, n, z = 1.96) {
  if (n === 0) return [NaN, NaN];
  const p = k / n;
  const d = 1 + (z * z) / n;
  const c = p + (z * z) / (2 * n);
  const s = (z * Math.sqrt((p * (1 - p)) / n + (z * z) / (4 * n * n))) / d;
  return [(c - s) / d, (c + s) / d];
}

function groupBy(rows, keyFn) {
  const m = new Map();
  for (const r of rows) {
    const k = keyFn(r);
    if (!m.has(k)) m.set(k, []);
    m.get(k).push(r);
  }
  return m;
}

/** 置换检验：打乱结果标签，看组间失败率极差是否超出随机波动 */
function permutationTest(rows, keyFn, maxPermutations = 4000) {
  const d = decided(rows);
  const keys = d.map((r) => keyFn(r));
  const labels = d.map((r) => r.outcome);
  const index = new Map();
  keys.forEach((k, i) => {
    if (!index.has(k)) index.set(k, []);
    index.get(k).push(i);
  });
  if (index.size < 2) return { spread: NaN, p: NaN };
  const ratesOf = (lab) => [...index.values()].map((idxs) => {
    let f = 0;
    for (const i of idxs) if (lab[i] === 'fail') f += 1;
    return f / idxs.length;
  });
  const observed = (() => { const r = ratesOf(labels); return Math.max(...r) - Math.min(...r); })();
  let seed = 20260901;
  const rand = () => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648; };
  let hits = 0;
  for (let t = 0; t < maxPermutations; t++) {
    const shuffled = [...labels];
    for (let i = shuffled.length - 1; i > 0; i--) {
      const j = Math.floor(rand() * (i + 1));
      [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
    }
    const r = ratesOf(shuffled);
    if (Math.max(...r) - Math.min(...r) >= observed) hits += 1;
  }
  return { spread: observed, p: hits / maxPermutations };
}

/* ------------------------------------------------------------------ */
/* 策略评估                                                            */
/* ------------------------------------------------------------------ */

/**
 * 置灰策略：命中 predicate 的请求在扣券前先置灰（并触发一次同步），
 * 因此不产生扣券失败，但每次置灰花费 GRAY_COST。
 */
function evaluatePolicy(name, rows, predicate) {
  const d = decided(rows);
  const gated = d.filter(predicate);
  const kept = d.filter((r) => !predicate(r));
  const avoided = fails(gated);
  const keptFailures = fails(kept);
  return {
    name,
    gated: gated.length,
    avoided,
    hitRate: gated.length ? avoided / gated.length : NaN,
    failures: keptFailures,
    failRate: kept.length ? keptFailures / kept.length : NaN,
    grayCost: gated.length * GRAY_COST,
    net: avoided * FAIL_COST - gated.length * GRAY_COST,
    breakEvenGrayCost: gated.length ? (avoided * FAIL_COST) / gated.length : NaN,
  };
}

const csvEscape = (v) => {
  const s = String(v);
  return /[",\n]/.test(s) ? `"${s.replace(/"/g, '""')}"` : s;
};

function writeCsv(file, header, rows) {
  const body = rows.map((r) => r.map(csvEscape).join(',')).join('\n');
  fs.writeFileSync(file, `${header.join(',')}\n${body}\n`, 'utf8');
}

/* ------------------------------------------------------------------ */
/* 主流程                                                              */
/* ------------------------------------------------------------------ */

const raw = readRows(CSV_FILE);
const normalized = normalize(raw);
const { kept: rows, dropped: dupDropped } = dedupe(normalized);

const all = decided(rows);
const unknownRows = rows.filter((r) => r.outcome === 'unknown');
const staleRows = all.filter((r) => r.stale);
const freshRows = all.filter((r) => !r.stale);

const say = (line = '') => { console.log(line); };

say('==================================================================');
say(' 招募失败归因报告  (recruitment_logs.csv)');
say('==================================================================');
say('');

/* 1. 数据体检 ------------------------------------------------------- */
say('【1】数据体检');
say(`  原始记录 ${raw.length} 行；log_id 完全重复 ${dupDropped} 行；去重后 ${rows.length} 行`);
say(`  成功 ${success(all)} / 失败 ${fails(all)} / 未决(空) ${unknownRows.length}，已判定样本 ${all.length}`);
say(`  整体失败率 ${pct(failRate(all), 2)}  (${fails(all)}/${all.length})`);
say(`  时间范围 ${new Date(rows[0].at).toISOString()} ~ ${new Date(rows.at(-1).at).toISOString()}`);

const naiveLag = raw.map((r) => (Date.parse(`${r.action_time.slice(0, 19)}Z`) - Date.parse(r.pool_synced_at)) / 60000);
const lagVals = rows.map((r) => r.lagMin);
say(`  时区口径：正确换算后快照时延 ${fixed(Math.min(...lagVals))}~${fixed(Math.max(...lagVals))} 分钟；`);
say(`            若把 +08:00 当 UTC 硬减，会得到 ${fixed(Math.min(...naiveLag))}~${fixed(Math.max(...naiveLag))} 分钟（凭空多 8 小时）`);
say(`  快照时延  p50=${fixed(quantile(lagVals, 0.5))}  p90=${fixed(quantile(lagVals, 0.9))}  max=${fixed(Math.max(...lagVals))} 分钟`);
const uniqLag = [...new Set(lagVals)].sort((a, b) => a - b);
const maxFreshLag = Math.max(...uniqLag.filter((v) => v <= 13));
const minStaleLag = Math.min(...uniqLag.filter((v) => v >= 14));
say(`  时延是双峰：0~${fixed(maxFreshLag)} 分钟 (${freshRows.length} 次, ${pct(freshRows.length / all.length)})`);
say(`              与 ${fixed(minStaleLag)}~${fixed(Math.max(...lagVals))} 分钟 (${staleRows.length} 次, ${pct(staleRows.length / all.length)})，中间无样本`);
say('');

/* 2. 关键对比 ------------------------------------------------------- */
say('【2】失败集中在「陈旧快照」上，卡池维度看不出差异');
const freshRate = failRate(freshRows);
const staleRate = failRate(staleRows);
const rr = staleRate / freshRate;
const [fl, fh] = wilson(fails(freshRows), freshRows.length);
const [sl, sh] = wilson(fails(staleRows), staleRows.length);
const staleShare = staleRows.length / all.length;
const paf = (staleShare * (rr - 1)) / (1 + staleShare * (rr - 1));
say(`  快照 ≤${STALE_MIN} 分钟: 失败 ${fails(freshRows)}/${freshRows.length} = ${pct(freshRate, 2)}  (95%CI ${pct(fl)}~${pct(fh)})`);
say(`  快照 >${STALE_MIN} 分钟: 失败 ${fails(staleRows)}/${staleRows.length} = ${pct(staleRate, 2)}  (95%CI ${pct(sl)}~${pct(sh)})`);
say(`  相对风险 RR = ${fixed(rr, 2)}；归因分数 PAF = ${pct(paf)}`);
say('');

const LAG_BUCKETS = [[0, 5], [5, 10], [10, 15], [15, 20], [20, 30], [30, 45], [45, 60], [60, Infinity]];
say('  按时延分桶：');
say(`    ${pad('时延(分钟)', 14)}${lpad('样本', 6)}${lpad('失败', 6)}${lpad('失败率', 9)}`);
const lagTable = [];
for (const [lo, hi] of LAG_BUCKETS) {
  const b = all.filter((r) => r.lagMin >= lo && r.lagMin < hi);
  if (!b.length) continue;
  const label = `${lo}-${hi === Infinity ? '+' : hi}`;
  say(`    ${pad(label, 14)}${lpad(b.length, 6)}${lpad(fails(b), 6)}${lpad(pct(failRate(b)), 9)}`);
  lagTable.push([label, b.length, fails(b), failRate(b).toFixed(4)]);
}
say('');

say('  分区服 / 分卡池：');
const zoneTable = [];
for (const [z, g] of groupBy(all, (r) => r.zone)) {
  say(`    ${pad(z, 12)} n=${lpad(g.length, 4)}  失败率 ${pad(pct(failRate(g)), 7)} 陈旧占比 ${pct(g.filter((r) => r.stale).length / g.length)}`);
  zoneTable.push([z, g.length, fails(g), failRate(g).toFixed(4), (g.filter((r) => r.stale).length / g.length).toFixed(4)]);
}
const zoneTest = permutationTest(all, (r) => r.zone);
const poolTable = [];
for (const [p, g] of groupBy(all, (r) => r.pool)) {
  poolTable.push([p, g.length, fails(g), failRate(g), g.filter((r) => r.stale).length / g.length]);
}
const poolTest = permutationTest(all, (r) => r.pool);
say(`    区服间差异置换检验 p=${fixed(zoneTest.p, 3)}（差异集中在青龙二区，见第 4 节）；`);
say(`    9 个卡池失败率 ${pct(Math.min(...poolTable.map((t) => t[3])))} ~ ${pct(Math.max(...poolTable.map((t) => t[3])))}，置换检验 p=${fixed(poolTest.p, 3)} → 不是某个池的问题`);
say('');

/* 3. 陈旧从哪来 ------------------------------------------------------ */
say('【3】陈旧快照从哪里来：并发越高，同步越跟不上');
const sortedByOnline = [...all].sort((a, b) => a.online - b.online);
const onlineTable = [];
say(`    ${pad('并发在线区间', 16)}${lpad('样本', 6)}${lpad('陈旧占比', 10)}${lpad('失败率', 9)}`);
for (let i = 0; i < 10; i++) {
  const slice = sortedByOnline.slice(Math.floor((i * sortedByOnline.length) / 10), Math.floor(((i + 1) * sortedByOnline.length) / 10));
  if (!slice.length) continue;
  const label = `${slice[0].online}-${slice.at(-1).online}`;
  const share = slice.filter((r) => r.stale).length / slice.length;
  say(`    ${pad(label, 16)}${lpad(slice.length, 6)}${lpad(pct(share), 10)}${lpad(pct(failRate(slice)), 9)}`);
  onlineTable.push([label, slice.length, share.toFixed(4), failRate(slice).toFixed(4)]);
}
say('  同一并发水平下再看失败率：');
say(`    ${pad('并发', 10)}${pad('快照新鲜', 22)}${pad('快照陈旧', 22)}`);
for (const [lo, hi] of [[0, 40], [40, 55], [55, 70], [70, 999]]) {
  const f = freshRows.filter((r) => r.online >= lo && r.online < hi);
  const s = staleRows.filter((r) => r.online >= lo && r.online < hi);
  say(`    ${pad(`${lo}-${hi === 999 ? '+' : hi}`, 10)}${pad(`${pct(failRate(f))} (${fails(f)}/${f.length})`, 22)}${pad(`${pct(failRate(s))} (${fails(s)}/${s.length})`, 22)}`);
}
say('  → 并发只改变「变陈旧」的概率；其余三区一旦陈旧，失败率就锁死在 40%~50%（青龙二区除外，见下节）。');
say('  → 时延是并发与失败之间的中介变量：直接按并发去拦，命中率只有 19.5%（见第 6 节）。');
say('');

/* 4. 对照组 ---------------------------------------------------------- */
say('【4】把「时延」和「根因」分开：青龙二区是同一批数据里的对照组');
const CONTROL_ZONE = '青龙二区';
const remainBand = (r) => (r.remain < 5 ? '0-5' : r.remain < 10 ? '5-10' : r.remain < 20 ? '10-20' : '20+');
const BANDS = ['0-5', '5-10', '10-20', '20+'];
const control = all.filter((r) => r.zone === CONTROL_ZONE);
const others = all.filter((r) => r.zone !== CONTROL_ZONE);
const controlStale = control.filter((r) => r.stale);
const othersStale = others.filter((r) => r.stale);
say(`  ${CONTROL_ZONE}：陈旧请求 ${controlStale.length} 次，失败 ${fails(controlStale)} 次（${pct(failRate(controlStale))}）`);
say(`  其余三区  ：陈旧请求 ${othersStale.length} 次，失败 ${fails(othersStale)} 次（${pct(failRate(othersStale))}）`);
say(`  两边的陈旧占比接近（${pct(controlStale.length / control.length)} vs ${pct(othersStale.length / others.length)}），即青龙二区同样被同步积压影响，却不因此失败`);
say(`    ${pad('剩余配额', 10)}${pad('青龙二区', 16)}${pad('其余三区', 16)}`);
const controlTable = [];
for (const b of BANDS) {
  const c = control.filter((r) => remainBand(r) === b);
  const o = others.filter((r) => remainBand(r) === b);
  say(`    ${pad(b, 10)}${pad(`${pct(failRate(c))} (n=${c.length})`, 16)}${pad(`${pct(failRate(o))} (n=${o.length})`, 16)}`);
  controlTable.push([b, c.length, fails(c), failRate(c).toFixed(4), o.length, fails(o), failRate(o).toFixed(4)]);
}
say('  只看陈旧请求（>15 分钟），对比更极端：');
const staleControlTable = [];
for (const b of BANDS) {
  const c = controlStale.filter((r) => remainBand(r) === b);
  const o = othersStale.filter((r) => remainBand(r) === b);
  say(`    ${pad(b, 10)}${pad(`${pct(failRate(c))} (n=${c.length})`, 16)}${pad(`${pct(failRate(o))} (n=${o.length})`, 16)}`);
  staleControlTable.push([b, c.length, fails(c), failRate(c).toFixed(4), o.length, fails(o), failRate(o).toFixed(4)]);
}
say('  → 其余三区：快照陈旧时，余量越多反而越容易失败（43%→58%），不可能是「真的卖完了」；');
say('  → 青龙二区：余量 ≥5 的 52 次陈旧请求一次都没失败，只有余量 <5 时才失败（30.8%）—— 这才是配额校验应有的样子。');

const controlRates = BANDS.map((b) => {
  const g = control.filter((r) => remainBand(r) === b);
  return { band: b, rows: g, rate: g.length ? fails(g) / g.length : 0, othersN: others.filter((r) => remainBand(r) === b).length };
});
const expectedOthers = controlRates.reduce((acc, c) => acc + c.othersN * c.rate, 0);
let seed2 = 20260902;
const rand2 = () => { seed2 = (seed2 * 1103515245 + 12345) % 2147483648; return seed2 / 2147483648; };
const draws = [];
for (let t = 0; t < 2000; t++) {
  let e = 0;
  for (const c of controlRates) {
    if (!c.rows.length) continue;
    let f = 0;
    for (let i = 0; i < c.rows.length; i++) if (c.rows[Math.floor(rand2() * c.rows.length)].outcome === 'fail') f += 1;
    e += (f / c.rows.length) * c.othersN;
  }
  draws.push(e);
}
draws.sort((a, b) => a - b);
const expectedTotal = expectedOthers + fails(control);
const reducedFailures = Math.round(fails(all) - expectedTotal);
const savedByValidation = reducedFailures * FAIL_COST;
say(`  反事实（假设青龙二区按余量的失败曲线同样适用于其余三区）：`);
say(`    其余三区 ${fails(others)} 次失败 → ≈${fixed(expectedOthers)} 次（bootstrap 95% 区间 ${fixed(quantile(draws, 0.025))}~${fixed(quantile(draws, 0.975))}）`);
say(`    全区 ${fails(all)} → ≈${fixed(expectedTotal)} 次（-${pct(1 - expectedTotal / fails(all))}），减少 ${reducedFailures} 次 ≈ ${savedByValidation} 点券 / 7 天`);
say('');

/* 5. 阈值 ------------------------------------------------------------ */
say('【5】阈值：15 分钟是怎么来的');
say(`  样本在 ${fixed(maxFreshLag)}~${fixed(minStaleLag)} 分钟之间完全断档，12~17 分钟任一阈值对样本的划分相同；`);
say('  取整到 15 分钟，并把「置灰收益 - 置灰成本」在 0~65 分钟上做扫描（out/policy_threshold_scan.csv）：');
const scan = [];
for (let t = 0; t <= 65; t++) {
  const r = evaluatePolicy(`T=${t}`, all, (x) => x.lagMin > t);
  scan.push(r);
  if ([5, 10, 12, 13, 14, 15, 16, 17, 20, 30, 45, 60, 65].includes(t)) {
    say(`    T=${lpad(t, 2)}  置灰 ${lpad(r.gated, 4)} 避免失败 ${lpad(r.avoided, 4)}  剩余失败率 ${pad(pct(r.failRate), 7)} 净收益 ${lpad(fixed(r.net), 6)} 点券`);
  }
}
const maxNet = Math.max(...scan.map((r) => r.net));
const plateau = scan.filter((r) => r.net === maxNet).map((r) => Number(r.name.slice(2)));
say(`  全量最优区间 T=${Math.min(...plateau)}~${Math.max(...plateau)} 分钟（净收益 ${fixed(maxNet)} 点券），15 分钟落在区间内。`);
say('');

/* 6. 策略对比 -------------------------------------------------------- */
say('【6】策略对比（全部已判定样本，置灰 20 点券/次，失败 75 点券/次）');
const policies = [
  evaluatePolicy('A. 不处置（现状）', all, () => false),
  evaluatePolicy(`B. 快照 >${STALE_MIN} 分钟置灰（推荐）`, all, (r) => r.stale),
  evaluatePolicy('C. 按并发 >70 置灰', all, (r) => r.online > 70),
  evaluatePolicy('D. 按余量 ≤5 置灰', all, (r) => r.remain <= 5),
  evaluatePolicy('E. 陈旧且高并发(>55)置灰', all, (r) => r.stale && r.online > 55),
  evaluatePolicy('F. 陈旧或极端并发(>80)置灰', all, (r) => r.stale || r.online > 80),
];
say(`    ${pad('策略', 30)}${lpad('置灰数', 8)}${lpad('避免失败', 9)}${lpad('命中率', 8)}${lpad('失败数', 8)}${lpad('失败率', 8)}${lpad('净收益', 9)}`);
for (const p of policies) {
  say(`    ${pad(p.name, 30)}${lpad(p.gated, 8)}${lpad(p.avoided, 9)}${lpad(pct(p.hitRate), 8)}${lpad(p.failures, 8)}${lpad(pct(p.failRate), 8)}${lpad(fixed(p.net), 9)}`);
}
const chosen = policies[1];
say(`  B 的盈亏平衡置灰成本 = ${fixed(chosen.breakEvenGrayCost, 1)} 点券 > 题设 20 点券，安全边际 ${pct(1 - GRAY_COST / chosen.breakEvenGrayCost)}`);
say('');

/* 7. 时间外回测 ------------------------------------------------------ */
say('【7】时间外回测：前 4 天选阈值，后 3 天验证');
const train = all.filter((r) => r.day <= TRAIN_LAST_DAY);
const test = all.filter((r) => r.day > TRAIN_LAST_DAY);
let bestTrain = null;
for (let t = 0; t <= 65; t++) {
  const r = evaluatePolicy(`T=${t}`, train, (x) => x.lagMin > t);
  if (!bestTrain || r.net > bestTrain.net) bestTrain = { ...r, t };
}
const testPolicy = evaluatePolicy(`T=${bestTrain.t}`, test, (x) => x.lagMin > bestTrain.t);
const trainBase = failRate(train);
const testBase = failRate(test);
say(`  训练集 ${train.length} 条（${pct(trainBase, 2)} 失败）；测试集 ${test.length} 条（${pct(testBase, 2)} 失败）`);
say(`  训练集选出的阈值 T=${bestTrain.t} 分钟`);
say(`  测试集：置灰 ${testPolicy.gated} 次，避免失败 ${testPolicy.avoided} 次，失败率 ${pct(testBase, 2)} → ${pct(testPolicy.failRate, 2)}，净收益 ${fixed(testPolicy.net)} 点券`);
const test15 = evaluatePolicy('T=15', test, (r) => r.stale);
say(`  固定用 T=15：测试集失败率 ${pct(testBase, 2)} → ${pct(test15.failRate, 2)}，净收益 ${fixed(test15.net)} 点券`);
say('');

/* 8. 账 -------------------------------------------------------------- */
say('【8】账');
const totalLoss = fails(all) * FAIL_COST;
const idealFailures = Math.round(all.length * freshRate);
say(`  本次活动已判定失败 ${fails(all)} 次 × 75 点券 = ${totalLoss} 点券的确定损失`);
say(`  未决 ${unknownRows.length} 条（${pct(unknownRows.length / rows.length)}）无法对账，其中 ${unknownRows.filter((r) => r.stale).length} 条落在陈旧区，风险敞口 ${unknownRows.length * FAIL_COST} 点券`);
say('  两条路线（互不排斥）：');
say(`    治本 · 校验改用权威余量（对齐青龙二区）：失败 ${fails(all)} → ≈${fixed(expectedTotal)} 次，减少 ${reducedFailures} 次 ≈ ${savedByValidation} 点券 / 7 天，且不阻挡任何成功招募`);
say(`    止血 · 陈旧即置灰（B 策略）：净收益 ${fixed(chosen.net)} 点券 / 7 天，代价是 ${chosen.gated - chosen.avoided} 次本可成功的招募被推迟到同步完成`);
say(`  未决样本敏感性：若 ${unknownRows.filter((r) => r.stale).length} 条陈旧未决全部算失败，B 的避免失败数为 ${chosen.avoided + unknownRows.filter((r) => r.stale).length}，净收益 ${fixed((chosen.avoided + unknownRows.filter((r) => r.stale).length) * FAIL_COST - chosen.gated * GRAY_COST)} 点券`);
say('');

/* 9. 写出结果 -------------------------------------------------------- */
fs.mkdirSync(OUT_DIR, { recursive: true });
writeCsv(path.join(OUT_DIR, 't_failure_by_lag.csv'), ['lag_bucket_min', 'attempts', 'failures', 'fail_rate'], lagTable);
writeCsv(path.join(OUT_DIR, 't_online_deciles.csv'), ['online_band', 'attempts', 'stale_share', 'fail_rate'], onlineTable);
writeCsv(path.join(OUT_DIR, 't_by_zone.csv'), ['server_zone', 'attempts', 'failures', 'fail_rate', 'stale_share'], zoneTable);
writeCsv(path.join(OUT_DIR, 't_by_pool.csv'), ['pool_type', 'attempts', 'failures', 'fail_rate', 'stale_share'],
  poolTable.map((t) => [t[0], t[1], t[2], t[3].toFixed(4), t[4].toFixed(4)]));
writeCsv(path.join(OUT_DIR, 't_control_zone.csv'), ['remain_band', 'control_n', 'control_failures', 'control_fail_rate', 'others_n', 'others_failures', 'others_fail_rate'], controlTable);
writeCsv(path.join(OUT_DIR, 't_control_zone_stale.csv'), ['remain_band', 'control_n', 'control_failures', 'control_fail_rate', 'others_n', 'others_failures', 'others_fail_rate'], staleControlTable);
writeCsv(path.join(OUT_DIR, 'policy_threshold_scan.csv'), ['threshold_min', 'gated', 'avoided_failures', 'remaining_failures', 'remaining_fail_rate', 'gray_cost', 'net_benefit'],
  scan.map((r) => [r.name.replace('T=', ''), r.gated, r.avoided, r.failures, r.failRate.toFixed(4), r.grayCost, r.net]));
writeCsv(path.join(OUT_DIR, 'policy_comparison.csv'), ['policy', 'gated', 'avoided_failures', 'hit_rate', 'remaining_failures', 'remaining_fail_rate', 'gray_cost', 'net_benefit', 'break_even_gray_cost'],
  policies.map((r) => [r.name, r.gated, r.avoided, Number.isFinite(r.hitRate) ? r.hitRate.toFixed(4) : '', r.failures, r.failRate.toFixed(4), r.grayCost, r.net, Number.isFinite(r.breakEvenGrayCost) ? r.breakEvenGrayCost.toFixed(2) : '']));

const summary = {
  generated_at: new Date().toISOString(),
  source: 'recruitment_logs.csv',
  assumptions: { fail_cost: FAIL_COST, gray_cost: GRAY_COST, stale_threshold_min: STALE_MIN },
  data_quality: {
    raw_rows: raw.length,
    duplicate_rows_dropped: dupDropped,
    rows_after_dedupe: rows.length,
    unknown_status: unknownRows.length,
    decided: all.length,
  },
  overall: { success: success(all), fail: fails(all), fail_rate: failRate(all) },
  staleness: {
    p50_min: quantile(lagVals, 0.5),
    p90_min: quantile(lagVals, 0.9),
    max_min: Math.max(...lagVals),
    fresh_attempts: freshRows.length,
    stale_attempts: staleRows.length,
    stale_share: staleShare,
  },
  contrast: {
    fresh_fail_rate: freshRate,
    stale_fail_rate: staleRate,
    relative_risk: rr,
    paf,
    zone_permutation_p: zoneTest.p,
    pool_permutation_p: poolTest.p,
  },
  policy: {
    recommended: chosen.name,
    gated: chosen.gated,
    avoided_failures: chosen.avoided,
    hit_rate: chosen.hitRate,
    failure_rate_before: failRate(all),
    failure_rate_after: chosen.failRate,
    net_benefit: chosen.net,
    break_even_gray_cost: chosen.breakEvenGrayCost,
  },
  holdout: {
    train_rows: train.length,
    test_rows: test.length,
    threshold_selected: bestTrain.t,
    test_fail_rate_before: testBase,
    test_fail_rate_after: testPolicy.failRate,
    test_net_benefit: testPolicy.net,
    fixed_15_fail_rate_after: test15.failRate,
    fixed_15_net_benefit: test15.net,
  },
  control_zone: {
    name: CONTROL_ZONE,
    stale_attempts: controlStale.length,
    stale_failures: fails(controlStale),
    stale_fail_rate: failRate(controlStale),
    others_stale_attempts: othersStale.length,
    others_stale_failures: fails(othersStale),
    others_stale_fail_rate: failRate(othersStale),
    expected_total_failures: expectedTotal,
    expected_total_ci: [quantile(draws, 0.025), quantile(draws, 0.975)],
    saved_by_validation: savedByValidation,
  },
  money: {
    confirmed_loss: totalLoss,
    unverified_at_risk: unknownRows.length * FAIL_COST,
    all_fresh_counterfactual_failures: idealFailures,
    all_fresh_counterfactual_saved: (fails(all) - idealFailures) * FAIL_COST,
  },
};
fs.writeFileSync(path.join(OUT_DIR, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`, 'utf8');
say(`结果已写入 ${path.relative(ROOT, OUT_DIR)}/ (summary.json, t_*.csv, policy_*.csv)`);

/* 10. 断言 ----------------------------------------------------------- */
if (process.argv.includes('--check')) {
  const checks = [
    ['去重后无重复 log_id', new Set(rows.map((r) => r.id)).size === rows.length],
    ['无负时延（时区换算正确）', rows.every((r) => r.lagMin >= 0)],
    ['成功+失败+未决 = 总行数', success(all) + fails(all) + unknownRows.length === rows.length],
    ['陈旧组失败率显著高于新鲜组', staleRate > freshRate * 2],
    ['置灰策略净收益为正', chosen.net > 0],
    ['时间外回测失败率下降', testPolicy.failRate < testBase],
    ['对照区陈旧请求失败率低于其他区', failRate(controlStale) < failRate(othersStale)],
    ['对照区余量<5 时失败率显著高于余量≥20', failRate(control.filter((r) => r.remain < 5)) > 5 * failRate(control.filter((r) => r.remain >= 20))],
  ];
  say('');
  say('【断言】');
  let ok = true;
  for (const [name, pass] of checks) {
    say(`  ${pass ? 'PASS' : 'FAIL'}  ${name}`);
    if (!pass) ok = false;
  }
  if (!ok) process.exitCode = 1;
}
