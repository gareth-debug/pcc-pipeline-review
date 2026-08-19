import React, { useState, useEffect, useRef, useMemo, useCallback } from "react";

/* ============================================================================
   Cheeky Pipeline Review
   Weekly 1:1 pipeline health and commit accountability.

   All state lives as one JSON blob in Redis under the key "pipeline-review"
   (see api/data.js). This file never owns the data: it reads the blob, migrates
   older shapes forward, and writes it back. Redeploying never touches data.
   ========================================================================== */

const DATA_VERSION = 8;
const SAVE_DEBOUNCE_MS = 900;
const POLL_MS = 8000;
const MAX_SNAPSHOTS = 260;

/* -------------------------------------------------------------- utilities */

function uid(p) {
  return p + "_" + Math.random().toString(36).slice(2, 9) + Date.now().toString(36).slice(-4);
}
function trimZero(s) {
  return String(s).replace(/\.0+$/, "").replace(/(\.[1-9]*)0+$/, "$1");
}
function parseMoney(raw) {
  if (raw === null || raw === undefined) return 0;
  if (typeof raw === "number") return isFinite(raw) ? Math.round(raw) : 0;
  let s = String(raw).trim().toLowerCase().replace(/[$,\s]/g, "");
  if (!s) return 0;
  let mult = 1;
  const last = s.charAt(s.length - 1);
  if (last === "k") { mult = 1e3; s = s.slice(0, -1); }
  else if (last === "m") { mult = 1e6; s = s.slice(0, -1); }
  else if (last === "b") { mult = 1e9; s = s.slice(0, -1); }
  const n = parseFloat(s);
  return isFinite(n) ? Math.round(n * mult) : 0;
}
function fmtMoney(n) {
  const v = Number(n) || 0;
  const neg = v < 0;
  const a = Math.abs(v);
  let out;
  if (a >= 1e9) out = "$" + trimZero((a / 1e9).toFixed(2)) + "B";
  else if (a >= 1e6) out = "$" + trimZero((a / 1e6).toFixed(1)) + "M";
  else if (a >= 1e3) out = "$" + trimZero((a / 1e3).toFixed(1)) + "K";
  else out = "$" + Math.round(a);
  return (neg ? "-" : "") + out;
}
function fmtSignedMoney(n) {
  const v = Number(n) || 0;
  return v === 0 ? "0" : (v > 0 ? "+" : "") + fmtMoney(v);
}
function fmtDays(n) {
  const v = Number(n) || 0;
  return v === 0 ? "\u2014" : (Math.round(v * 10) / 10) + "d";
}
function fmtInputMoney(n) {
  const v = Math.round(Number(n) || 0);
  if (v === 0) return "";
  const a = Math.abs(v);
  if (a >= 1e6 && a % 1e4 === 0) return trimZero((v / 1e6).toFixed(2)) + "M";
  if (a >= 1e3 && a % 1e3 === 0) return (v / 1e3) + "K";
  return String(v);
}
function mondayOf(d) {
  const x = d ? new Date(d) : new Date();
  x.setHours(0, 0, 0, 0);
  const day = x.getDay();
  x.setDate(x.getDate() + (day === 0 ? -6 : 1 - day));
  return x;
}
function isoDate(d) {
  return d.getFullYear() + "-" + String(d.getMonth() + 1).padStart(2, "0") + "-" + String(d.getDate()).padStart(2, "0");
}
function thisMonday() { return isoDate(mondayOf(new Date())); }
const MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
function shortDate(iso) {
  if (!iso) return "\u2014";
  const p = String(iso).split("-");
  const d = new Date(Number(p[0]), Number(p[1]) - 1, Number(p[2]));
  if (isNaN(d.getTime())) return String(iso);
  return MONTHS[d.getMonth()] + " " + d.getDate();
}
function weeksBetween(a, b) {
  if (!a || !b) return 0;
  const x = new Date(a + "T00:00:00"), y = new Date(b + "T00:00:00");
  if (isNaN(x.getTime()) || isNaN(y.getTime())) return 0;
  return Math.round((y - x) / (7 * 24 * 3600 * 1000));
}
function clockTime(t) {
  const d = new Date(t);
  return String(d.getHours()).padStart(2, "0") + ":" + String(d.getMinutes()).padStart(2, "0");
}
function shortName(n) {
  const p = String(n || "").trim().split(/\s+/);
  return p.length < 2 ? p[0] : p[0] + " " + p[p.length - 1].charAt(0) + ".";
}

/* Three tiers: at/above target, within reach, behind. Every bar and pill
   in the app reads its colour from this one function. */
function tone(actual, target) {
  if (!(target > 0)) return "good";
  const r = actual / target;
  if (r >= 1) return "good";
  if (r >= 0.8) return "warn";
  return "bad";
}

/* ------------------------------------------------------------ aggregation */

function cellOf(src, repId, stageId) {
  const r = src && src[repId];
  const c = r ? (r.stages ? r.stages[stageId] : r[stageId]) : null;
  return {
    gpv: c && isFinite(Number(c.gpv)) ? Number(c.gpv) : 0,
    avgDays: c && isFinite(Number(c.avgDays)) ? Number(c.avgDays) : 0
  };
}
/* GPV-weighted average days; falls back to a simple mean of reported figures
   when a stage carries no GPV. */
function aggregate(src, ids, stages) {
  const byStage = {};
  let total = 0, coverage = 0;
  stages.forEach((st) => {
    let gpv = 0, w = 0, ds = 0, dc = 0;
    ids.forEach((rid) => {
      const c = cellOf(src, rid, st.id);
      gpv += c.gpv;
      w += c.gpv * c.avgDays;
      if (c.avgDays > 0) { ds += c.avgDays; dc += 1; }
    });
    byStage[st.id] = { gpv, avgDays: gpv > 0 ? w / gpv : (dc > 0 ? ds / dc : 0) };
    total += gpv;
    if (st.inCoverage !== false) coverage += gpv;
  });
  return { byStage, total, coverage };
}
/* Baseline = earliest capture in the most recent week at or before this Monday.
   Manual mid-week captures are kept as history but never become the baseline. */
function pickBaseline(snapshots, mondayIso) {
  const el = (snapshots || []).filter((s) => s.weekOf && s.weekOf <= mondayIso);
  if (!el.length) return null;
  const week = el.map((s) => s.weekOf).sort().pop();
  return el.filter((s) => s.weekOf === week).sort((a, b) => (a.takenAt || 0) - (b.takenAt || 0))[0];
}
function weeklyCaptures(snapshots) {
  const bw = {};
  (snapshots || []).forEach((s) => {
    const c = bw[s.weekOf];
    if (!c || (s.takenAt || 0) < (c.takenAt || 0)) bw[s.weekOf] = s;
  });
  return Object.keys(bw).sort().map((w) => bw[w]);
}
function commitStats(commits, repId, mondayIso) {
  const mine = (commits || []).filter((c) => (repId ? c.repId === repId : true));
  const open = mine.filter((c) => c.status === "open");
  const thisWeek = mine.filter((c) => c.weekOf === mondayIso);
  const moved = mine.filter((c) => c.status === "moved");
  const missed = mine.filter((c) => c.status === "missed");
  const resolved = moved.length + missed.length;
  const sum = (a) => a.reduce((x, c) => x + (Number(c.gpv) || 0), 0);
  return {
    open, thisWeek,
    openGpv: sum(open), thisWeekGpv: sum(thisWeek),
    moved: moved.length, missed: missed.length, resolved,
    hitRate: resolved ? moved.length / resolved : null
  };
}

/* ------------------------------------------------------------- data model */

/* ---------------------------------------------------------------------------
   THE MODEL. These figures are locked: nothing in the interface edits them.
   Changing them means editing this block and redeploying.

   Sized from throughput rather than opinion. Little's Law says what sits in a
   stage equals the rate flowing through it times how long it sits there. So we
   start at the activation target, divide back through each stage's conversion
   rate to get the flow that must enter it, then multiply by dwell time.

   At these conversion rates a $90M book sustains roughly $3.1M activated per
   month. $4M/month would need about $113M. See Settings for the full working.
   --------------------------------------------------------------------------- */
const PER_REP_TARGET = 90e6;         // total pipeline one rep carries
const ACTIVATION_PER_MONTH = 4e6;    // what the business asks each rep to activate

const STAGE_MODEL = [
  { id: "st_discovery",      name: "Discovery",         floor: 56e6, dwellDays: 45, conv: 0.35 },
  { id: "st_evaluation",     name: "Evaluation",        floor: 13e6, dwellDays: 30, conv: 0.45 },
  { id: "st_negotiation",    name: "Negotiation",       floor: 6e6,  dwellDays: 30, conv: 0.65 },
  { id: "st_closeplan",      name: "Mutual close plan", floor: 3e6,  dwellDays: 21, conv: 0.85 },
  { id: "st_implementation", name: "Implementation",    floor: 12e6, dwellDays: 90, conv: 0.95 }
];

function defaultStages() {
  return STAGE_MODEL.map((s) => Object.assign({ inCoverage: true }, s));
}

const WEEKS_PER_MONTH = 13 / 3;      // 4.333

/* Required monthly flow into each stage, working back from the activation
   target. Also the basis for how much must leave the stage before it. */
function modelFlows() {
  const out = new Array(STAGE_MODEL.length);
  let need = ACTIVATION_PER_MONTH;
  for (let i = STAGE_MODEL.length - 1; i >= 0; i--) {
    need = need / STAGE_MODEL[i].conv;
    out[i] = need;
  }
  return out;
}

/* What must LEAVE a stage each week. Holding a target is only half the job:
   a full stage that never empties is a blockage, not a healthy book. What has
   to leave stage N is exactly what has to enter stage N+1; out of the last
   stage, it is the activation target itself. */
function weeklyOutflowNeed(idx) {
  const flows = modelFlows();
  const monthly = idx < STAGE_MODEL.length - 1 ? flows[idx + 1] : ACTIVATION_PER_MONTH;
  return monthly / WEEKS_PER_MONTH;
}
function defaultReps() {
  return [
    { id: "rep_david", name: "David Agadzhanyan", active: true },
    { id: "rep_ryan", name: "Ryan Wadhams", active: true },
    { id: "rep_aubrey", name: "Aubrey Heathcott", active: true },
    { id: "rep_zachariah", name: "Zachariah Wichman", active: true },
    { id: "rep_tacen", name: "Tacen Woods", active: true },
    { id: "rep_wilmer", name: "Wilmer Lemus", active: true },
    { id: "rep_joey", name: "Joey Millet", active: true }
  ];
}
function defaultData() {
  return {
    meta: { version: DATA_VERSION, updatedAt: Date.now() },
    config: { coverageTarget: PER_REP_TARGET, stages: defaultStages(), reps: defaultReps() },
    targets: {},        /* per-rep, per-stage overrides of the even split */
    current: {},
    commits: [],
    snapshots: []
  };
}

/* Forward-migrate whatever came out of storage. Never drops unknown fields,
   never renumbers ids. Safe to run on every load. */
function migrate(raw) {
  const base = defaultData();
  const input = raw && typeof raw === "object" ? raw : {};
  const d = Object.assign({}, base, input);

  d.meta = Object.assign({ version: DATA_VERSION, updatedAt: Date.now() }, input.meta || {});
  d.config = Object.assign({}, base.config, input.config || {});

  /* Stages and targets come from the model, not from storage, so an older blob
     carrying superseded figures is corrected on load rather than honoured. */
  d.config.stages = defaultStages();

  const reps = Array.isArray(d.config.reps) ? d.config.reps : [];
  d.config.reps = reps.map((r, i) => ({
    id: r.id || ("rep_" + i + "_" + Math.random().toString(36).slice(2, 7)),
    name: r.name || ("Rep " + (i + 1)),
    active: r.active !== false
  }));
  d.config.coverageTarget = PER_REP_TARGET;

  const t = input.targets && typeof input.targets === "object" ? input.targets : {};
  d.targets = {};
  Object.keys(t).forEach((rid) => {
    const row = t[rid];
    if (!row || typeof row !== "object") return;
    const out = {};
    Object.keys(row).forEach((sid) => {
      if (isFinite(Number(row[sid]))) out[sid] = Number(row[sid]);
    });
    d.targets[rid] = out;
  });

  const cur = input.current && typeof input.current === "object" ? input.current : {};
  d.current = {};
  Object.keys(cur).forEach((rid) => {
    const src = cur[rid] || {};
    const stagesIn = src.stages && typeof src.stages === "object" ? src.stages : src;
    const out = {};
    Object.keys(stagesIn).forEach((sid) => {
      const c = stagesIn[sid];
      if (!c || typeof c !== "object") return;
      out[sid] = {
        gpv: isFinite(Number(c.gpv)) ? Number(c.gpv) : 0,
        avgDays: isFinite(Number(c.avgDays)) ? Number(c.avgDays) : 0
      };
    });
    d.current[rid] = { stages: out, note: typeof src.note === "string" ? src.note : "" };
  });
  d.config.reps.forEach((r) => {
    if (!d.current[r.id]) d.current[r.id] = { stages: {}, note: "" };
  });

  d.commits = (Array.isArray(input.commits) ? input.commits : []).map((c, i) => ({
    id: c.id || uid("cmt"),
    repId: c.repId || "",
    name: typeof c.name === "string" ? c.name : "",
    gpv: isFinite(Number(c.gpv)) ? Number(c.gpv) : 0,
    /* v1 allowed a "new" pseudo-source into the first stage; that concept is
       gone, so those commits keep their destination and lose the source. */
    fromStage: c.fromStage === "new" ? "" : (c.fromStage || ""),
    toStage: c.toStage || "",
    weekOf: c.weekOf || thisMonday(),
    status: c.status === "moved" || c.status === "missed" ? c.status : "open",
    resolvedWeek: c.resolvedWeek || null,
    createdAt: c.createdAt || Date.now() - 1000 * i
  }));

  d.snapshots = (Array.isArray(input.snapshots) ? input.snapshots : [])
    .filter((s) => s && s.weekOf)
    .map((s) => ({
      id: s.id || uid("snap"),
      weekOf: s.weekOf,
      takenAt: Number(s.takenAt) || 0,
      auto: s.auto !== false,
      coverageTarget: isFinite(Number(s.coverageTarget)) ? Number(s.coverageTarget) : 0,
      floors: s.floors && typeof s.floors === "object" ? s.floors : {},
      reps: s.reps && typeof s.reps === "object" ? s.reps : {}
    }));

  d.meta.version = DATA_VERSION;
  return d;
}

function makeSnapshot(d, weekOf, auto) {
  const reps = {};
  d.config.reps.forEach((r) => {
    const stages = {};
    d.config.stages.forEach((st) => {
      const c = cellOf(d.current, r.id, st.id);
      stages[st.id] = { gpv: c.gpv, avgDays: c.avgDays };
    });
    reps[r.id] = { stages };
  });
  const floors = {};
  d.config.stages.forEach((st) => { floors[st.id] = Number(st.floor) || 0; });
  return {
    id: uid("snap"), weekOf, takenAt: Date.now(), auto: !!auto,
    coverageTarget: Number(d.config.coverageTarget) || 0, floors, reps
  };
}

/* ------------------------------------------------------- targets and flow */

function activeRepsOf(d) { return d.config.reps.filter((r) => r.active !== false); }

/* Each stage's `floor` is what ONE rep is expected to hold in that stage.
   The team number is that figure multiplied by the active head count, not
   divided by it. A rep can be given their own figure via d.targets. */
function repTarget(d, repId, stageId) {
  const st = d.config.stages.filter((s) => s.id === stageId)[0];
  return st ? (Number(st.floor) || 0) : 0;
}
/* What the whole team should be holding in a stage. */
function teamFloor(d, stage) {
  return (Number(stage.floor) || 0) * (activeRepsOf(d).length || 1);
}
/* The first stage fills from prospecting, not from a named deal crossing over,
   so it never takes inbound commits. */
function takesInbound(idx) { return idx > 0; }

/* What has to move into this stage for the rep to hit target, given what they
   have already pledged to move out of it this week. */
function stageFlow(d, repId, idx) {
  const stages = d.config.stages;
  const st = stages[idx];
  const prev = idx > 0 ? stages[idx - 1] : null;
  const next = idx < stages.length - 1 ? stages[idx + 1] : null;
  const cell = cellOf(d.current, repId, st.id);
  const target = repTarget(d, repId, st.id);
  const open = d.commits.filter((c) => c.repId === repId && c.status === "open");
  const inbound = open.filter((c) => c.toStage === st.id);
  const outbound = open.filter((c) => c.fromStage === st.id);
  const sum = (a) => a.reduce((x, c) => x + (Number(c.gpv) || 0), 0);
  const pledgedIn = sum(inbound), pledgedOut = sum(outbound);
  const gap = Math.max(0, target - cell.gpv);
  const required = gap + pledgedOut;
  const shortfall = Math.max(0, required - pledgedIn);
  const inb = takesInbound(idx);

  /* throughput: what has to cross into the next stage this week */
  const outNeed = idx < stages.length - 1 ? weeklyOutflowNeed(idx) : weeklyOutflowNeed(idx);
  const outShort = Math.max(0, outNeed - pledgedOut);
  const holdOk = cell.gpv >= target;

  /* Two separate readings, because they answer different questions.

     ACTION is what to do this week, and it is only ever about movement:
       empty  nothing here to move
       move   there is stock but not enough is committed onward
       ok     enough is committed

     RISK is forward-looking and about shape. A stage well under its target is
     not a failure this week, it is a hole that lands once the deals that should
     have crossed it would have reached activation. Being light in one stage
     while heavy in another is a legitimate shape and is never marked down. */
  const lightBy = Math.max(0, target - cell.gpv);
  let state;
  if (cell.gpv <= 0) state = "empty";
  else if (outShort > 0) state = "move";
  else state = "ok";

  const hole = target > 0 && cell.gpv < target * 0.6;

  return {
    stage: st, prev, next, idx,
    gpv: cell.gpv, avgDays: cell.avgDays, target,
    inbound, outbound, pledgedIn, pledgedOut,
    gap, required, shortfall,
    outNeed, outShort, holdOk, lightBy, hole,
    monthsOfStock: outNeed > 0 ? cell.gpv / (outNeed * WEEKS_PER_MONTH) : 0,
    isShort: state === "light" || state === "empty",
    isStuck: state === "move",
    state
  };
}
function sourceLabel(f) { return f.prev ? f.prev.name : "new pipeline"; }

/* ------------------------------------------------------- weighted cover */

/* Odds that a deal sitting in this stage eventually activates: the product of
   every conversion rate from here to the end. A dollar in Mutual close plan is
   worth about ten in Discovery, which is why a bottom-heavy book should not be
   marked down for its shape. */
function activationOdds(idx) {
  return STAGE_MODEL.slice(idx).reduce((a, s) => a * s.conv, 1);
}

/* Expected activation sitting in the book, split into what is already signed
   and what still has to be sold. Blending the two lets a fat implementation
   queue hide a dead selling motion, so they are always reported separately. */
function coverOf(d, repIds) {
  const stages = d.config.stages;
  const agg = aggregate(d.current, repIds, stages);
  let selling = 0, locked = 0;
  stages.forEach((st, i) => {
    const v = agg.byStage[st.id].gpv * activationOdds(i);
    if (i === stages.length - 1) locked += v; else selling += v;
  });
  const perMonth = ACTIVATION_PER_MONTH * (repIds.length || 1);
  return {
    selling, locked, total: selling + locked,
    monthsSelling: perMonth > 0 ? selling / perMonth : 0,
    monthsLocked: perMonth > 0 ? locked / perMonth : 0,
    months: perMonth > 0 ? (selling + locked) / perMonth : 0
  };
}

/* The same calculation on the target book, so there is something to compare to. */
function targetCover() {
  let selling = 0, locked = 0;
  STAGE_MODEL.forEach((st, i) => {
    const v = st.floor * activationOdds(i);
    if (i === STAGE_MODEL.length - 1) locked += v; else selling += v;
  });
  return {
    selling, locked, total: selling + locked,
    monthsSelling: selling / ACTIVATION_PER_MONTH,
    monthsLocked: locked / ACTIVATION_PER_MONTH,
    months: (selling + locked) / ACTIVATION_PER_MONTH
  };
}

/* How much has to move this week across the whole funnel, and how much of it
   has actually been named. In a stagnant funnel this is the number that matters. */
function flowOf(d, repIds, monday) {
  const stages = d.config.stages;
  let need = 0, named = 0;
  stages.forEach((st, i) => {
    need += weeklyOutflowNeed(i) * (repIds.length || 1);
    named += d.commits
      .filter((c) => c.status === "open" && c.fromStage === st.id && repIds.indexOf(c.repId) >= 0)
      .reduce((a, c) => a + (Number(c.gpv) || 0), 0);
  });
  return { need, named, pct: need > 0 ? (named / need) * 100 : 0 };
}

/* A hole in a stage does not hurt today. It hurts once the deals that should
   have passed through it would have reached activation. */
function impactHorizon(idx) {
  const days = STAGE_MODEL.slice(idx).reduce((a, s) => a + s.dwellDays, 0);
  const when = new Date(Date.now() + days * 864e5);
  return {
    days,
    months: days / 30.4,
    label: MONTHS[when.getMonth()] + " " + when.getFullYear()
  };
}

/* --------------------------------------------------------- days trends */

/* Captures are keyed to Mondays, so a window is just a number of Mondays back.
   Looking back 1 gives the change over the past week, 4 the past month, 12 the
   past quarter. Falls back to the nearest capture within a week if a Monday
   was missed, and reports nothing at all rather than guessing. */
const TREND_WINDOWS = [1, 2, 4, 12];

function captureWeeksBack(snapshots, mondayIso, weeks) {
  const caps = weeklyCaptures(snapshots);
  if (!caps.length) return null;
  const wantTime = new Date(mondayIso + "T00:00:00").getTime() - (weeks - 1) * 7 * 864e5;
  let best = null, bestDiff = Infinity;
  caps.forEach((c) => {
    const t = new Date(c.weekOf + "T00:00:00").getTime();
    const diff = Math.abs(t - wantTime);
    /* Captures land on Mondays, so anything not within a few days of the
       wanted Monday belongs to a different window. Borrowing a neighbouring
       week would label the same change as two different periods. */
    if (diff <= 3 * 864e5 && diff < bestDiff) { bestDiff = diff; best = c; }
  });
  return best;
}

/* Percentage change in days-in-stage across each window. Down is good. */
function daysTrends(d, repIds, stageId, mondayIso) {
  const stages = d.config.stages;
  const now = aggregate(d.current, repIds, stages).byStage[stageId].avgDays;
  return TREND_WINDOWS.map((w) => {
    const cap = captureWeeksBack(d.snapshots, mondayIso, w);
    if (!cap) return { weeks: w, ok: false };
    const then = aggregate(cap.reps, repIds, stages).byStage[stageId].avgDays;
    if (!(then > 0) || !(now > 0)) return { weeks: w, ok: false };
    return { weeks: w, ok: true, pct: ((now - then) / then) * 100, then, weekOf: cap.weekOf };
  });
}

/* ---------------------------------------------------------------- atoms */

function MoneyInput({ value, onCommit, onEditing, className }) {
  const [text, setText] = useState(fmtInputMoney(value));
  const focused = useRef(false);
  useEffect(() => { if (!focused.current) setText(fmtInputMoney(value)); }, [value]);
  return (
    <input
      className={className || "in num"}
      value={text}
      placeholder={"\u2014"}
      inputMode="decimal"
      onFocus={(e) => { focused.current = true; if (onEditing) onEditing(1); e.target.select(); }}
      onChange={(e) => setText(e.target.value)}
      onBlur={() => {
        focused.current = false;
        if (onEditing) onEditing(-1);
        const n = parseMoney(text);
        setText(fmtInputMoney(n));
        onCommit(n);
      }}
      onKeyDown={(e) => { if (e.key === "Enter") e.currentTarget.blur(); }}
    />
  );
}

function DaysInput({ value, onCommit, onEditing }) {
  const [text, setText] = useState(value ? String(value) : "");
  const focused = useRef(false);
  useEffect(() => { if (!focused.current) setText(value ? String(value) : ""); }, [value]);
  return (
    <input
      className="in num sm"
      value={text}
      placeholder={"\u2014"}
      inputMode="decimal"
      onFocus={(e) => { focused.current = true; if (onEditing) onEditing(1); e.target.select(); }}
      onChange={(e) => setText(e.target.value)}
      onBlur={() => {
        focused.current = false;
        if (onEditing) onEditing(-1);
        const n = parseFloat(String(text).replace(/[^0-9.\-]/g, ""));
        const v = isFinite(n) && n >= 0 ? Math.round(n * 10) / 10 : 0;
        setText(v ? String(v) : "");
        onCommit(v);
      }}
      onKeyDown={(e) => { if (e.key === "Enter") e.currentTarget.blur(); }}
    />
  );
}

function TextInput({ value, onCommit, onEditing, placeholder, className }) {
  const [text, setText] = useState(value || "");
  const focused = useRef(false);
  useEffect(() => { if (!focused.current) setText(value || ""); }, [value]);
  return (
    <input
      className={className || "in"}
      value={text}
      placeholder={placeholder || ""}
      onFocus={() => { focused.current = true; if (onEditing) onEditing(1); }}
      onChange={(e) => setText(e.target.value)}
      onBlur={() => { focused.current = false; if (onEditing) onEditing(-1); onCommit(text.trim()); }}
      onKeyDown={(e) => { if (e.key === "Enter") e.currentTarget.blur(); }}
    />
  );
}

function Pill({ tone: t, children }) {
  return <span className={"sp " + (t || "flat")}>{children}</span>;
}

function Delta({ value }) {
  const v = Number(value) || 0;
  if (!v) return <span className="d flat">{"\u2014"}</span>;
  return (
    <span className={"d " + (v > 0 ? "up" : "down")}>
      <span className="ar">{v > 0 ? "\u2191" : "\u2193"}</span>{fmtMoney(Math.abs(v))}
    </span>
  );
}


function StageSelect({ value, stages, onChange, onEditing }) {
  return (
    <select
      className="sel"
      value={value || ""}
      onFocus={() => onEditing && onEditing(1)}
      onBlur={() => onEditing && onEditing(-1)}
      onChange={(e) => onChange(e.target.value)}
    >
      <option value="">{"stage\u2026"}</option>
      {stages.map((s) => <option key={s.id} value={s.id}>{s.name}</option>)}
    </select>
  );
}

/* Semicircular coverage gauge: the one big visual on the master tab. */
function Gauge({ pct, tone: t }) {
  const w = 168, h = 104, cx = 84, cy = 88, r = 68, sw = 15;
  const p = Math.max(0, Math.min(100, pct)) / 100;
  const a = Math.PI * (1 - p);
  const x = cx + r * Math.cos(a);
  const y = cy - r * Math.sin(a);
  return (
    <svg className="gauge" width={w} height={h} viewBox={"0 0 " + w + " " + h} aria-hidden="true">
      <path className="gauge-arc gauge-bg" strokeWidth={sw}
        d={"M " + (cx - r) + " " + cy + " A " + r + " " + r + " 0 0 1 " + (cx + r) + " " + cy} />
      {p > 0.004 ? (
        <path className={"gauge-arc gauge-val " + t} strokeWidth={sw}
          d={"M " + (cx - r) + " " + cy + " A " + r + " " + r + " 0 0 1 " + x.toFixed(2) + " " + y.toFixed(2)} />
      ) : null}
      <text className="gauge-pct" x={cx} y={cy - 16} textAnchor="middle">{Math.round(pct)}%</text>
      <text className="gauge-lab" x={cx} y={cy + 2} textAnchor="middle">OF TARGET</text>
    </svg>
  );
}

/* Down is good: deals are clearing the stage faster than they were. */
function DaysTrend({ trends, compact }) {
  const shown = trends.filter((t) => t.ok);
  if (!shown.length) return <span className="faint" style={{ fontSize: "12px", fontWeight: 600 }}>no history yet</span>;
  return (
    <span className="trend">
      {(compact ? shown.slice(0, 3) : shown).map((t) => {
        const flat = Math.abs(t.pct) < 1;
        const cls = flat ? "flat" : (t.pct < 0 ? "good" : "bad");
        return (
          <span key={t.weeks} className={"tchip " + cls}
            title={"vs " + shortDate(t.weekOf) + ", when it was " + fmtDays(t.then)}>
            <b>{t.weeks}w</b>
            {flat ? " \u2014" : (t.pct < 0 ? " \u2193" : " \u2191") + Math.abs(Math.round(t.pct)) + "%"}
          </span>
        );
      })}
    </span>
  );
}

/* The headline is a sum across every stage, which is not obvious from the
   number alone. This shows the working so it never has to be taken on trust. */
function CoverWorking({ data, repIds }) {
  const stages = data.config.stages;
  const agg = aggregate(data.current, repIds, stages);
  const rows = stages.map((st, i) => ({
    name: st.name,
    gpv: agg.byStage[st.id].gpv,
    odds: activationOdds(i),
    value: agg.byStage[st.id].gpv * activationOdds(i)
  }));
  const total = rows.reduce((a, r) => a + r.value, 0);
  return (
    <div className="calc">
      {rows.map((r) => (
        <span key={r.name} className="calc-part">
          <b>{r.name.split(" ")[0]}</b> {fmtMoney(r.gpv)} &times; {(r.odds * 100).toFixed(0)}% = {fmtMoney(r.value)}
        </span>
      ))}
      <span className="calc-total">total {fmtMoney(total)}</span>
    </div>
  );
}

function Spark({ points }) {
  const v = (points || []).filter((p) => isFinite(p));
  if (v.length < 2) return null;
  const min = Math.min.apply(null, v), max = Math.max.apply(null, v);
  const span = (max - min) || 1;
  const w = 54, h = 14, pad = 2;
  const step = (w - pad * 2) / (v.length - 1);
  const pts = v.map((x, i) => (pad + i * step).toFixed(1) + "," + (h - pad - ((x - min) / span) * (h - pad * 2)).toFixed(1));
  const rising = v[v.length - 1] > v[0];
  return (
    <svg className="spark" width={w} height={h} viewBox={"0 0 " + w + " " + h} aria-hidden="true">
      <polyline points={pts.join(" ")} className={"spark-line " + (rising ? "bad" : "good")} />
    </svg>
  );
}

function Bar({ value, target, scale, tone: t, pledged }) {
  const s = scale > 0 ? scale : 1;
  const w = Math.max(0, Math.min(100, (Math.max(value, 0) / s) * 100));
  const tx = Math.max(0, Math.min(100, (Math.max(target, 0) / s) * 100));
  const pw = pledged ? Math.max(0, Math.min(100 - w, (pledged / s) * 100)) : 0;
  return (
    <span className="st-bar">
      <span className={"st-fill " + t} style={{ width: w.toFixed(1) + "%" }} />
      {pw > 0 ? <span className="st-pledge" style={{ left: w.toFixed(1) + "%", width: pw.toFixed(1) + "%" }} /> : null}
      {target > 0 ? <span className="st-tick" style={{ left: tx.toFixed(1) + "%" }} /> : null}
    </span>
  );
}

/* ---------------------------------------------------------- master view */

function buildFocus(d, monday) {
  const moves = [], light = [], extras = [];
  activeRepsOf(d).forEach((r) => {
    d.config.stages.forEach((st, i) => {
      const f = stageFlow(d, r.id, i);
      if (f.state === "move") {
        moves.push({
          k: "bad", sort: f.outShort, rep: r,
          text: <>needs <em>{fmtMoney(f.outShort)}</em> more named out of <b>{st.name}</b>
            {" "}into {f.next ? f.next.name : "live"} this week</>
        });
      }
      if (f.hole) {
        const h = impactHorizon(i);
        light.push({
          k: "warn", sort: f.lightBy, rep: r,
          text: <>is <em>{fmtMoney(f.lightBy)}</em> light in <b>{st.name}</b>, and what goes in now activates
            around {h.label} &mdash; a <em>{h.months.toFixed(1)}-month</em> lead time, so it has to start this week</>
        });
      }
    });
  });
  moves.sort((a, b) => b.sort - a.sort);
  light.sort((a, b) => b.sort - a.sort);

  d.commits.filter((c) => c.status === "open" && weeksBetween(c.weekOf, monday) >= 2).forEach((c) => {
    const rep = d.config.reps.filter((r) => r.id === c.repId)[0];
    extras.push({
      k: "warn", rep,
      text: <><b>{c.name || "An unnamed deal"}</b> has not moved in <em>{weeksBetween(c.weekOf, monday)} weeks</em></>
    });
  });
  activeRepsOf(d).forEach((r) => {
    if (commitStats(d.commits, r.id, monday).thisWeek.length === 0) {
      extras.push({ k: "warn", rep: r, text: <>has named nothing to move this week</> });
    }
    /* Direction of travel beats an absolute number: a stage getting slower
       over a month is worth raising whatever the headline figure is. */
    d.config.stages.forEach((st) => {
      const t = daysTrends(d, [r.id], st.id, monday).filter((x) => x.ok && x.weeks === 4)[0];
      if (t && t.pct >= 15) {
        extras.push({
          k: "warn", rep: r,
          text: <><b>{st.name}</b> has slowed <em>{Math.round(t.pct)}%</em> over four weeks,
            from {fmtDays(t.then)} to {fmtDays(cellOf(d.current, r.id, st.id).avgDays)}</>
        });
      }
    });
  });
  return moves.slice(0, 5).concat(light.slice(0, 2)).concat(extras.slice(0, 2));
}

function MasterView({ ctx }) {
  const { data, stages, ids, monday, baseline, actions, onEditing, setTab } = ctx;
  const cur = aggregate(data.current, ids, stages);
  const base = baseline ? aggregate(baseline.reps, ids, stages) : null;
  const team = commitStats(data.commits, null, monday);
  const cover = coverOf(data, ids);
  const tgtOne = targetCover();
  const tgt = { months: tgtOne.months, monthsLocked: tgtOne.monthsLocked, monthsSelling: tgtOne.monthsSelling };
  const coverPct = tgt.months > 0 ? (cover.months / tgt.months) * 100 : 0;
  const coverTone = tone(cover.months, tgt.months);
  const flow = flowOf(data, ids, monday);
  const flowTone = tone(flow.named, flow.need);
  const discNeed = weeklyOutflowNeed(0) * ids.length;
  const discNamed = data.commits
    .filter((c) => c.status === "open" && c.fromStage === stages[0].id && ids.indexOf(c.repId) >= 0)
    .reduce((a, c) => a + (Number(c.gpv) || 0), 0);

  const caps = weeklyCaptures(data.snapshots).slice(-8);
  const trend = {};
  stages.forEach((st) => {
    trend[st.id] = caps.map((s) => aggregate(s.reps, ids, stages).byStage[st.id].avgDays);
  });

  const scale = Math.max.apply(null, stages.map((st) => Math.max(cur.byStage[st.id].gpv, teamFloor(data, st))).concat([1]));
  const focus = buildFocus(data, monday);
  const maxMonths = Math.max.apply(null, activeRepsOf(data).map((r) => coverOf(data, [r.id]).months).concat([tgtOne.months]));

  return (
    <>
      <div className="headline">
        <div className="headline-row">
          <Gauge pct={Math.min(coverPct, 999)} tone={coverTone} />
          <div>
            <div className="hero-k">How long the book lasts</div>
            <div className="hero-v">{cover.months.toFixed(1)} <span style={{ fontSize: "22px", fontWeight: 700 }}>months</span></div>
            <div className="hero-s">
              If no new deal ever came in, what the team is already working would keep activation at{" "}
              <b>{fmtMoney(ACTIVATION_PER_MONTH * ids.length)} a month</b> for {cover.months.toFixed(1)} months.
              A full book lasts <b>{tgt.months.toFixed(1)}</b>.
              <div className="faint" style={{ fontSize: "12.5px", marginTop: "4px", fontWeight: 600 }}>
                {fmtMoney(cover.total)} expected to activate across all five stages, against{" "}
                {fmtMoney(tgtOne.total * ids.length)} for a full book
              </div>
              <CoverWorking data={data} repIds={ids} />
            </div>
          </div>
          <div className="minis">
            <div className="mini">
              <div className="mini-k">Already won</div>
              <div className="mini-v">{cover.monthsLocked.toFixed(1)}m</div>
              <div className="mini-s">signed, waiting to go live &middot; target {tgt.monthsLocked.toFixed(1)}m</div>
            </div>
            <div className="mini">
              <div className="mini-k">Still to win</div>
              <div className="mini-v">{cover.monthsSelling.toFixed(1)}m</div>
              <div className="mini-s">still has to be sold &middot; target {tgt.monthsSelling.toFixed(1)}m</div>
            </div>
            <div className="mini">
              <div className="mini-k">Since Monday</div>
              <div className="mini-v">{base ? fmtSignedMoney(cur.total - base.total) : "\u2014"}</div>
              <div className="mini-s">{baseline ? "vs " + shortDate(baseline.weekOf) : "no baseline"}</div>
            </div>
          </div>
        </div>
        <div className="track">
          <div className={"track-fill " + coverTone} style={{ width: Math.min(100, coverPct).toFixed(1) + "%" }} />
          <div className="track-tick" style={{ left: "100%" }} />
        </div>
        <div className="track-labels">
          <span>0</span>
          <span>{tgt.months.toFixed(1)} months = a full book</span>
        </div>
      </div>

      <div className="headline" style={{ marginTop: "14px" }}>
        <div className="headline-row">
          <Gauge pct={Math.min(flow.pct, 999)} tone={flowTone} />
          <div>
            <div className="hero-k">Deals named to move this week</div>
            <div className="hero-v">{fmtMoney(flow.named)}</div>
            <div className="hero-s">
              of the <b>{fmtMoney(flow.need)}</b> that should move up a stage this week
              <div className="faint" style={{ fontSize: "12.5px", marginTop: "4px", fontWeight: 600 }}>
                the book above only refills if this one gets hit
              </div>
            </div>
          </div>
          <div className="minis">
            <div className="mini">
              <div className="mini-k">Out of Discovery</div>
              <div className="mini-v">{fmtMoney(discNamed)}</div>
              <div className="mini-s">of {fmtMoney(discNeed)} needed</div>
            </div>
            <div className="mini">
              <div className="mini-k">Open commits</div>
              <div className="mini-v">{team.open.length}</div>
              <div className="mini-s">{fmtMoney(team.openGpv)} in play</div>
            </div>
            <div className="mini">
              <div className="mini-k">Team hit rate</div>
              <div className="mini-v">{team.hitRate === null ? "\u2014" : Math.round(team.hitRate * 100) + "%"}</div>
              <div className="mini-s">{team.moved} moved, {team.missed} missed</div>
            </div>
          </div>
        </div>
      </div>

      <div className="section">
        <div className="section-h"><h2>This week&rsquo;s focus</h2><span className="hint">biggest gaps first</span></div>
        {focus.length === 0 ? (
          <div className="all-clear">Every rep is on target in every stage. Short 1:1s this week.</div>
        ) : (
          <div className="focus">
            {focus.map((f, i) => (
              <div key={i} className={"focus-row " + f.k}>
                <div className="focus-who"><span className="pip" />{f.rep ? shortName(f.rep.name) : "Team"}</div>
                <div className="focus-txt">{f.text}</div>
                <div><button className="btn" onClick={() => setTab(f.rep ? f.rep.id : "master")}>Open</button></div>
              </div>
            ))}
          </div>
        )}
      </div>

      <div className="section">
        <div className="section-h"><h2>The funnel</h2><span className="hint">bar is what is held, the pill is what is moving out this week</span></div>
        <div className="fun-head">
          <div>Stage</div><div />
          <div style={{ textAlign: "right" }}>GPV</div>
          <div style={{ textAlign: "right" }}>moving out</div>
          <div style={{ textAlign: "right" }}>Median days in stage</div>
        </div>
        {stages.map((st, i) => {
          const a = cur.byStage[st.id];
          const b0 = base ? base.byStage[st.id] : null;
          const b = b0 && (b0.gpv > 0 || b0.avgDays > 0) ? b0 : null;
          const floor = teamFloor(data, st);
          const t = tone(a.gpv, floor);
          /* what the whole team must push out of this stage this week, and
             what they have actually committed */
          const outNeedTeam = weeklyOutflowNeed(i) * ids.length;
          const movedTeam = data.commits
            .filter((c) => c.status === "open" && c.fromStage === st.id && ids.indexOf(c.repId) >= 0)
            .reduce((x, c) => x + (Number(c.gpv) || 0), 0);
          return (
            <div className="fun-row" key={st.id}>
              <div className="fun-name"><span className="idx">{i + 1}</span>{st.name}</div>
              <div><Bar value={a.gpv} target={floor} scale={scale} tone={t} /></div>
              <div className="fun-gpv">
                {fmtMoney(a.gpv)}
                <div style={{ fontSize: "12px", marginTop: "2px", fontWeight: 600 }}>{b ? <Delta value={a.gpv - b.gpv} /> : null}</div>
              </div>
              <div className="fun-gap">
                <Pill tone={movedTeam >= outNeedTeam ? "good" : (movedTeam > 0 ? "warn" : "bad")}>
                  {fmtMoney(movedTeam)} of {fmtMoney(outNeedTeam)}
                </Pill>
                {a.gpv < floor * 0.6 ? (
                  <div style={{ fontSize: "11px", fontWeight: 700, marginTop: "4px", color: "var(--warn)" }}>
                    thin &middot; {impactHorizon(i).months.toFixed(1)}m lead time
                  </div>
                ) : null}
              </div>
              <div className="fun-days">
                {fmtDays(a.avgDays)}
                <div style={{ marginTop: "4px", display: "flex", justifyContent: "flex-end" }}>
                  <DaysTrend trends={daysTrends(data, ids, st.id, monday)} compact />
                </div>
                <div style={{ marginTop: "3px", display: "flex", justifyContent: "flex-end" }}><Spark points={trend[st.id]} /></div>
              </div>
            </div>
          );
        })}
        <div className="fun-foot">
          <div className="fun-name">Total pipeline</div><div />
          <div className="fun-gpv">{fmtMoney(cur.total)}</div>
          <div className="fun-gap" />
          <div className="fun-days">{base ? <Delta value={cur.total - base.total} /> : null}</div>
        </div>
      </div>

      <div className="section">
        <div className="section-h">
          <h2>The team</h2><span className="hint">how many months each book would last with nothing new added &mdash; a full one lasts {tgt.months.toFixed(1)}</span>
          <span className="spacer" />
          <button className="btn txt" onClick={actions.toggleMatrix}>{ctx.showMatrix ? "Hide" : "Show"} stage breakdown</button>
        </div>
        <table className="tbl">
          <thead>
            <tr>
              <th>Rep</th>
              <th className="r nar">Book lasts</th>
              <th className="r nar">Already won</th>
              <th className="r nar">Still to win</th>
              <th className="r nar">Named to move</th>
              <th className="r nar">Thin stages</th>
              <th className="r nar">Hit rate</th>
            </tr>
          </thead>
          <tbody>
            {activeRepsOf(data).map((r) => {
              const s2 = commitStats(data.commits, r.id, monday);
              const cv = coverOf(data, [r.id]);
              const fl = flowOf(data, [r.id], monday);
              let thin = 0;
              stages.forEach((st, i) => { if (stageFlow(data, r.id, i).hole) thin += 1; });
              const ctone = tone(cv.months, tgt.months);
              const barMax = Math.max(maxMonths, tgt.months);
              return (
                <tr key={r.id}>
                  <td>
                    <div className="namecell">
                      <button className="lnk" onClick={() => setTab(r.id)}>{r.name}</button>
                      <span className="repbar">
                        <span className={ctone} style={{ width: ((cv.months / barMax) * 100).toFixed(1) + "%" }} />
                        <i style={{ left: ((tgt.months / barMax) * 100).toFixed(1) + "%" }} />
                      </span>
                    </div>
                  </td>
                  <td className="r nar strong">{cv.months.toFixed(1)}m</td>
                  <td className="r nar muted">{cv.monthsLocked.toFixed(1)}m</td>
                  <td className="r nar muted">{cv.monthsSelling.toFixed(1)}m</td>
                  <td className="r nar">
                    <Pill tone={fl.named >= fl.need ? "good" : (fl.named > 0 ? "warn" : "bad")}>
                      {fmtMoney(fl.named)} of {fmtMoney(fl.need)}
                    </Pill>
                  </td>
                  <td className="r nar">{thin ? <Pill tone="warn">{thin}</Pill> : <Pill tone="good">none</Pill>}</td>
                  <td className="r nar">{s2.hitRate === null ? <span className="faint">{"\u2014"}</span> : Math.round(s2.hitRate * 100) + "%"}</td>
                </tr>
              );
            })}
          </tbody>
        </table>

        {ctx.showMatrix ? (
          <div className="matrix-wrap" style={{ marginTop: "20px" }}>
            <table className="tbl">
              <thead>
                <tr>
                  <th>Rep</th>
                  {stages.map((st) => <th key={st.id} className="r nar">{st.name}</th>)}
                  <th className="r nar">Total</th>
                </tr>
              </thead>
              <tbody>
                {activeRepsOf(data).map((r) => {
                  const m = aggregate(data.current, [r.id], stages);
                  return (
                    <tr key={r.id}>
                      <td className="muted">{shortName(r.name)}</td>
                      {stages.map((st) => {
                        const g = m.byStage[st.id].gpv;
                        const t = repTarget(data, r.id, st.id);
                        return (
                          <td key={st.id} className="r nar" style={g < t ? { color: "var(--bad)" } : null}>
                            {g ? fmtMoney(g) : <span className="faint">{"\u2014"}</span>}
                          </td>
                        );
                      })}
                      <td className="r nar strong">{fmtMoney(m.total)}</td>
                    </tr>
                  );
                })}
                <tr>
                  <td className="muted">Team floor</td>
                  {stages.map((st) => <td key={st.id} className="r nar faint">{fmtMoney(teamFloor(data, st))}</td>)}
                  <td className="r nar faint">{fmtMoney(stages.reduce((a, s) => a + teamFloor(data, s), 0))}</td>
                </tr>
              </tbody>
            </table>
          </div>
        ) : null}
      </div>
    </>
  );
}

/* ------------------------------------------------------------- rep view */

/* One deal the rep has named to move out of the stage they are looking at.
   The only choices are what it is called, where it is going, and how big. */
function CommitRow({ commit, stages, actions, onEditing, monday }) {
  const age = weeksBetween(commit.weekOf, monday);
  return (
    <div className="cmt">
      <span>
        <TextInput value={commit.name} placeholder="Opportunity name" onEditing={onEditing}
          onCommit={(v) => actions.setCommit(commit.id, "name", v)} />
        {age > 0 ? <span className="tag carried">carried {age}w</span> : null}
      </span>
      <span className="cmt-src">
        <StageSelect value={commit.toStage} stages={stages} onEditing={onEditing}
          onChange={(v) => actions.setCommit(commit.id, "toStage", v)} />
      </span>
      <MoneyInput value={commit.gpv} onEditing={onEditing} onCommit={(v) => actions.setCommit(commit.id, "gpv", v)} />
      <span className="acts">
        <button className="btn ok" onClick={() => actions.resolveCommit(commit.id, "moved")}>Moved</button>
        <button className="btn no" onClick={() => actions.resolveCommit(commit.id, "missed")}>Missed</button>
        <button className="btn x" title="Delete" onClick={() => actions.deleteCommit(commit.id)}>×</button>
      </span>
    </div>
  );
}

function RepView({ ctx, rep }) {
  const { data, stages, monday, baseline, actions, onEditing } = ctx;
  const [openStage, setOpenStage] = useState(null);
  const [showHist, setShowHist] = useState(false);

  const mine = aggregate(data.current, [rep.id], stages);
  const mb = baseline ? aggregate(baseline.reps, [rep.id], stages) : null;
  const st = commitStats(data.commits, rep.id, monday);

  const cover = coverOf(data, [rep.id]);
  const tgt = targetCover();
  const flow = flowOf(data, [rep.id], monday);

  /* Open on the first stage that needs work, until the user picks another. */
  let firstShort = stages.length ? stages[0].id : null;
  for (let i = 0; i < stages.length; i++) {
    if (stageFlow(data, rep.id, i).isShort) { firstShort = stages[i].id; break; }
  }
  const activeStage = openStage === undefined || openStage === null ? firstShort : (openStage === "__none__" ? null : openStage);

  const scale = Math.max.apply(null, stages.map((s, i) => {
    const f = stageFlow(data, rep.id, i);
    return Math.max(f.gpv, f.target, f.gpv + f.pledgedIn);
  }).concat([1]));

  const resolved = data.commits.filter((c) => c.repId === rep.id && c.status !== "open");
  const note = (data.current[rep.id] && data.current[rep.id].note) || "";

  return (
    <>
      <div className="headline">
        <div className="headline-row">
          <div>
            <div className="hero-k">{rep.name}</div>
            <div className="hero-v">{cover.months.toFixed(1)} <span style={{ fontSize: "20px", fontWeight: 700 }}>months</span></div>
            <div className="hero-s">
              Their book would keep {fmtMoney(ACTIVATION_PER_MONTH)} a month running for{" "}
              {cover.months.toFixed(1)} months with nothing new added. A full book lasts <b>{tgt.months.toFixed(1)}</b>.
              <div className="faint" style={{ fontSize: "12.5px", marginTop: "4px", fontWeight: 600 }}>
                {fmtMoney(mine.total)} of pipeline across all five stages, of which{" "}
                {fmtMoney(cover.total)} is expected to activate eventually
              </div>
              <CoverWorking data={data} repIds={[rep.id]} />
            </div>
          </div>
          <div className="minis">
            <div className="mini">
              <div className="mini-k">Already won</div>
              <div className="mini-v">{cover.monthsLocked.toFixed(1)}m</div>
              <div className="mini-s">signed, going live &middot; target {tgt.monthsLocked.toFixed(1)}m</div>
            </div>
            <div className="mini">
              <div className="mini-k">Still to win</div>
              <div className="mini-v">{cover.monthsSelling.toFixed(1)}m</div>
              <div className="mini-s">still to be sold &middot; target {tgt.monthsSelling.toFixed(1)}m</div>
            </div>
            <div className="mini">
              <div className="mini-k">Named to move</div>
              <div className="mini-v">{fmtMoney(flow.named)}</div>
              <div className="mini-s">of {fmtMoney(flow.need)} this week</div>
            </div>
          </div>
        </div>
      </div>

      <div className="section">
        <div className="section-h"><h2>Walk the funnel</h2><span className="hint">open a stage to work it</span></div>
        <div className="walk">
          {stages.map((s, i) => {
            const f = stageFlow(data, rep.id, i);
            const inb = takesInbound(i);
            const b = mb ? mb.byStage[s.id] : null;
            /* A capture with nothing in it is not a baseline. Comparing against
               it would report the first week of data entry as a huge jump. */
            const hasBase = !!b && (b.gpv > 0 || b.avgDays > 0);
            const isOpen = s.id === activeStage;
            const t = tone(f.gpv, f.target);
            const edge = f.state === "move" ? "warn" : (f.state === "ok" ? "good" : "bad");

            const nextName = f.next ? f.next.name : "live";
            const stateEl =
              f.state === "empty" ? <Pill tone="bad">nothing to move</Pill>
                : f.state === "move" ? <Pill tone="warn">move {fmtMoney(f.outShort)}</Pill>
                  : <Pill tone="good">on track</Pill>;

            /* One short sentence. The reasoning lives in Settings, not here. */
            let lead;
            if (f.state === "empty") {
              lead = inb
                ? <>Nothing in this stage yet. It fills when {sourceLabel(f)} deals move across.</>
                : <>Nothing in this stage yet. This one fills from prospecting.</>;
            } else if (f.state === "move") {
              lead = <><em>{fmtMoney(f.outNeed)}</em> should move to {nextName} this week.
                {" "}{f.pledgedOut > 0 ? "You have named " + fmtMoney(f.pledgedOut) + "." : "Nothing is named yet."}
                {" "}Add <em>{fmtMoney(f.outShort)}</em> more.</>;
            } else {
              lead = <>Holding <em>{fmtMoney(f.gpv)}</em> and moving <em>{fmtMoney(f.pledgedOut)}</em> to {nextName} this week. On track.</>;
            }

            return (
              <div key={s.id} className={"st" + (isOpen ? " open" : "") + " tone-" + edge}>
                <button className="st-row" onClick={() => setOpenStage(isOpen ? "__none__" : s.id)}>
                  <span className="st-name">
                    <span className="st-chev">{"\u25b6"}</span>
                    <span className="idx">{i + 1}</span>{s.name}
                  </span>
                  <Bar value={f.gpv} target={f.target} scale={scale} tone={t} pledged={f.pledgedIn} />
                  <span className="st-fig">
                    {fmtMoney(f.gpv)}<span className="of"> / {fmtMoney(f.target)}</span>
                    <span className="st-sub">
                      {fmtMoney(f.pledgedOut)} of {fmtMoney(f.outNeed)} out
                    </span>
                    <span className="st-sub">
                      {fmtDays(f.avgDays)} in stage
                      {(() => {
                        const t = daysTrends(data, [rep.id], s.id, monday).filter((x) => x.ok)[0];
                        if (!t || Math.abs(t.pct) < 1) return "";
                        return (t.pct < 0 ? " \u2193" : " \u2191") + Math.abs(Math.round(t.pct)) + "% 1w";
                      })()}
                    </span>
                  </span>
                  <span className="st-state">
                    {stateEl}
                    {f.hole ? <span className="st-risk-dot" title={"Thin by " + fmtMoney(f.lightBy) + ". What enters now activates around " + impactHorizon(i).label + ", so closing it starts this week."} /> : null}
                  </span>
                </button>

                {isOpen ? (
                  <div className="st-body">
                    <p className={"st-lead " + f.state}>{lead}</p>
                    {f.hole ? (
                      <p className="st-risk">
                        <b>{fmtMoney(f.lightBy)} light</b> here, holding {fmtMoney(f.gpv)} of {fmtMoney(f.target)}.
                        {" "}What enters {s.name} now is what activates around <b>{impactHorizon(i).label}</b>, so the{" "}
                        {impactHorizon(i).months.toFixed(1)}-month lead time is the reason to close this
                        <b> now</b>, not later.
                        {inb
                          ? " It fills from " + sourceLabel(f) + ", which is this week's job in that stage."
                          : " It fills from prospecting, so the work starts this week."}
                      </p>
                    ) : null}
                    <div className="st-fields">
                      <span className="st-f">
                        <label>GPV</label>
                        <MoneyInput value={f.gpv} onEditing={onEditing} onCommit={(v) => actions.setCell(rep.id, s.id, "gpv", v)} />
                        {hasBase && b.gpv > 0 ? <Delta value={f.gpv - b.gpv} /> : null}
                      </span>
                      <span className="st-f">
                        <label>median days in stage</label>
                        <DaysInput value={f.avgDays} onEditing={onEditing} onCommit={(v) => actions.setCell(rep.id, s.id, "avgDays", v)} />
                        <DaysTrend trends={daysTrends(data, [rep.id], s.id, monday)} />
                      </span>
                      <span className="st-f">
                        <label>target</label>
                        <span className="fixed">{fmtMoney(f.target)}</span>
                      </span>
                      <span className="st-f">
                        <label>move out weekly</label>
                        <span className="fixed">{fmtMoney(f.outNeed)}</span>
                        <Pill tone={f.outShort > 0 ? "warn" : "good"}>
                          {fmtMoney(f.pledgedOut)} committed
                        </Pill>
                      </span>
                    </div>

                    <div className="cmt-lbl">
                      Moving out of {s.name} this week &mdash; {fmtMoney(f.pledgedOut)} of {fmtMoney(f.outNeed)} needed
                    </div>
                    {f.outbound.length ? f.outbound.map((c) => (
                      <CommitRow key={c.id} commit={c} stages={stages} actions={actions} onEditing={onEditing} monday={monday} />
                    )) : <div className="cmt-none">No deals named yet.</div>}

                    {f.inbound.length ? (
                      <div className="cmt-none" style={{ marginTop: "10px" }}>
                        Arriving from {sourceLabel(f)} this week: {f.inbound.length} deal{f.inbound.length === 1 ? "" : "s"},{" "}
                        {fmtMoney(f.pledgedIn)}. Marked off in {sourceLabel(f)}.
                      </div>
                    ) : null}

                    <div className="row-acts">
                      <button className="btn primary" onClick={() => actions.addCommitOutOf(rep.id, s.id)}>
                        Move a deal out of {s.name}
                      </button>
                      {i < stages.length - 1 ? (
                        <button className="btn txt" onClick={() => setOpenStage(stages[i + 1].id)}>
                          Next: {stages[i + 1].name} {"\u2192"}
                        </button>
                      ) : null}
                    </div>
                  </div>
                ) : null}
              </div>
            );
          })}
        </div>
      </div>

      {resolved.length ? (
        <div className="section">
          <div className="section-h">
            <h2>Track record</h2>
            <span className="hint">{st.moved} moved, {st.missed} missed</span>
            <span className="spacer" />
            <button className="btn txt" onClick={() => setShowHist(!showHist)}>{showHist ? "Hide" : "Show all " + resolved.length}</button>
          </div>
          {showHist ? (
            <table className="tbl">
              <thead>
                <tr>
                  <th>Opportunity</th><th className="r nar">GPV</th><th>Move</th>
                  <th className="nar">Committed</th><th className="nar">Outcome</th><th className="r nar" />
                </tr>
              </thead>
              <tbody>
                {resolved.map((c) => (
                  <tr key={c.id}>
                    <td>{c.name || <span className="faint">unnamed</span>}</td>
                    <td className="r nar">{fmtMoney(c.gpv)}</td>
                    <td className="mv">
                      <b>{ctx.stageName(c.fromStage)}</b> {"\u2192"} <b>{ctx.stageName(c.toStage)}</b>
                    </td>
                    <td className="nar muted">{shortDate(c.weekOf)}</td>
                    <td className="nar"><span className={"tag " + c.status}>{c.status}</span></td>
                    <td className="r nar"><button className="btn x" onClick={() => actions.reopenCommit(c.id)}>reopen</button></td>
                  </tr>
                ))}
              </tbody>
            </table>
          ) : null}
        </div>
      ) : null}

      <div className="section">
        <div className="section-h"><h2>1:1 note</h2></div>
        <textarea
          className="note"
          value={note}
          placeholder="What came out of this week's conversation."
          onFocus={() => onEditing(1)}
          onBlur={() => onEditing(-1)}
          onChange={(e) => actions.setNote(rep.id, e.target.value)}
        />
      </div>
    </>
  );
}

/* -------------------------------------------------------- settings view */

function SettingsView({ ctx }) {
  const { data, stages, actions, onEditing } = ctx;
  const n = activeRepsOf(data).length || 1;
  const floorSum = stages.reduce((a, s) => a + (Number(s.floor) || 0), 0);
  const flows = modelFlows();
  const captures = data.snapshots.slice().sort((a, b) => (b.takenAt || 0) - (a.takenAt || 0));

  return (
    <>
      <div className="section">
        <div className="section-h">
          <h2>The model</h2>
          <span className="hint">fixed targets, sized from the activation goal &mdash; nothing here is editable</span>
        </div>
        <p className="muted" style={{ marginTop: 0, maxWidth: "740px", fontSize: "14px" }}>
          Every rep carries <b>{fmtMoney(PER_REP_TARGET)}</b> of pipeline. That is not a round number
          someone picked: it is what has to sit in the book to activate <b>{fmtMoney(ACTIVATION_PER_MONTH)} a
          month</b>, given how long deals linger in each stage and how many survive it. Start at
          activation, divide back through each conversion rate to get the volume that must enter a
          stage, then multiply by the time it spends there.
        </p>
        <table className="tbl">
          <thead>
            <tr>
              <th>Stage</th>
              <th className="r nar">Sits for</th>
              <th className="r nar">Converts at</th>
              <th className="r nar">So hold</th>
              <th className="r nar">Move out weekly</th>
              <th className="r nar">Team of {n}</th>
            </tr>
          </thead>
          <tbody>
            {stages.map((st, i) => (
              <tr key={st.id}>
                <td><span className="idx">{i + 1}</span> {st.name}</td>
                <td className="r nar muted">{st.dwellDays}d</td>
                <td className="r nar muted">{Math.round(st.conv * 100)}%</td>
                <td className="r nar strong">{fmtMoney(st.floor)}</td>
                <td className="r nar strong">{fmtMoney(weeklyOutflowNeed(i))}</td>
                <td className="r nar muted">{fmtMoney(teamFloor(data, st))} held, {fmtMoney(weeklyOutflowNeed(i) * n)}/wk out</td>
              </tr>
            ))}
            <tr>
              <td className="strong">Per rep</td>
              <td className="r nar muted">{stages.reduce((a, x) => a + (x.dwellDays || 0), 0)}d total</td>
              <td className="r nar muted">{(stages.reduce((a, x) => a * (x.conv || 1), 1) * 100).toFixed(1)}% overall</td>
              <td className="r nar strong">{fmtMoney(floorSum)}</td>
              <td className="r nar" />
              <td className="r nar strong">{fmtMoney(stages.reduce((a, x) => a + teamFloor(data, x), 0))} held</td>
            </tr>
          </tbody>
        </table>
        <p className="muted" style={{ marginTop: "14px", maxWidth: "740px", fontSize: "13.5px" }}>
          Implementation is pinned at three months&rsquo; cover, since a signed deal still takes about{" "}
          {STAGE_MODEL[4].dwellDays} days to go live. The four earlier stages are scaled so the total
          lands on {fmtMoney(PER_REP_TARGET)}.
        </p>
        <table className="tbl" style={{ marginTop: "18px" }}>
          <thead>
            <tr>
              <th>A dollar sitting in</th>
              <th className="r nar">Odds it activates</th>
              <th className="r nar">Worth</th>
              <th className="r nar">Target there</th>
              <th className="r nar">Expected activation</th>
            </tr>
          </thead>
          <tbody>
            {stages.map((st, i) => (
              <tr key={st.id}>
                <td><span className="idx">{i + 1}</span> {st.name}</td>
                <td className="r nar muted">{(activationOdds(i) * 100).toFixed(1)}%</td>
                <td className="r nar muted">{(activationOdds(i) / activationOdds(0)).toFixed(1)}x Discovery</td>
                <td className="r nar muted">{fmtMoney(st.floor)}</td>
                <td className="r nar strong">{fmtMoney(st.floor * activationOdds(i))}</td>
              </tr>
            ))}
            <tr>
              <td className="strong">Whole book</td>
              <td className="r nar" />
              <td className="r nar" />
              <td className="r nar strong">{fmtMoney(PER_REP_TARGET)}</td>
              <td className="r nar strong">{fmtMoney(targetCover().total)} &middot; {targetCover().months.toFixed(1)} months</td>
            </tr>
          </tbody>
        </table>
        <p className="muted" style={{ marginTop: "14px", maxWidth: "740px", fontSize: "13.5px" }}>
          <b>Shape is not scored.</b> A dollar in Mutual close plan is worth roughly ten in Discovery, so a
          rep who is heavy late and light in the middle is ahead, not behind, and the headline reflects
          that. A thin stage is still called out, with its lead time attached: what crosses into a stage
          now is what activates months later, so a long lead time is a reason to close the gap this week
          rather than a reason it can wait. Signed business and unsold pipeline are reported separately,
          because a full implementation queue can otherwise hide a selling motion that has stopped.
        </p>
        <p className="muted" style={{ marginTop: "10px", maxWidth: "740px", fontSize: "13.5px" }}>
          <b>The holding figure is the easier half.</b> A stage that is full but never empties is a
          blockage, not a healthy book, so each stage also has a weekly movement requirement: what has to
          leave it is exactly what has to enter the next one. Discovery is where that bites &mdash;{" "}
          <b>{fmtMoney(weeklyOutflowNeed(0))} has to cross into Evaluation every week, per rep</b>. A rep
          holding {fmtMoney(PER_REP_TARGET * 0.75)} in Discovery who commits nothing out is not ahead of
          target, they are months of stock standing still, and the app marks that stage as stuck rather
          than green.
        </p>
      </div>

      <div className="section">
        <div className="section-h"><h2>Reps</h2><span className="hint">unticking keeps history and drops them from the team total, but every active rep still carries the full per-rep target</span></div>
        <table className="tbl">
          <thead>
            <tr><th>Name</th><th className="nar">Active</th><th className="r nar">Pipeline</th><th className="r nar">Target</th><th className="r nar">Gap</th><th className="r nar" /></tr>
          </thead>
          <tbody>
            {data.config.reps.map((r) => {
              const m = aggregate(data.current, [r.id], stages);
              let t = 0;
              stages.forEach((s) => { t += repTarget(data, r.id, s.id); });
              return (
                <tr key={r.id}>
                  <td><TextInput className="in" value={r.name} onEditing={onEditing} onCommit={(v) => actions.setRepName(r.id, v)} /></td>
                  <td className="nar"><input type="checkbox" checked={r.active !== false} onChange={(e) => actions.setRepActive(r.id, e.target.checked)} /></td>
                  <td className="r nar">{fmtMoney(m.total)}</td>
                  <td className="r nar muted">{fmtMoney(t)}</td>
                  <td className="r nar"><Delta value={m.total - t} /></td>
                  <td className="r nar"><button className="btn x" title="Remove rep" onClick={() => actions.removeRep(r.id)}>×</button></td>
                </tr>
              );
            })}
          </tbody>
        </table>
        <div className="row-acts">
          <button className="btn primary" onClick={actions.addRep}>Add rep</button>
        </div>
      </div>

      <div className="section">
        <div className="section-h"><h2>Captures</h2><span className="hint">Monday captures set the baseline; manual ones are history only</span></div>
        <table className="tbl">
          <thead>
            <tr><th className="nar">Week of</th><th className="nar">Taken</th><th className="nar">Kind</th><th className="r nar">Pipeline then</th><th className="r nar" /></tr>
          </thead>
          <tbody>
            {captures.length === 0 ? (
              <tr><td className="empty" colSpan={5}>No captures yet.</td></tr>
            ) : captures.map((s) => {
              const a = aggregate(s.reps, ctx.ids, stages);
              return (
                <tr key={s.id}>
                  <td className="nar">{shortDate(s.weekOf)}</td>
                  <td className="nar muted">{s.takenAt ? new Date(s.takenAt).toLocaleDateString() + " " + clockTime(s.takenAt) : "\u2014"}</td>
                  <td className="nar"><span className="tag">{s.auto ? "Monday" : "manual"}</span></td>
                  <td className="r nar">{fmtMoney(a.total)}</td>
                  <td className="r nar"><button className="btn x" title="Delete capture" onClick={() => actions.deleteSnapshot(s.id)}>×</button></td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>

      <div className="section">
        <div className="section-h"><h2>Data</h2><span className="hint">nothing here is lost by redeploying the app</span></div>
        <div className="row-acts">
          <button className="btn" onClick={actions.copyBackup}>Copy everything as JSON</button>
          <button className="btn" onClick={actions.loadSample}>Load sample numbers</button>
          <button className="btn no" onClick={actions.clearNumbers}>Clear all numbers</button>
        </div>
        <p className="faint" style={{ marginTop: "10px", fontSize: "13px" }}>
          Sample numbers fill every rep and a prior week so you can see the tool working. Clearing wipes
          GPV, days, commits and captures but keeps your reps, stages, floors and targets.
        </p>
      </div>
    </>
  );
}

/* --------------------------------------------------------- sample data */

const SAMPLE_NOW = {
  rep_david: [[6, 44], [4.5, 27], [2, 16], [1.5, 11], [3, 7]],
  rep_ryan: [[4.5, 51], [3, 33], [1.5, 19], [1, 13], [2, 9]],
  rep_aubrey: [[5.5, 39], [4, 25], [2, 14], [1.5, 10], [2.5, 6]],
  rep_zachariah: [[3.5, 58], [2.5, 36], [1, 24], [0.5, 15], [1.5, 12]],
  rep_tacen: [[4, 47], [3, 29], [1, 17], [0.5, 12], [1, 8]],
  rep_wilmer: [[5, 42], [3.5, 31], [1.5, 20], [1, 14], [2, 10]],
  rep_joey: [[3.5, 63], [2.5, 38], [0.5, 26], [0.5, 16], [1, 11]]
};
const SAMPLE_LAST = {
  rep_david: [[5, 48], [4, 29], [2, 18], [1, 13], [2.5, 8]],
  rep_ryan: [[4.5, 55], [3, 35], [1.5, 21], [1, 14], [2, 10]],
  rep_aubrey: [[5, 43], [3.5, 27], [1.5, 16], [1.5, 11], [2, 7]],
  rep_zachariah: [[3.5, 60], [2.5, 38], [1, 25], [0.5, 16], [1.5, 13]],
  rep_tacen: [[3.5, 50], [2.5, 31], [1, 19], [0.5, 13], [1, 9]],
  rep_wilmer: [[4.5, 45], [3, 33], [1.5, 22], [0.5, 15], [2, 11]],
  rep_joey: [[3.5, 66], [2.5, 40], [0.5, 28], [0.5, 17], [1, 12]]
};
function sampleBoard(d, rows) {
  const out = {};
  d.config.reps.forEach((r) => {
    const row = rows[r.id];
    const stages = {};
    d.config.stages.forEach((st, i) => {
      const p = row && row[i] ? row[i] : [0, 0];
      stages[st.id] = { gpv: Math.round(p[0] * 1e6), avgDays: p[1] };
    });
    out[r.id] = { stages, note: "" };
  });
  return out;
}
function buildSample(d) {
  const mon = thisMonday();
  const wk = (n) => isoDate(new Date(mondayOf(new Date()).getTime() - n * 7 * 864e5));
  const s = d.config.stages;
  const id = (i) => (s[i] ? s[i].id : "");   /* stage ids come from the model */
  d.current = sampleBoard(d, SAMPLE_NOW);
  const last = sampleBoard(d, SAMPLE_LAST);
  const floors = {};
  s.forEach((st) => { floors[st.id] = Number(st.floor) || 0; });
  d.snapshots = [
    { id: uid("snap"), weekOf: wk(1), takenAt: Date.now() - 7 * 864e5, auto: true, coverageTarget: d.config.coverageTarget, floors, reps: last },
    { id: uid("snap"), weekOf: mon, takenAt: Date.now() - 3 * 864e5, auto: true, coverageTarget: d.config.coverageTarget, floors, reps: last }
  ];
  const mk = (repId, name, gpv, from, to, weekOf, status) => ({
    id: uid("cmt"), repId, name, gpv: Math.round(gpv * 1e6),
    fromStage: from, toStage: to, weekOf, status,
    resolvedWeek: status === "open" ? null : mon, createdAt: Date.now()
  });
  d.commits = [
    mk("rep_david", "Halberd Retail", 2.4, id(1), id(2), mon, "open"),
    mk("rep_david", "Kestrel Group", 1.1, id(2), id(3), wk(3), "open"),
    mk("rep_ryan", "Tarn Logistics", 1.2, id(0), id(1), mon, "open"),
    mk("rep_aubrey", "Vellum Health", 1.5, id(3), id(4), mon, "open"),
    mk("rep_aubrey", "Pellworth Dental", 0.8, id(1), id(2), mon, "open"),
    mk("rep_tacen", "Calder Foods", 0.6, id(0), id(1), mon, "open"),
    mk("rep_wilmer", "Ashgrove Union", 1.2, id(2), id(3), wk(1), "open"),
    mk("rep_david", "Ridgeline Motors", 1.6, id(1), id(2), wk(1), "moved"),
    mk("rep_david", "Pelham and Co", 0.9, id(0), id(1), wk(2), "missed"),
    mk("rep_ryan", "Marlow Freight", 1.3, id(2), id(3), wk(1), "missed"),
    mk("rep_aubrey", "Southbank Clinic", 1.1, id(1), id(2), wk(1), "moved"),
    mk("rep_wilmer", "Bracken Supply", 0.95, id(1), id(2), wk(2), "moved"),
    mk("rep_tacen", "Orrery Grocers", 0.5, id(1), id(2), wk(2), "missed"),
    mk("rep_zachariah", "Linden Systems", 1.4, id(1), id(2), wk(2), "missed")
  ];
  return d;
}

/* ------------------------------------------------------------------ app */

export default function App() {
  const [data, setData] = useState(null);
  const [tab, setTab] = useState("master");
  const [showMatrix, setShowMatrix] = useState(false);
  const [status, setStatus] = useState({ kind: "load", text: "Loading" });

  const dataRef = useRef(null);
  const dirtyRef = useRef(false);
  const savingRef = useRef(false);
  const editingRef = useRef(0);
  const revRef = useRef(0);
  const lastRawRef = useRef("");
  const timerRef = useRef(null);
  const storageOkRef = useRef(false);
  const doSaveRef = useRef(null);

  const onEditing = useCallback((delta) => {
    editingRef.current = Math.max(0, editingRef.current + delta);
  }, []);

  const schedule = useCallback(() => {
    if (timerRef.current) clearTimeout(timerRef.current);
    timerRef.current = setTimeout(() => { if (doSaveRef.current) doSaveRef.current(); }, SAVE_DEBOUNCE_MS);
  }, []);

  const doSave = useCallback(async () => {
    const d = dataRef.current;
    if (!d || !storageOkRef.current) return;
    const rev = revRef.current;
    const raw = JSON.stringify(d);
    savingRef.current = true;
    setStatus({ kind: "save", text: "Saving" });
    try {
      const r = await fetch("/api/data", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ value: raw })
      });
      if (!r.ok) throw new Error("HTTP " + r.status);
      lastRawRef.current = raw;
      if (revRef.current === rev) {
        dirtyRef.current = false;
        setStatus({ kind: "ok", text: "Saved " + clockTime(Date.now()) });
      } else {
        schedule();
      }
    } catch (e) {
      dirtyRef.current = true;
      setStatus({ kind: "err", text: "Save failed, retrying" });
      if (timerRef.current) clearTimeout(timerRef.current);
      timerRef.current = setTimeout(() => { if (doSaveRef.current) doSaveRef.current(); }, 5000);
    } finally {
      savingRef.current = false;
    }
  }, [schedule]);

  useEffect(() => { doSaveRef.current = doSave; }, [doSave]);

  const update = useCallback((mutator) => {
    const prev = dataRef.current;
    if (!prev) return;
    const next = JSON.parse(JSON.stringify(prev));
    mutator(next);
    if (!next.meta) next.meta = {};
    next.meta.updatedAt = Date.now();
    next.meta.version = DATA_VERSION;
    dataRef.current = next;
    revRef.current += 1;
    dirtyRef.current = true;
    setData(next);
    schedule();
  }, [schedule]);

  /* Initial load. If storage cannot be read, the app runs read-only rather
     than risking a write of defaults over real data. */
  useEffect(() => {
    let cancelled = false;
    (async () => {
      let raw = null, reachable = false;
      try {
        const r = await fetch("/api/data");
        if (!r.ok) throw new Error("HTTP " + r.status);
        const j = await r.json();
        reachable = true;
        raw = j && typeof j.value === "string" ? j.value : null;
      } catch (e) {
        reachable = false;
      }
      if (cancelled) return;

      if (!reachable) {
        setData(migrate(null));
        setStatus({ kind: "err", text: "Can't reach storage, nothing will be saved" });
        return;
      }
      let parsed = null;
      if (raw) {
        try { parsed = JSON.parse(raw); }
        catch (e) {
          setData(migrate(null));
          setStatus({ kind: "err", text: "Stored data is unreadable, saving is off" });
          return;
        }
      }

      storageOkRef.current = true;
      const d = migrate(parsed);
      let changed = !raw;
      const mon = thisMonday();
      if (!d.snapshots.some((s) => s.weekOf === mon)) {
        d.snapshots.push(makeSnapshot(d, mon, true));
        changed = true;
      }
      if (d.snapshots.length > MAX_SNAPSHOTS) {
        d.snapshots = d.snapshots.slice()
          .sort((a, b) => String(a.weekOf).localeCompare(String(b.weekOf)) || (a.takenAt || 0) - (b.takenAt || 0))
          .slice(-MAX_SNAPSHOTS);
        changed = true;
      }
      dataRef.current = d;
      setData(d);
      lastRawRef.current = raw || "";
      if (changed) {
        revRef.current += 1;
        dirtyRef.current = true;
        schedule();
        setStatus({ kind: "ok", text: raw ? "Captured this week's baseline" : "Started a new dataset" });
      } else {
        setStatus({ kind: "ok", text: "Loaded" });
      }
    })();
    return () => { cancelled = true; };
  }, [schedule]);

  /* Background sync so two people in the app stay in step. */
  useEffect(() => {
    const t = setInterval(async () => {
      if (!storageOkRef.current) return;
      if (dirtyRef.current || savingRef.current || editingRef.current > 0) return;
      try {
        const r = await fetch("/api/data");
        if (!r.ok) return;
        const j = await r.json();
        const raw = j && typeof j.value === "string" ? j.value : null;
        if (!raw || raw === lastRawRef.current) return;
        const remote = migrate(JSON.parse(raw));
        lastRawRef.current = raw;
        if (JSON.stringify(remote) === JSON.stringify(dataRef.current)) return;
        dataRef.current = remote;
        setData(remote);
        setStatus({ kind: "ok", text: "Synced " + clockTime(Date.now()) });
      } catch (e) { /* transient; the next tick retries */ }
    }, POLL_MS);
    return () => clearInterval(t);
  }, []);

  /* Last-gasp save if the tab closes mid-edit. */
  useEffect(() => {
    const onLeave = () => {
      if (!dirtyRef.current || !storageOkRef.current || !dataRef.current) return;
      try {
        fetch("/api/data", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ value: JSON.stringify(dataRef.current) }),
          keepalive: true
        });
      } catch (e) { /* nothing else to try */ }
    };
    window.addEventListener("beforeunload", onLeave);
    return () => window.removeEventListener("beforeunload", onLeave);
  }, []);

  const monday = thisMonday();

  const actions = useMemo(() => ({
    setCell(repId, stageId, field, value) {
      update((d) => {
        if (!d.current[repId]) d.current[repId] = { stages: {}, note: "" };
        if (!d.current[repId].stages[stageId]) d.current[repId].stages[stageId] = { gpv: 0, avgDays: 0 };
        d.current[repId].stages[stageId][field] = value;
      });
    },
    setNote(repId, text) {
      update((d) => {
        if (!d.current[repId]) d.current[repId] = { stages: {}, note: "" };
        d.current[repId].note = text;
      });
    },
    addRep() {
      update((d) => {
        const id = uid("rep");
        d.config.reps.push({ id, name: "New rep", active: true });
        d.current[id] = { stages: {}, note: "" };
      });
    },
    setRepName(id, v) { update((d) => { const r = d.config.reps.find((x) => x.id === id); if (r) r.name = v || r.name; }); },
    setRepActive(id, on) { update((d) => { const r = d.config.reps.find((x) => x.id === id); if (r) r.active = !!on; }); },
    removeRep(id) {
      const r = dataRef.current.config.reps.find((x) => x.id === id);
      if (!window.confirm("Remove " + (r ? r.name : "this rep") + "? Their numbers and commits go too. Unticking Active keeps the history.")) return;
      update((d) => {
        d.config.reps = d.config.reps.filter((x) => x.id !== id);
        delete d.current[id];
        delete d.targets[id];
        d.commits = d.commits.filter((c) => c.repId !== id);
      });
      setTab("master");
    },
    /* A rep works a stage by naming what leaves it, so the stage they are
       looking at is the source and the next stage is the default destination. */
    addCommitOutOf(repId, stageId) {
      update((d) => {
        const i = d.config.stages.findIndex((s) => s.id === stageId);
        const to = i >= 0 && i < d.config.stages.length - 1 ? d.config.stages[i + 1].id : "";
        d.commits.push({
          id: uid("cmt"), repId, name: "", gpv: 0, fromStage: stageId, toStage: to,
          weekOf: thisMonday(), status: "open", resolvedWeek: null, createdAt: Date.now()
        });
      });
    },
    setCommit(id, field, value) { update((d) => { const c = d.commits.find((x) => x.id === id); if (c) c[field] = value; }); },
    resolveCommit(id, st) { update((d) => { const c = d.commits.find((x) => x.id === id); if (c) { c.status = st; c.resolvedWeek = thisMonday(); } }); },
    reopenCommit(id) { update((d) => { const c = d.commits.find((x) => x.id === id); if (c) { c.status = "open"; c.resolvedWeek = null; } }); },
    deleteCommit(id) {
      const c = dataRef.current.commits.find((x) => x.id === id);
      if (!window.confirm("Delete " + (c && c.name ? c.name : "this commit") + "? Marking it missed keeps it on the record.")) return;
      update((d) => { d.commits = d.commits.filter((x) => x.id !== id); });
    },
    captureNow() {
      update((d) => { d.snapshots.push(makeSnapshot(d, thisMonday(), false)); });
      setStatus({ kind: "ok", text: "Snapshot captured" });
    },
    deleteSnapshot(id) {
      if (!window.confirm("Delete this capture? Week-over-week deltas that used it will change.")) return;
      update((d) => { d.snapshots = d.snapshots.filter((s) => s.id !== id); });
    },
    toggleMatrix() { setShowMatrix((v) => !v); },
    loadSample() {
      if (!window.confirm("Fill every rep with sample numbers? This replaces any GPV, commits and captures already entered.")) return;
      update((d) => { buildSample(d); });
      setStatus({ kind: "ok", text: "Sample numbers loaded" });
    },
    clearNumbers() {
      if (!window.confirm("Clear all GPV, days, commits and captures? Reps, stages, floors and targets stay.")) return;
      update((d) => {
        d.current = {};
        d.config.reps.forEach((r) => { d.current[r.id] = { stages: {}, note: "" }; });
        d.commits = [];
        d.snapshots = [];
      });
      setStatus({ kind: "ok", text: "Numbers cleared" });
    },
    copyBackup() {
      const text = JSON.stringify(dataRef.current, null, 2);
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(text)
          .then(() => setStatus({ kind: "ok", text: "Copied to clipboard" }))
          .catch(() => setStatus({ kind: "err", text: "Clipboard blocked by the browser" }));
      } else {
        setStatus({ kind: "err", text: "Clipboard not available here" });
      }
    }
  }), [update]);

  if (!data) {
    return <div className="app"><Styles /><div style={{ padding: "64px 24px", color: "#6B7793" }}>{status.text}</div></div>;
  }

  const stages = data.config.stages;
  const reps = activeRepsOf(data);
  const ids = reps.map((r) => r.id);
  const baseline = pickBaseline(data.snapshots, monday);
  const stageName = (id) => {
    const s = stages.find((x) => x.id === id);
    return s ? s.name : "\u2014";
  };
  const ctx = { data, stages, ids, monday, baseline, actions, onEditing, setTab, showMatrix, stageName };
  const currentRep = data.config.reps.find((r) => r.id === tab);

  return (
    <div className="app">
      <Styles />
      <header className="head">
        <div className="head-top">
          <div className="brand">
            <h1>Cheeky Pipeline Review</h1>
            <span className="wk">
              Week of {shortDate(monday)}{baseline ? " \u00b7 baseline " + shortDate(baseline.weekOf) : ""}
            </span>
          </div>
          <div className="head-right">
            <span className="pill">{status.text}</span>
            <button className="btn" onClick={actions.captureNow}>Capture snapshot</button>
          </div>
        </div>
        <nav className="tabs">
          <button className={"tab" + (tab === "master" ? " on" : "")} onClick={() => setTab("master")}>Master</button>
          {reps.map((r) => (
            <button key={r.id} className={"tab" + (tab === r.id ? " on" : "")} onClick={() => setTab(r.id)}>{shortName(r.name)}</button>
          ))}
          <button className={"tab sep" + (tab === "settings" ? " on" : "")} onClick={() => setTab("settings")}>Settings</button>
        </nav>
      </header>
      <main>
        {tab === "master" ? <MasterView ctx={ctx} /> : null}
        {tab === "settings" ? <SettingsView ctx={ctx} /> : null}
        {currentRep ? <RepView key={currentRep.id} ctx={ctx} rep={currentRep} /> : null}
        {tab !== "master" && tab !== "settings" && !currentRep ? (
          <div className="section"><p className="empty">That tab no longer exists. Pick another above.</p></div>
        ) : null}
      </main>
    </div>
  );
}

/* ------------------------------------------------------------------ css */

function Styles() {
  return (
    <style>{`
@import url("https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700;800&display=swap");
:root{
  --ink:#1B2333; --ink-2:#414D66; --slate:#6B7793; --faint:#9AA5BC;
  --line:#E8ECF3; --paper:#F6F8FC; --card:#FFFFFF; --track:#EDF1F7;
  --good:#0FA47A; --good-bg:#E3F6EF; --good-bar:#3FC098;
  --warn:#E09B2D; --warn-bg:#FCF3E3; --warn-bar:#F0B84E;
  --bad:#EE5A5A;  --bad-bg:#FDECEC;  --bad-bar:#F58080;
  --accent:#5B6FE0; --accent-bg:#EDF0FE;
  --r:14px; --r-sm:9px;
  --shadow:0 1px 2px rgba(27,35,51,.04), 0 10px 28px -18px rgba(27,35,51,.28);
  --font:"Plus Jakarta Sans",-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;
}
*{box-sizing:border-box}
html,body{margin:0;padding:0}
body{background:var(--paper);color:var(--ink);font-family:var(--font);font-size:15px;line-height:1.5;
  -webkit-font-smoothing:antialiased;font-variant-numeric:tabular-nums}
.num,.st-fig,.hero-v,.mini-v,.fun-gpv{font-variant-numeric:tabular-nums;font-feature-settings:"tnum" 1}
.app{min-height:100vh}

/* ---------------- header ---------------- */
.head{position:sticky;top:0;z-index:30;background:rgba(246,248,252,.9);backdrop-filter:saturate(180%) blur(10px);
  border-bottom:1px solid var(--line)}
.head-top{display:flex;align-items:center;justify-content:space-between;gap:16px;max-width:1180px;margin:0 auto;padding:16px 24px 10px;flex-wrap:wrap}
.brand{display:flex;align-items:baseline;gap:12px}
.brand h1{margin:0;font-size:20px;font-weight:800;letter-spacing:-.03em}
.brand .wk{font-size:13px;color:var(--slate);font-weight:500}
.head-right{display:flex;align-items:center;gap:10px}
.pill{font-size:12px;color:var(--slate);white-space:nowrap;font-weight:500}

.tabs{display:flex;align-items:center;gap:6px;max-width:1180px;margin:0 auto;padding:2px 24px 10px;overflow-x:auto;scrollbar-width:thin}
.tab{appearance:none;background:none;border:0;border-radius:999px;padding:7px 15px;font:inherit;font-size:13.5px;font-weight:600;
  color:var(--slate);cursor:pointer;white-space:nowrap;transition:background .12s,color .12s}
.tab:hover{background:#EAEEF6;color:var(--ink)}
.tab.on{background:var(--ink);color:#fff}
.tab.sep{margin-left:auto}

main{max-width:1180px;margin:0 auto;padding:8px 24px 96px}
.section{background:var(--card);border-radius:var(--r);box-shadow:var(--shadow);padding:22px 24px;margin-top:18px}
.section-h{display:flex;align-items:baseline;gap:12px;margin:0 0 16px;flex-wrap:wrap}
.section-h h2{margin:0;font-size:16px;font-weight:700;letter-spacing:-.02em}
.section-h .hint{font-size:12.5px;color:var(--faint);font-weight:500}
.section-h .spacer{margin-left:auto}

/* ---------------- headline ---------------- */
.headline{background:var(--card);border-radius:var(--r);box-shadow:var(--shadow);padding:24px;margin-top:18px}
.headline-row{display:flex;align-items:center;gap:32px;flex-wrap:wrap}
.hero-k{font-size:13px;color:var(--slate);font-weight:600;margin-bottom:4px}
.hero-v{font-size:42px;line-height:1.05;letter-spacing:-.04em;font-weight:800}
.hero-s{font-size:14px;margin-top:8px;color:var(--ink-2);font-weight:500}
.hero-s .short{color:var(--bad);font-weight:700}
.hero-s .over{color:var(--good);font-weight:700}
.minis{display:flex;gap:14px;margin-left:auto;flex-wrap:wrap}
.mini{background:var(--paper);border-radius:var(--r-sm);padding:12px 16px;min-width:132px}
.mini-k{font-size:12px;color:var(--slate);font-weight:600}
.mini-v{font-size:22px;letter-spacing:-.025em;font-weight:700;margin-top:3px}
.mini-s{font-size:12px;color:var(--faint);margin-top:1px;font-weight:500}

/* the coverage gauge: the one big visual on the master tab */
.gauge{flex:none}
.gauge-arc{fill:none;stroke-linecap:round}
.gauge-bg{stroke:var(--track)}
.gauge-val.good{stroke:var(--good-bar)}
.gauge-val.warn{stroke:var(--warn-bar)}
.gauge-val.bad{stroke:var(--bad-bar)}
.gauge-pct{font-size:26px;font-weight:800;letter-spacing:-.03em;fill:var(--ink)}
.gauge-lab{font-size:11px;font-weight:600;fill:var(--faint)}

.track{position:relative;height:12px;background:var(--track);border-radius:999px;margin:20px 0 6px}
.track-fill{position:absolute;left:0;top:0;bottom:0;border-radius:999px;background:var(--good-bar)}
.track-fill.warn{background:var(--warn-bar)}
.track-fill.bad{background:var(--bad-bar)}
.track-tick{position:absolute;top:-4px;bottom:-4px;width:3px;border-radius:2px;background:var(--ink)}
.track-labels{display:flex;justify-content:space-between;font-size:12px;color:var(--faint);font-weight:600}

/* ---------------- focus list ---------------- */
.focus{display:flex;flex-direction:column;gap:8px}
.focus-row{display:grid;grid-template-columns:150px 1fr auto;gap:14px;align-items:center;
  padding:12px 14px;border-radius:var(--r-sm);font-size:14px;background:var(--paper)}
.focus-row.bad{background:var(--bad-bg)}
.focus-row.warn{background:var(--warn-bg)}
.focus-row.good{background:var(--good-bg)}
.focus-who{font-weight:700;display:flex;align-items:center;gap:9px;font-size:13.5px}
.focus-who .pip{width:9px;height:9px;border-radius:50%;flex:none}
.focus-row.bad .pip{background:var(--bad)}
.focus-row.warn .pip{background:var(--warn)}
.focus-row.good .pip{background:var(--good)}
.focus-txt{color:var(--ink-2)}
.focus-txt em{font-style:normal;font-weight:800;color:var(--ink)}
.focus-row.bad .focus-txt em{color:var(--bad)}
.all-clear{padding:16px;background:var(--good-bg);border-radius:var(--r-sm);color:var(--good);font-weight:600}

/* ---------------- master funnel ---------------- */
.fun-head{display:grid;grid-template-columns:170px 1fr 116px 116px 118px;gap:16px;padding:0 0 10px;
  font-size:11.5px;color:var(--faint);font-weight:700;border-bottom:1px solid var(--line)}
.fun-row{display:grid;grid-template-columns:170px 1fr 116px 116px 118px;gap:16px;align-items:center;
  padding:15px 0;border-bottom:1px solid var(--line)}
.fun-row:last-of-type{border-bottom:0}
.fun-name{font-size:14.5px;font-weight:650;display:flex;align-items:center;gap:10px}
.idx{display:inline-flex;align-items:center;justify-content:center;width:22px;height:22px;border-radius:50%;
  background:var(--paper);color:var(--slate);font-size:11.5px;font-weight:700;flex:none}
.fun-bar{position:relative;height:14px;background:var(--track);border-radius:999px}
.fun-fill{position:absolute;left:0;top:0;bottom:0;border-radius:999px;background:var(--good-bar)}
.fun-fill.warn{background:var(--warn-bar)}
.fun-fill.bad{background:var(--bad-bar)}
.fun-tick{position:absolute;top:-4px;bottom:-4px;width:3px;border-radius:2px;background:var(--ink)}
.fun-gpv{text-align:right;font-size:16px;font-weight:700;letter-spacing:-.02em}
.fun-gap{text-align:right;font-size:13px;font-weight:600;color:var(--slate)}
.fun-days{text-align:right;font-size:14px;font-weight:600;color:var(--ink-2)}
.fun-foot{display:grid;grid-template-columns:170px 1fr 116px 116px 118px;gap:16px;padding:15px 0 0;
  border-top:2px solid var(--line);margin-top:4px}
.fun-foot .fun-gpv{font-size:17px;font-weight:800}

/* ---------------- state pills ---------------- */
.sp{display:inline-block;padding:4px 11px;border-radius:999px;font-size:12.5px;font-weight:700;white-space:nowrap}
.sp.good{background:var(--good-bg);color:var(--good)}
.sp.warn{background:var(--warn-bg);color:var(--warn)}
.sp.bad{background:var(--bad-bg);color:var(--bad)}
.sp.flat{background:var(--paper);color:var(--faint)}

/* ---------------- tables ---------------- */
.tbl{width:100%;border-collapse:collapse;font-size:14px}
.tbl th{font-size:11.5px;font-weight:700;color:var(--faint);text-align:left;padding:0 10px 10px;border-bottom:1px solid var(--line);white-space:nowrap}
.tbl td{padding:12px 10px;border-bottom:1px solid var(--line);vertical-align:middle}
.tbl tbody tr:last-child td{border-bottom:0}
.tbl tbody tr:hover{background:var(--paper)}
.tbl th:first-child,.tbl td:first-child{padding-left:0}
.tbl th:last-child,.tbl td:last-child{padding-right:0}
.tbl .r{text-align:right}
.tbl .nar{width:1%;white-space:nowrap}
.strong{font-weight:700}
.muted{color:var(--slate)}
.faint{color:var(--faint)}
.empty{padding:20px 0;color:var(--slate)}
.namecell{display:flex;flex-direction:column;gap:6px;min-width:190px}
.namecell .lnk{background:none;border:0;padding:0;font:inherit;font-size:14px;font-weight:650;color:var(--ink);cursor:pointer;text-align:left}
.namecell .lnk:hover{color:var(--accent)}
.repbar{height:8px;background:var(--track);border-radius:999px;position:relative;width:100%}
.repbar span{position:absolute;left:0;top:0;bottom:0;border-radius:999px;background:var(--good-bar)}
.repbar span.warn{background:var(--warn-bar)}
.repbar span.bad{background:var(--bad-bar)}
.repbar i{position:absolute;top:-3px;bottom:-3px;width:2px;background:var(--ink);border-radius:2px}

/* ---------------- deltas ---------------- */
.d{font-size:13px;font-weight:700;white-space:nowrap}
.d.up{color:var(--good)}
.d.down{color:var(--bad)}
.d.flat{color:var(--faint)}
.d .ar{font-size:11px;margin-right:2px}
.days-d{font-size:12.5px;font-weight:700;margin-left:7px;color:var(--slate)}
.days-d.good{color:var(--good)}
.days-d.bad{color:var(--bad)}

/* ---------------- inputs ---------------- */
.in{font:inherit;font-size:14px;font-weight:600;border:1.5px solid var(--line);background:var(--card);
  padding:8px 11px;border-radius:var(--r-sm);color:inherit;width:100%;transition:border-color .12s,box-shadow .12s}
.in:hover{border-color:#D5DCE8}
.in:focus{outline:none;border-color:var(--accent);box-shadow:0 0 0 4px var(--accent-bg)}
.in.num{text-align:right;width:108px}
.in.num.sm{width:78px}
.sel{font:inherit;font-size:13.5px;font-weight:600;border:1.5px solid var(--line);background:var(--card);
  padding:7px 9px;border-radius:var(--r-sm);color:inherit;cursor:pointer;min-width:136px}
.sel:focus{outline:none;border-color:var(--accent);box-shadow:0 0 0 4px var(--accent-bg)}
.note{width:100%;max-width:780px;min-height:92px;font:inherit;font-size:14px;line-height:1.6;padding:12px 14px;
  border:1.5px solid var(--line);border-radius:var(--r-sm);resize:vertical;background:var(--card)}
.note:focus{outline:none;border-color:var(--accent);box-shadow:0 0 0 4px var(--accent-bg)}

/* ---------------- buttons ---------------- */
.btn{font:inherit;font-size:13px;font-weight:650;padding:7px 14px;border:1.5px solid var(--line);
  background:var(--card);border-radius:999px;cursor:pointer;color:var(--ink-2);transition:all .12s}
.btn:hover{border-color:#CFD8E6;color:var(--ink)}
.btn:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
.btn:disabled{opacity:.35;cursor:default}
.btn.primary{background:var(--ink);border-color:var(--ink);color:#fff}
.btn.primary:hover{background:#2A3348;border-color:#2A3348;color:#fff}
.btn.ok{color:var(--good);border-color:#CDEDE1}
.btn.ok:hover{background:var(--good-bg);border-color:var(--good)}
.btn.no{color:var(--bad);border-color:#F9D3D3}
.btn.no:hover{background:var(--bad-bg);border-color:var(--bad)}
.btn.x{border-color:transparent;color:var(--faint);padding:7px 9px}
.btn.x:hover{background:var(--paper);color:var(--ink)}
.btn.txt{border:0;background:none;padding:4px 2px;color:var(--accent);font-weight:700}
.btn.txt:hover{color:#3B4FC0;text-decoration:underline;text-underline-offset:3px}
.acts{display:flex;gap:7px;justify-content:flex-end}
.row-acts{display:flex;align-items:center;gap:14px;margin-top:16px;flex-wrap:wrap}

/* ---------------- tags ---------------- */
.tag{display:inline-block;font-size:11px;font-weight:700;padding:2px 9px;border-radius:999px;
  background:var(--paper);color:var(--slate);margin-left:8px;white-space:nowrap}
.tag.carried{background:var(--warn-bg);color:var(--warn)}
.tag.moved{background:var(--good-bg);color:var(--good)}
.tag.missed{background:var(--bad-bg);color:var(--bad)}
.mv{font-size:13px;color:var(--slate);font-weight:500}
.mv b{font-weight:700;color:var(--ink-2)}
.flow-amt{text-align:right;font-weight:700}
.spark{display:block;overflow:visible}
.spark-line{fill:none;stroke:var(--faint);stroke-width:2;stroke-linejoin:round;stroke-linecap:round}
.spark-line.bad{stroke:var(--bad-bar)}
.spark-line.good{stroke:var(--good-bar)}

.preview-note{margin:16px 0 0;padding:11px 16px;background:var(--accent-bg);border-radius:var(--r-sm);
  font-size:13px;color:#4457B8;font-weight:600}
.matrix-wrap{overflow-x:auto}

/* ---------------- stage walk ---------------- */
.walk{display:flex;flex-direction:column;gap:8px}
.st{border:1.5px solid var(--line);border-radius:var(--r-sm);overflow:hidden;transition:border-color .12s}
.st:hover{border-color:#D9E1EC}
.st.open{border-color:#D0D9E8;background:var(--card)}
.st.tone-bad{border-left:4px solid var(--bad-bar)}
.st.tone-warn{border-left:4px solid var(--warn-bar)}
.st.tone-good{border-left:4px solid var(--good-bar)}
.st-row{display:grid;grid-template-columns:1fr 170px 128px 132px;gap:18px;align-items:center;
  padding:15px 18px;cursor:pointer;background:none;border:0;width:100%;text-align:left;font:inherit;color:inherit}
.st-row:hover{background:var(--paper)}
.st-row:focus-visible{outline:2px solid var(--accent);outline-offset:-3px}
.st-name{font-size:15px;font-weight:700;display:flex;align-items:center;gap:10px;letter-spacing:-.01em}
.st-chev{color:var(--faint);font-size:9px;transition:transform .15s}
.st.open .st-chev{transform:rotate(90deg)}
.st-bar{position:relative;height:14px;background:var(--track);border-radius:999px}
.st-fill{position:absolute;left:0;top:0;bottom:0;border-radius:999px;background:var(--good-bar)}
.st-fill.warn{background:var(--warn-bar)}
.st-fill.bad{background:var(--bad-bar)}
.st-pledge{position:absolute;top:0;bottom:0;background:repeating-linear-gradient(45deg,#BFE3D5,#BFE3D5 4px,transparent 4px,transparent 8px);border-radius:0 999px 999px 0}
.st-tick{position:absolute;top:-4px;bottom:-4px;width:3px;border-radius:2px;background:var(--ink)}
.st-fig{text-align:right;font-size:15px;font-weight:700;letter-spacing:-.02em}
.st-fig .of{color:var(--faint);font-size:13px;font-weight:600}
.st-sub{display:block;font-size:12.5px;color:var(--faint);margin-top:3px;font-weight:600;white-space:nowrap}
.st-state{text-align:right}
.st-body{padding:4px 18px 20px 18px;border-top:1px solid var(--line);background:var(--card)}
.st-lead{font-size:14.5px;color:var(--ink-2);margin:16px 0;max-width:660px;font-weight:500}
.st-lead em{font-style:normal;font-weight:800;color:var(--ink)}
.st-lead.short em{color:var(--bad)}
.st-lead.covered em{color:var(--good)}
.st-fields{display:flex;gap:22px;align-items:center;flex-wrap:wrap;margin-bottom:18px;
  background:var(--paper);border-radius:var(--r-sm);padding:14px 16px}
.st-f{display:flex;align-items:center;gap:9px}
.st-f label{font-size:12.5px;color:var(--slate);font-weight:600}
.calc{display:flex;flex-wrap:wrap;gap:6px;margin-top:10px;max-width:640px}
.calc-part{font-size:11.5px;font-weight:600;color:var(--slate);background:var(--paper);padding:3px 9px;border-radius:999px;white-space:nowrap}
.calc-part b{font-weight:800;color:var(--ink-2)}
.calc-total{font-size:11.5px;font-weight:800;color:var(--ink);background:var(--accent-bg);padding:3px 10px;border-radius:999px;white-space:nowrap}
.st-risk{font-size:13px;color:var(--warn);background:var(--warn-bg);padding:9px 13px;border-radius:var(--r-sm);margin:0 0 16px;max-width:660px;font-weight:500}
.st-risk b{font-weight:800}
.st-risk-dot{display:inline-block;width:7px;height:7px;border-radius:50%;background:var(--warn);margin-left:7px;vertical-align:middle}
.trend{display:inline-flex;gap:5px;flex-wrap:wrap;align-items:center}
.tchip{font-size:11.5px;font-weight:700;padding:2px 7px;border-radius:999px;background:var(--paper);color:var(--slate);white-space:nowrap}
.tchip b{font-weight:800;opacity:.55;margin-right:1px}
.tchip.good{background:var(--good-bg);color:var(--good)}
.tchip.bad{background:var(--bad-bg);color:var(--bad)}
.tchip.flat{background:var(--paper);color:var(--faint)}
.fixed{font-size:14px;font-weight:700;color:var(--ink);white-space:nowrap}
.tgt{background:none;border:0;border-bottom:2px dashed #D3DBE8;padding:3px 2px;font:inherit;font-size:14px;
  font-weight:700;color:var(--slate);cursor:text;width:84px;text-align:right}
.tgt:hover{border-bottom-color:var(--slate);color:var(--ink)}
.tgt:focus{outline:none;border-bottom-color:var(--accent);color:var(--ink)}

.cmt{display:grid;grid-template-columns:1fr 140px 108px auto;gap:12px;align-items:center;padding:9px 0;border-bottom:1px solid var(--line)}
.cmt:last-of-type{border-bottom:0}
.cmt-lbl{font-size:12px;color:var(--faint);font-weight:700;margin:16px 0 4px}
.cmt-none{font-size:13px;color:var(--faint);padding:8px 0;font-weight:500}
.cmt-src{font-size:12.5px;color:var(--slate);font-weight:600}

@media (max-width:900px){
  .fun-head,.fun-row,.fun-foot{grid-template-columns:130px 1fr 100px 104px;gap:12px}
  .fun-days{display:none}
  .minis{margin-left:0}
  .hero-v{font-size:34px}
}
@media (max-width:760px){
  main{padding:8px 14px 72px}
  .head-top,.tabs{padding-left:14px;padding-right:14px}
  .section,.headline{padding:18px 16px}
  .st-row{grid-template-columns:1fr 118px;gap:10px}
  .st-bar,.st-state{display:none}
  .cmt{grid-template-columns:1fr 96px;gap:9px}
  .focus-row{grid-template-columns:1fr auto;gap:8px}
  .focus-who{grid-column:1/-1}
  .fun-head,.fun-row,.fun-foot{grid-template-columns:1fr 96px 100px}
  .fun-bar{display:none}
  .tbl{min-width:540px}
}
@media (prefers-reduced-motion:reduce){*{transition:none!important;animation:none!important}}

`}</style>
  );
}
