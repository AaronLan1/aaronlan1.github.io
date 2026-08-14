'use strict';

/* ============================================================
 * 静电场模拟 — 核心逻辑
 * 点电荷电场线 / 等势面 / φ-x · E-x · Ep-x 图像
 * ============================================================ */

// ---------- 常量 ----------
const K = 8.9875517923e9;      // N·m²/C²
const UC = 1e-6;               // μC → C
const TAU = Math.PI * 2;
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const lerp = (a, b, t) => a + (b - a) * t;

// ---------- 全局状态 ----------
const state = {
  charges: [],
  seq: 0,
  selId: null,
  view: { cx: 0, cy: 0, scale: 110 },   // scale: px / m
  showField: true,
  showEqui: true,
  showGrid: true,
  lockX: false,
  field: { density: 24, width: 1.7, color: '#43536e', dashed: false, arrows: true },
  equi: { levels: 14, opacity: 0.5, color: '#6f8fc4' },
  plot: { q0: 1, yLine: 0, tab: 'phi' },
  fieldLines: [],
  equiPaths: [],
};

// ---------- DOM ----------
const $ = id => document.getElementById(id);
const canvas = $('field');
const ctx = canvas.getContext('2d');
const staticCanvas = document.createElement('canvas');
const sctx = staticCanvas.getContext('2d');
const plotCanvas = $('plotCanvas');
const plotCtx = plotCanvas.getContext('2d');
const plotWindow = $('plotWindow');
const plotBody = $('plotBody');
const plotHead = $('plotHead');
const plotResize = $('plotResize');
const plotPlaceholder = $('plotPlaceholder');

let W = 0, H = 0, DPR = 1;

// ---------- 工具 ----------
function fmt(v) {
  if (!Number.isFinite(v)) return '—';
  const s = Math.abs(v) >= 100 ? v.toFixed(0) : v.toFixed(2);
  return parseFloat(s).toString();
}
function fmtSI(v, d = 2) {
  if (!Number.isFinite(v)) return '—';
  if (v === 0) return '0';
  const neg = v < 0, a = Math.abs(v);
  const units = ['p', 'n', 'μ', 'm', '', 'k', 'M', 'G', 'T'];
  let e = Math.floor(Math.log10(a) / 3);
  e = clamp(e, -4, 4);
  return (neg ? '-' : '') + (a / Math.pow(10, e * 3)).toFixed(d) + units[e + 4];
}
const debounce = (fn, ms) => { let t; return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); }; };
const easeOutBack = t => { const c1 = 1.70158, c3 = c1 + 1; return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2); };

// ---------- 视图变换 ----------
const w2s = (wx, wy) => [(wx - state.view.cx) * state.view.scale + W / 2, (wy - state.view.cy) * state.view.scale + H / 2];
const s2w = (px, py) => ({ x: state.view.cx + (px - W / 2) / state.view.scale, y: state.view.cy + (py - H / 2) / state.view.scale });
function viewBounds(m = 0) {
  const w = W / state.view.scale, h = H / state.view.scale;
  return {
    x0: state.view.cx - w / 2 - w * m, x1: state.view.cx + w / 2 + w * m,
    y0: state.view.cy - h / 2 - h * m, y1: state.view.cy + h / 2 + h * m,
    w, h,
  };
}

// ---------- 电荷管理 ----------
const chargeColor = c => (c.q >= 0 ? '#d97b6c' : '#5e8fc4');
const chargeLight = c => (c.q >= 0 ? '#f2b3a7' : '#a3c3e4');
const chargeRadiusPx = c => clamp(11 + 6.5 * Math.sqrt(Math.abs(c.q)), 11, 26);

function addCharge(x, y, q, silent) {
  const c = { id: 'c' + (++state.seq), x, y, q, born: silent ? -1e9 : performance.now() };
  state.charges.push(c);
  state.selId = c.id;
  renderChargeList();
  scheduleRecompute(true);
  return c;
}
function removeCharge(id) {
  state.charges = state.charges.filter(c => c.id !== id);
  if (state.selId === id) state.selId = null;
  renderChargeList();
  scheduleRecompute(true);
}
function moveCharge(id, x, y) {
  const c = state.charges.find(c => c.id === id);
  if (c) { c.x = x; c.y = y; }
}
function setChargeQ(id, q) {
  const c = state.charges.find(c => c.id === id);
  if (c) { c.q = q; scheduleRecompute(true); }
}

// ---------- 物理 ----------
function E(x, y) {
  let ex = 0, ey = 0;
  for (const c of state.charges) {
    const dx = x - c.x, dy = y - c.y;
    const r2 = dx * dx + dy * dy + 1e-9;
    const r = Math.sqrt(r2);
    const f = K * c.q * UC / (r2 * r);
    ex += f * dx; ey += f * dy;
  }
  return { ex, ey };
}
function phiAt(x, y) {
  let v = 0;
  for (const c of state.charges) v += K * c.q * UC / (Math.hypot(x - c.x, y - c.y) + 1e-9);
  return v;
}
const ExAt = (x, y) => E(x, y).ex;

// ---------- 电场线追踪 ----------
function unitE(x, y) {
  const e = E(x, y);
  const m = Math.hypot(e.ex, e.ey) + 1e-12;
  return { ex: e.ex / m, ey: e.ey / m };
}
function traceLine(x0, y0, h, stepMax, bounds, skipId, stopR) {
  const pts = [{ x: x0, y: y0 }];
  let px = x0, py = y0;
  for (let s = 0; s < stepMax; s++) {
    const k1 = unitE(px, py);
    const k2 = unitE(px + k1.ex * h * 0.5, py + k1.ey * h * 0.5);
    const k3 = unitE(px + k2.ex * h * 0.5, py + k2.ey * h * 0.5);
    const k4 = unitE(px + k3.ex * h, py + k3.ey * h);
    px += h / 6 * (k1.ex + 2 * k2.ex + 2 * k3.ex + k4.ex);
    py += h / 6 * (k1.ey + 2 * k2.ey + 2 * k3.ey + k4.ey);
    pts.push({ x: px, y: py });
    let hit = false;
    for (const c of state.charges) {
      if (c.id === skipId) continue;
      if (Math.hypot(px - c.x, py - c.y) < chargeRadiusPx(c) / state.view.scale * 1.15 + stopR) { hit = true; break; }
    }
    if (hit) break;
    if (px < bounds.x0 || px > bounds.x1 || py < bounds.y0 || py > bounds.y1) break;
  }
  return pts;
}
function computeFieldLines() {
  const lines = [];
  if (!state.charges.length) return lines;
  const b = viewBounds(0.2);
  const h = clamp(Math.min(b.w, b.h) / 450, 0.02, 0.5);
  const stepMax = 6000;
  const pos = state.charges.filter(c => c.q > 0);
  const n = Math.max(4, state.field.density);

  if (pos.length) {
    for (const c of pos) {
      const r0 = chargeRadiusPx(c) / state.view.scale + h * 2;
      for (let i = 0; i < n; i++) {
        const a = i / n * TAU;
        const pts = traceLine(c.x + r0 * Math.cos(a), c.y + r0 * Math.sin(a), h, stepMax, b, c.id, 0.02);
        if (pts.length > 2) lines.push(pts);
      }
    }
  } else if (state.charges.some(c => c.q < 0)) {
    // 无正电荷：电场线从视口边界进入
    const per = Math.max(3, Math.round(n / 4));
    for (let i = 0; i < per; i++) {
      const t = (i + 0.5) / per;
      const seeds = [
        { x: b.x0 + (b.x1 - b.x0) * t, y: b.y0 },
        { x: b.x0 + (b.x1 - b.x0) * t, y: b.y1 },
        { x: b.x0, y: b.y0 + (b.y1 - b.y0) * t },
        { x: b.x1, y: b.y0 + (b.y1 - b.y0) * t },
      ];
      for (const s of seeds) {
        const pts = traceLine(s.x, s.y, h, stepMax, b, null, 0.02);
        if (pts.length > 2) lines.push(pts);
      }
    }
  }
  return lines;
}

// ---------- 等势线（Marching Squares） ----------
const EQ_CASES = [
  [], [0, 3], [0, 1], [1, 3], [1, 2], [0, 3, 1, 2], [0, 2], [2, 3],
  [2, 3], [0, 2], [0, 1, 2, 3], [1, 2], [1, 3], [0, 1], [0, 3], [],
];
const EQ_EDGES = [[0, 1], [1, 2], [2, 3], [3, 0]];
function edgePt(ei, vx, vy, vv, iso) {
  const [a, b] = EQ_EDGES[ei];
  const va = vv[a], vb = vv[b];
  const t = vb === va ? 0.5 : (iso - va) / (vb - va);
  return { x: lerp(vx[a], vx[b], t), y: lerp(vy[a], vy[b], t) };
}
function isoValues(vmin, vmax, n) {
  const out = [];
  const sides = [];
  if (vmin < 0) sides.push([vmin, Math.min(0, vmax), -1]);
  if (vmax > 0) sides.push([Math.max(0, vmin), vmax, 1]);
  if (!sides.length) return out;
  const per = Math.max(2, Math.round(n / sides.length));
  for (const [a, b, sgn] of sides) {
    let lo = Math.log10(Math.abs(a)), hi = Math.log10(Math.abs(b));
    if (!Number.isFinite(lo)) lo = hi - 5;
    if (!Number.isFinite(hi)) hi = lo + 5;
    for (let i = 0; i < per; i++) {
      const v = sgn * Math.pow(10, lo + (hi - lo) * (i / per));
      if (Number.isFinite(v) && Math.abs(v) > 1e-12) out.push(v);
    }
  }
  return out;
}
function computeEquipotentials() {
  if (!state.charges.length) return [];
  const b = viewBounds(0.1);
  const cell = Math.max(b.w, b.h) / 150;
  const nx = Math.ceil(b.w / cell), ny = Math.ceil(b.h / cell);
  const Wd = nx + 1;
  const vals = new Float64Array(Wd * (ny + 1));
  let vmin = Infinity, vmax = -Infinity;
  for (let j = 0; j <= ny; j++) {
    for (let i = 0; i <= nx; i++) {
      const v = phiAt(b.x0 + i * cell, b.y0 + j * cell);
      vals[j * Wd + i] = v;
      if (v < vmin) vmin = v;
      if (v > vmax) vmax = v;
    }
  }
  if (!Number.isFinite(vmin) || !Number.isFinite(vmax)) return [];
  const isos = isoValues(vmin, vmax, state.equi.levels);
  const out = [];
  for (const iso of isos) {
    const segs = [];
    for (let j = 0; j < ny; j++) {
      for (let i = 0; i < nx; i++) {
        const v0 = vals[j * Wd + i], v1 = vals[j * Wd + i + 1],
              v2 = vals[(j + 1) * Wd + i + 1], v3 = vals[(j + 1) * Wd + i];
        let mask = 0;
        if (v0 < iso) mask |= 1;
        if (v1 < iso) mask |= 2;
        if (v2 < iso) mask |= 4;
        if (v3 < iso) mask |= 8;
        if (!mask || mask === 15) continue;
        const cs = EQ_CASES[mask];
        const sx = b.x0 + i * cell, sy = b.y0 + j * cell;
        const vx = [sx, sx + cell, sx + cell, sx];
        const vy = [sy, sy, sy + cell, sy + cell];
        const vv = [v0, v1, v2, v3];
        for (let e = 0; e < cs.length; e += 2) {
          segs.push({ a: edgePt(cs[e], vx, vy, vv, iso), b: edgePt(cs[e + 1], vx, vy, vv, iso) });
        }
      }
    }
    if (segs.length) out.push({ iso, polylines: assemblePolylines(segs) });
  }
  return out;
}

// 将 marching squares 无序线段按端点连通性组装为折线
function assemblePolylines(segs) {
  const n = segs.length;
  const keyOf = p => p.x.toFixed(4) + ',' + p.y.toFixed(4);
  const idx = new Map();
  for (let i = 0; i < n; i++) {
    const s = segs[i];
    for (const e of [s.a, s.b]) {
      const k = keyOf(e);
      if (!idx.has(k)) idx.set(k, []);
      idx.get(k).push(i);
    }
  }
  const used = new Uint8Array(n);
  const polylines = [];
  const takeAt = k => {
    const list = idx.get(k);
    if (!list) return null;
    for (const i of list) {
      if (used[i]) continue;
      used[i] = 1;
      const s = segs[i];
      return keyOf(s.a) === k ? s.b : s.a;
    }
    return null;
  };
  for (let start = 0; start < n; start++) {
    if (used[start]) continue;
    used[start] = 1;
    const s = segs[start];
    const line = [s.a, s.b];
    for (;;) {
      const nx = takeAt(keyOf(line[line.length - 1]));
      if (!nx) break;
      line.push(nx);
    }
    for (;;) {
      const nx = takeAt(keyOf(line[0]));
      if (!nx) break;
      line.unshift(nx);
    }
    polylines.push(line);
  }
  return polylines;
}

// Chaikin 折线平滑（一次迭代切角），消除 marching squares 的直线感
function chaikinSmooth(pts) {
  if (pts.length < 3) return pts;
  const closed = Math.hypot(pts[0].x - pts[pts.length - 1].x, pts[0].y - pts[pts.length - 1].y) < 1e-6;
  if (!closed) {
    const out = [pts[0]];
    for (let i = 0; i < pts.length - 1; i++) {
      const p0 = pts[i], p1 = pts[i + 1];
      out.push({ x: p0.x * 0.75 + p1.x * 0.25, y: p0.y * 0.75 + p1.y * 0.25 });
      out.push({ x: p0.x * 0.25 + p1.x * 0.75, y: p0.y * 0.25 + p1.y * 0.75 });
    }
    out.push(pts[pts.length - 1]);
    return out;
  }
  const core = pts.slice(0, -1);
  const m = core.length;
  const out = [];
  for (let i = 0; i < m; i++) {
    const p0 = core[i], p1 = core[(i + 1) % m];
    out.push({ x: p0.x * 0.75 + p1.x * 0.25, y: p0.y * 0.75 + p1.y * 0.25 });
    out.push({ x: p0.x * 0.25 + p1.x * 0.75, y: p0.y * 0.25 + p1.y * 0.75 });
  }
  out.push(out[0]);
  return out;
}

// ---------- 静态层渲染 ----------
function niceStep(target) {
  const mag = Math.pow(10, Math.floor(Math.log10(target)));
  const norm = target / mag;
  const f = norm < 1.5 ? 1 : norm < 3.5 ? 2 : norm < 7.5 ? 5 : 10;
  return f * mag;
}
function drawGrid(c) {
  if (!state.showGrid) return;
  const b = viewBounds(0);
  const step = niceStep(90 / state.view.scale);
  const minor = step / 5;
  c.lineWidth = 1;
  // 细网格
  c.strokeStyle = '#f1f3f7';
  c.beginPath();
  for (let x = Math.ceil(b.x0 / minor) * minor; x <= b.x1; x += minor) {
    const [sx] = w2s(x, 0); c.moveTo(sx, 0); c.lineTo(sx, H);
  }
  for (let y = Math.ceil(b.y0 / minor) * minor; y <= b.y1; y += minor) {
    const [, sy] = w2s(0, y); c.moveTo(0, sy); c.lineTo(W, sy);
  }
  c.stroke();
  // 主网格
  c.strokeStyle = '#dde2ea';
  c.beginPath();
  for (let x = Math.ceil(b.x0 / step) * step; x <= b.x1; x += step) {
    const [sx] = w2s(x, 0); c.moveTo(sx, 0); c.lineTo(sx, H);
  }
  for (let y = Math.ceil(b.y0 / step) * step; y <= b.y1; y += step) {
    const [, sy] = w2s(0, y); c.moveTo(0, sy); c.lineTo(W, sy);
  }
  c.stroke();
  // 坐标轴（若在视口内）：深色轴线 + 方向箭头 + 轴名
  const x0s = w2s(0, 0);
  const axisColor = '#6f7c90';
  const hasYAxis = x0s[0] >= 0 && x0s[0] <= W;
  const hasXAxis = x0s[1] >= 0 && x0s[1] <= H;
  c.strokeStyle = axisColor;
  c.lineWidth = 1.9;
  if (hasYAxis) { c.beginPath(); c.moveTo(x0s[0], 0); c.lineTo(x0s[0], H); c.stroke(); }
  if (hasXAxis) { c.beginPath(); c.moveTo(0, x0s[1]); c.lineTo(W, x0s[1]); c.stroke(); }
  c.lineWidth = 1;
  c.fillStyle = axisColor;
  c.font = '600 13px "Segoe UI", "PingFang SC", "Microsoft YaHei", sans-serif';
  if (hasXAxis) {
    // x 轴正方向箭头（视口右缘）
    const ay = x0s[1];
    c.beginPath(); c.moveTo(W - 10, ay - 5.5); c.lineTo(W - 1, ay); c.lineTo(W - 10, ay + 5.5); c.closePath(); c.fill();
    c.textAlign = 'left'; c.textBaseline = 'middle';
    c.fillText('x', W - 18, ay);
  }
  if (hasYAxis) {
    // y 轴正方向箭头（视口上缘）
    const ax = x0s[0];
    c.beginPath(); c.moveTo(ax - 5.5, 10); c.lineTo(ax, 1); c.lineTo(ax + 5.5, 10); c.closePath(); c.fill();
    c.textAlign = 'center'; c.textBaseline = 'bottom';
    c.fillText('y', ax, 12);
  }
  // 刻度标签
  c.fillStyle = '#6e7889';
  c.font = '600 11px "Segoe UI", "PingFang SC", "Microsoft YaHei", sans-serif';
  c.textBaseline = 'top';
  c.textAlign = 'center';
  for (let x = Math.ceil(b.x0 / step) * step; x <= b.x1; x += step) {
    if (Math.abs(x) < step * 1e-6) continue;
    const [sx] = w2s(x, 0);
    if (sx < 30 || sx > W - 30) continue;
    c.fillText(fmtSI(x, 1), sx, H - 18);
  }
  c.textAlign = 'right';
  c.textBaseline = 'middle';
  for (let y = Math.ceil(b.y0 / step) * step; y <= b.y1; y += step) {
    if (Math.abs(y) < step * 1e-6) continue;
    const [, sy] = w2s(0, y);
    if (sy < 20 || sy > H - 20) continue;
    c.fillText(fmtSI(y, 1), 6, sy);
  }
  // 单位提示
  c.textAlign = 'left'; c.textBaseline = 'bottom';
  c.fillStyle = '#b3bccb';
  c.fillText('单位：m', 8, H - 4);
}

function drawEquipotentials(c) {
  if (!state.showEqui || !state.equiPaths.length) return;
  c.save();
  c.strokeStyle = state.equi.color;
  c.globalAlpha = state.equi.opacity;
  c.lineWidth = 1.2;
  c.lineJoin = 'round';
  c.lineCap = 'round';
  for (const { polylines } of state.equiPaths) {
    const p = new Path2D();
    for (const pl of polylines) {
      const smooth = chaikinSmooth(pl);
      for (let i = 0; i < smooth.length; i++) {
        const [sx, sy] = w2s(smooth[i].x, smooth[i].y);
        if (i === 0) p.moveTo(sx, sy);
        else p.lineTo(sx, sy);
      }
    }
    c.stroke(p);
  }
  c.restore();
}

function arrowPoints(pts, gap) {
  const out = [];
  let dist = 0, prev = pts[0];
  for (let i = 1; i < pts.length; i++) {
    const dx = pts[i].x - prev.x, dy = pts[i].y - prev.y;
    const d = Math.hypot(dx, dy);
    if (d < 1e-6) continue;
    let t = 0;
    while (t < 1) {
      const nd = dist + d * (1 - t);
      if (nd >= gap) {
        const tt = t + (gap - dist) / d;
        out.push({ x: prev.x + dx * tt, y: prev.y + dy * tt, a: Math.atan2(dy, dx) });
        dist = 0; t = tt;
      } else { dist = nd; break; }
    }
    prev = pts[i];
  }
  return out;
}
function drawFieldLines(c) {
  if (!state.showField || !state.fieldLines.length) return;
  c.save();
  c.strokeStyle = state.field.color;
  c.lineWidth = state.field.width;
  c.lineCap = 'round'; c.lineJoin = 'round';
  if (state.field.dashed) c.setLineDash([8, 6]);
  for (const ln of state.fieldLines) {
    c.beginPath();
    let first = true;
    for (const p of ln) {
      const [sx, sy] = w2s(p.x, p.y);
      if (first) { c.moveTo(sx, sy); first = false; } else c.lineTo(sx, sy);
    }
    c.stroke();
  }
  c.setLineDash([]);
  if (state.field.arrows) {
    c.fillStyle = state.field.color;
    for (const ln of state.fieldLines) {
      const sp = ln.map(p => { const [x, y] = w2s(p.x, p.y); return { x, y }; });
      for (const ar of arrowPoints(sp, 20)) {
        c.save();
        c.translate(ar.x, ar.y);
        c.rotate(ar.a);
        c.beginPath();
        c.moveTo(6.5, 0);
        c.lineTo(-3.8, 4.2);
        c.lineTo(-1.8, 0);
        c.lineTo(-3.8, -4.2);
        c.closePath();
        c.fill();
        c.restore();
      }
    }
  }
  c.restore();
}

function renderStatic() {
  sctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  sctx.clearRect(0, 0, W, H);
  sctx.fillStyle = '#fbfcfe';
  sctx.fillRect(0, 0, W, H);
  drawGrid(sctx);
  drawEquipotentials(sctx);
  drawFieldLines(sctx);
}

// ---------- 动态层渲染 ----------
function drawSamplingLine(c) {
  const y = state.plot.yLine;
  if (!Number.isFinite(y)) return;
  const [, sy] = w2s(0, y);
  if (sy < -10 || sy > H + 10) return;
  c.save();
  c.strokeStyle = 'rgba(90,108,156,.45)';
  c.setLineDash([9, 7]);
  c.lineWidth = 1.2;
  c.beginPath(); c.moveTo(0, sy); c.lineTo(W, sy); c.stroke();
  c.setLineDash([]);
  c.fillStyle = 'rgba(90,108,156,.85)';
  c.font = '11px "Segoe UI", "PingFang SC", "Microsoft YaHei", sans-serif';
  c.fillText('采样线 y = ' + fmt(y) + ' m', 10, sy - 8);
  c.restore();
}
function drawCharges(c, now) {
  for (const ch of state.charges) {
    const [sx, sy] = w2s(ch.x, ch.y);
    if (sx < -60 || sx > W + 60 || sy < -60 || sy > H + 60) continue;
    const r = chargeRadiusPx(ch);
    const t = ch.born < 0 ? 1 : clamp((now - ch.born) / 320, 0, 1);
    const sc = ch.born < 0 ? 1 : easeOutBack(t);
    const R = r * sc;
    const main = chargeColor(ch), light = chargeLight(ch);
    const sel = ch.id === state.selId;

    if (sel) {
      const pulse = 1 + 0.1 * Math.sin(now / 240);
      c.beginPath(); c.arc(sx, sy, R * pulse + 5, 0, TAU);
      c.strokeStyle = '#5a6c9c'; c.lineWidth = 1.6; c.stroke();
      const ring = (now / 900) % 1;
      c.beginPath(); c.arc(sx, sy, R + 12 + ring * 26, 0, TAU);
      c.strokeStyle = `rgba(90,108,156,${0.3 * (1 - ring)})`; c.lineWidth = 2; c.stroke();
    }
    // 光晕
    const glow = c.createRadialGradient(sx, sy, R * 0.4, sx, sy, R * 2.1);
    glow.addColorStop(0, sel ? 'rgba(90,108,156,.30)' : 'rgba(120,135,165,.16)');
    glow.addColorStop(1, 'rgba(255,255,255,0)');
    c.fillStyle = glow;
    c.beginPath(); c.arc(sx, sy, R * 2.1, 0, TAU); c.fill();
    // 球体
    const ball = c.createRadialGradient(sx - R * 0.35, sy - R * 0.42, R * 0.12, sx, sy, R);
    ball.addColorStop(0, '#ffffff');
    ball.addColorStop(0.32, light);
    ball.addColorStop(1, main);
    c.fillStyle = ball;
    c.beginPath(); c.arc(sx, sy, R, 0, TAU); c.fill();
    // 符号
    c.fillStyle = '#fff';
    c.font = `600 ${Math.round(R * 1.05)}px "Segoe UI", sans-serif`;
    c.textAlign = 'center'; c.textBaseline = 'middle';
    c.fillText(ch.q >= 0 ? '+' : '−', sx, sy + 1);
    // 数值标签
    c.font = '11px "Segoe UI", "PingFang SC", "Microsoft YaHei", sans-serif';
    c.fillStyle = 'rgba(60,68,84,.82)';
    c.fillText('q = ' + fmt(ch.q) + ' μC', sx, sy + R + 15);
  }
}
function renderDynamic(now) {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.clearRect(0, 0, W, H);
  ctx.drawImage(staticCanvas, 0, 0, W, H);
  drawSamplingLine(ctx);
  drawCharges(ctx, now);
  requestAnimationFrame(renderDynamic);
}

// ---------- 重算调度 ----------
let lastRecompute = 0, recomputeTimer = 0;
function recompute() {
  state.fieldLines = computeFieldLines();
  state.equiPaths = computeEquipotentials();
  renderStatic();
  drawPlot();
}
function scheduleRecompute(immediate) {
  const now = performance.now();
  if (immediate || now - lastRecompute > 50) {
    lastRecompute = now;
    recompute();
  } else if (!recomputeTimer) {
    recomputeTimer = setTimeout(() => {
      recomputeTimer = 0;
      lastRecompute = performance.now();
      recompute();
    }, 50 - (now - lastRecompute));
  }
}

// ============================================================
// 图像小窗口：φ-x / E-x / Ep-x
// ============================================================
const PLOT_COLORS = { phi: '#5a6c9c', ex: '#b07252', ep: '#5d8a6f' };
const PLOT_UNITS = { phi: 'φ / V', ex: 'Ex / (V·m⁻¹)', ep: 'Ep / J' };

function plotXRange() {
  const vMin = parseFloat($('plotXMin').value), vMax = parseFloat($('plotXMax').value);
  const b = viewBounds(0);
  const lo = Number.isFinite(vMin) ? vMin : b.x0;
  const hi = Number.isFinite(vMax) ? vMax : b.x1;
  return hi > lo ? { x0: lo, x1: hi } : { x0: b.x0, x1: b.x1 };
}
function computePlotData(tab) {
  const { x0, x1 } = plotXRange();
  const n = 460;
  const yLine = state.plot.yLine;
  const xs = [], ys = [];
  for (let i = 0; i < n; i++) {
    const x = x0 + (x1 - x0) * i / (n - 1);
    xs.push(x);
    let skip = false;
    for (const c of state.charges) if (Math.abs(x - c.x) < 0.07) { skip = true; break; }
    if (skip) { ys.push(NaN); continue; }
    if (tab === 'phi') ys.push(phiAt(x, yLine));
    else if (tab === 'ex') ys.push(ExAt(x, yLine));
    else ys.push(state.plot.q0 * UC * phiAt(x, yLine));
  }
  return { xs, ys, x0, x1, marks: state.charges.filter(c => c.x >= x0 && c.x <= x1) };
}
function drawPlot() {
  const rect = plotBody.getBoundingClientRect();
  const w = rect.width, h = rect.height;
  if (w < 10 || h < 10) return;
  const dpr = DPR;
  if (plotCanvas.width !== Math.round(w * dpr)) { plotCanvas.width = Math.round(w * dpr); plotCanvas.height = Math.round(h * dpr); }
  const c = plotCtx;
  c.setTransform(dpr, 0, 0, dpr, 0, 0);
  c.clearRect(0, 0, w, h);
  c.fillStyle = '#ffffff';
  c.fillRect(0, 0, w, h);
  const has = state.charges.length > 0;
  plotPlaceholder.classList.toggle('hidden', has);
  if (!has) return;

  const tab = state.plot.tab;
  const data = computePlotData(tab);
  const m = { l: 56, r: 16, t: 20, b: 30 };
  const pw = w - m.l - m.r, ph = h - m.t - m.b;

  // y 值域：2%–98% 分位 + 包含 0
  const finite = [];
  for (const v of data.ys) if (Number.isFinite(v)) finite.push(v);
  if (!finite.length) return;
  finite.sort((a, b) => a - b);
  let yMin = finite[Math.max(0, Math.floor(finite.length * 0.02))];
  let yMax = finite[Math.min(finite.length - 1, Math.floor(finite.length * 0.98))];
  yMin = Math.min(0, yMin); yMax = Math.max(0, yMax);
  if (yMax - yMin < 1e-9) { yMax += 1; yMin -= 1; }
  const pad = (yMax - yMin) * 0.08;
  yMin -= pad; yMax += pad;

  const X = x => m.l + (x - data.x0) / (data.x1 - data.x0) * pw;
  const Y = v => m.t + (1 - (clamp(v, yMin, yMax) - yMin) / (yMax - yMin)) * ph;

  // 水平网格 + y 标签
  c.font = '10px "Segoe UI", sans-serif';
  c.textAlign = 'right'; c.textBaseline = 'middle';
  const TICKS = 4;
  for (let i = 0; i <= TICKS; i++) {
    const v = yMin + (yMax - yMin) * i / TICKS;
    const yy = Y(v);
    c.strokeStyle = '#eef0f4'; c.lineWidth = 1;
    c.beginPath(); c.moveTo(m.l, yy); c.lineTo(w - m.r, yy); c.stroke();
    c.fillStyle = '#9aa4b5';
    c.fillText(fmtSI(v, 1), m.l - 7, yy);
  }
  // 垂直网格 + x 标签
  c.textAlign = 'center'; c.textBaseline = 'top';
  const XTICKS = 6;
  for (let i = 0; i <= XTICKS; i++) {
    const xv = data.x0 + (data.x1 - data.x0) * i / XTICKS;
    const xx = X(xv);
    c.strokeStyle = '#eef0f4';
    c.beginPath(); c.moveTo(xx, m.t); c.lineTo(xx, m.t + ph); c.stroke();
    c.fillStyle = '#9aa4b5';
    c.fillText(fmtSI(xv, 1), xx, m.t + ph + 8);
  }
  // 零线
  if (0 >= yMin && 0 <= yMax) {
    const yy = Y(0);
    c.strokeStyle = '#dde2ea'; c.lineWidth = 1.1;
    c.beginPath(); c.moveTo(m.l, yy); c.lineTo(w - m.r, yy); c.stroke();
  }
  // 边框
  c.strokeStyle = '#dfe4ec'; c.lineWidth = 1;
  c.strokeRect(m.l + 0.5, m.t + 0.5, pw - 1, ph - 1);

  // 曲线
  c.strokeStyle = PLOT_COLORS[tab];
  c.lineWidth = 2;
  c.lineJoin = 'round'; c.lineCap = 'round';
  c.beginPath();
  let started = false;
  for (let i = 0; i < data.ys.length; i++) {
    const v = data.ys[i];
    if (!Number.isFinite(v)) { started = false; continue; }
    const xx = X(data.xs[i]), yy = Y(v);
    if (!started) { c.moveTo(xx, yy); started = true; } else c.lineTo(xx, yy);
  }
  c.stroke();

  // 电荷位置标记
  for (const ch of data.marks) {
    const xx = X(ch.x);
    if (xx < m.l + 2 || xx > w - m.r - 2) continue;
    c.strokeStyle = 'rgba(122,132,150,.5)'; c.lineWidth = 1; c.setLineDash([4, 4]);
    c.beginPath(); c.moveTo(xx, m.t + 1); c.lineTo(xx, m.t + ph - 1); c.stroke();
    c.setLineDash([]);
    c.fillStyle = chargeColor(ch);
    c.beginPath(); c.arc(xx, m.t - 5, 4.5, 0, TAU); c.fill();
    c.fillStyle = '#fff';
    c.font = '600 10px "Segoe UI", sans-serif';
    c.textAlign = 'center'; c.textBaseline = 'middle';
    c.fillText(ch.q >= 0 ? '+' : '−', xx, m.t - 4.5);
  }

  // 图例与单位
  c.fillStyle = '#8b94a6';
  c.font = '11px "Segoe UI", "PingFang SC", "Microsoft YaHei", sans-serif';
  c.textAlign = 'left'; c.textBaseline = 'top';
  c.fillText(PLOT_UNITS[tab], m.l + 6, 4);
  c.textAlign = 'right'; c.textBaseline = 'bottom';
  c.fillText('x / m', w - m.r - 2, h - 4);
}

// ============================================================
// 交互
// ============================================================
const pointers = new Map();
let dragMode = null;      // 'charge' | 'pan'
let dragChargeId = null;
let pinchState = null;

function hitCharge(px, py) {
  let best = null, bd = Infinity;
  for (const c of state.charges) {
    const [sx, sy] = w2s(c.x, c.y);
    const d = Math.hypot(px - sx, py - sy);
    if (d < chargeRadiusPx(c) + 6 && d < bd) { bd = d; best = c; }
  }
  return best;
}

canvas.addEventListener('pointerdown', e => {
  if (e.button !== 0) return; // 仅响应左键 / 触摸
  canvas.setPointerCapture(e.pointerId);
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pointers.size === 1) {
    const c = hitCharge(e.clientX, e.clientY);
    if (c) {
      dragMode = 'charge';
      dragChargeId = c.id;
      state.selId = c.id;
      renderChargeList();
    } else {
      dragMode = 'pan';
      canvas.classList.add('panning');
    }
  } else if (pointers.size === 2) {
    dragMode = null;
    const [a, b] = [...pointers.values()];
    pinchState = {
      d: Math.hypot(a.x - b.x, a.y - b.y),
      mx: (a.x + b.x) / 2, my: (a.y + b.y) / 2,
      cx: state.view.cx, cy: state.view.cy, scale: state.view.scale,
      w1: a, w2: b,
    };
  }
});
canvas.addEventListener('pointermove', e => {
  if (!pointers.has(e.pointerId)) return;
  const prev = pointers.get(e.pointerId);
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pointers.size === 2 && pinchState) {
    const [a, b] = [...pointers.values()];
    const d = Math.hypot(a.x - b.x, a.y - b.y);
    const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
    const f = d / pinchState.d;
    const ns = clamp(pinchState.scale * f, 6, 900);
    // 保持 pinch 起始中心对应的世界点跟随当前中心
    const wx = pinchState.cx + (pinchState.mx - W / 2) / pinchState.scale;
    const wy = pinchState.cy + (pinchState.my - H / 2) / pinchState.scale;
    state.view.scale = ns;
    state.view.cx = wx - (mx - W / 2) / ns;
    state.view.cy = wy - (my - H / 2) / ns;
    scheduleRecompute();
    return;
  }
  if (dragMode === 'charge') {
    const w = s2w(e.clientX, e.clientY);
    const c = state.charges.find(c => c.id === dragChargeId);
    if (c) moveCharge(c.id, w.x, state.lockX ? c.y : w.y);
    scheduleRecompute();
  } else if (dragMode === 'pan') {
    // 用上一次记录的指针位置计算位移（prev 在本次更新之前）
    const dx = e.clientX - prev.x, dy = e.clientY - prev.y;
    state.view.cx -= dx / state.view.scale;
    state.view.cy -= dy / state.view.scale;
    scheduleRecompute();
  }
});
function endPointer(e) {
  pointers.delete(e.pointerId);
  if (pointers.size < 2) pinchState = null;
  if (pointers.size === 0) {
    dragMode = null;
    dragChargeId = null;
    canvas.classList.remove('panning');
  }
}
canvas.addEventListener('pointerup', endPointer);
canvas.addEventListener('pointercancel', endPointer);

canvas.addEventListener('wheel', e => {
  e.preventDefault();
  const f = Math.exp(-e.deltaY * 0.0014);
  const ns = clamp(state.view.scale * f, 6, 900);
  const px = e.clientX, py = e.clientY;
  const wx = state.view.cx + (px - W / 2) / state.view.scale;
  const wy = state.view.cy + (py - H / 2) / state.view.scale;
  state.view.cx = wx - (px - W / 2) / ns;
  state.view.cy = wy - (py - H / 2) / ns;
  state.view.scale = ns;
  scheduleRecompute();
}, { passive: false });

canvas.addEventListener('dblclick', e => {
  const w = s2w(e.clientX, e.clientY);
  addCharge(w.x, w.y, 2);
});

document.addEventListener('keydown', e => {
  if (e.target && typeof e.target.matches === 'function' && e.target.matches('input')) return;
  if ((e.key === 'Delete' || e.key === 'Backspace') && state.selId) {
    e.preventDefault();
    removeCharge(state.selId);
  } else if (e.key === 'Escape') {
    state.selId = null;
    renderChargeList();
  }
});

// ---------- 图像窗口拖动 / 缩放 / 开关 ----------
let winDrag = null, winResize = null;
plotHead.addEventListener('pointerdown', e => {
  if (e.target.closest('button')) return;
  winDrag = { sx: e.clientX, sy: e.clientY, l: plotWindow.offsetLeft, t: plotWindow.offsetTop };
  plotHead.setPointerCapture(e.pointerId);
});
plotHead.addEventListener('pointermove', e => {
  if (!winDrag) return;
  const l = clamp(winDrag.l + e.clientX - winDrag.sx, -plotWindow.offsetWidth + 80, innerWidth - 60);
  const t = clamp(winDrag.t + e.clientY - winDrag.sy, 0, innerHeight - 60);
  plotWindow.style.left = l + 'px';
  plotWindow.style.top = t + 'px';
});
plotHead.addEventListener('pointerup', () => { winDrag = null; });
plotHead.addEventListener('pointercancel', () => { winDrag = null; });

plotResize.addEventListener('pointerdown', e => {
  winResize = { sx: e.clientX, sy: e.clientY, w: plotWindow.offsetWidth, h: plotWindow.offsetHeight };
  plotResize.setPointerCapture(e.pointerId);
  e.stopPropagation();
});
plotResize.addEventListener('pointermove', e => {
  if (!winResize) return;
  const w = clamp(winResize.w + e.clientX - winResize.sx, 300, innerWidth - 40);
  const h = clamp(winResize.h + e.clientY - winResize.sy, 220, innerHeight - 60);
  plotWindow.style.width = w + 'px';
  plotWindow.style.height = h + 'px';
  drawPlot();
});
plotResize.addEventListener('pointerup', () => { winResize = null; });
plotResize.addEventListener('pointercancel', () => { winResize = null; });

function showPlotWindow(show) {
  plotWindow.classList.toggle('hidden', !show);
  $('plotRestore').classList.toggle('hidden', show);
  if (show) drawPlot();
}
$('plotMin').addEventListener('click', () => showPlotWindow(false));
$('plotClose').addEventListener('click', () => showPlotWindow(false));
$('plotRestore').addEventListener('click', () => showPlotWindow(true));

// ============================================================
// 控制面板 UI
// ============================================================
function renderChargeList() {
  const list = $('chargeList');
  list.innerHTML = '';
  for (const c of state.charges) {
    const pos = c.q >= 0;
    const card = document.createElement('div');
    card.className = 'charge-card' + (c.id === state.selId ? ' selected' : '');
    card.dataset.id = c.id;
    card.innerHTML = `
      <div class="cc-dot ${pos ? 'pos' : 'neg'}" data-sign="${pos ? '+' : '−'}"></div>
      <div class="cc-mid">
        <div class="cc-q">
          <span class="q-sign ${pos ? 'pos' : 'neg'}">q</span>
          <span>=</span>
          <input class="num" type="number" step="0.1" value="${fmt(c.q)}" aria-label="电荷量 μC">
          <span class="unit">μC</span>
        </div>
        <div class="cc-pos">(${fmt(c.x)}, ${fmt(c.y)}) m</div>
      </div>
      <button class="cc-del" title="删除电荷" aria-label="删除">
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <path d="M4 7h16M9 7V5a1 1 0 0 1 1-1h4a1 1 0 0 1 1 1v2m3 0-1 13a1 1 0 0 1-1 1H8a1 1 0 0 1-1-1L6 7"/>
        </svg>
      </button>`;
    const qInput = card.querySelector('.num');
    qInput.addEventListener('change', () => {
      const v = parseFloat(qInput.value);
      if (Number.isFinite(v)) setChargeQ(c.id, v);
      else qInput.value = fmt(c.q);
    });
    card.querySelector('.cc-del').addEventListener('click', e => {
      e.stopPropagation();
      removeCharge(c.id);
    });
    card.addEventListener('click', e => {
      // 点击输入框或删除按钮时不触发选中重建，避免输入框失焦
      if (e.target.closest('input') || e.target.closest('.cc-del')) return;
      state.selId = c.id;
      renderChargeList();
    });
    list.appendChild(card);
  }
  $('emptyCharges').style.display = state.charges.length ? 'none' : 'block';
}

// 滑块绑定（含进度填充）
function bindSlider(id, apply) {
  const el = $(id), out = $(id + 'Out');
  const upd = () => {
    const v = parseFloat(el.value);
    apply(v);
    const pct = (v - parseFloat(el.min)) / (parseFloat(el.max) - parseFloat(el.min)) * 100;
    el.style.setProperty('--fill', pct + '%');
    if (out) out.textContent = (v % 1 === 0 ? v.toFixed(0) : v.toFixed(2).replace(/0$/, ''));
  };
  el.addEventListener('input', () => { upd(); scheduleRecompute(); });
  upd();
}
function bindToggle(id, apply) {
  const el = $(id);
  el.addEventListener('change', () => { apply(el.checked); scheduleRecompute(); });
}
function bindSwatches(boxId, colorId, apply) {
  const box = $(boxId), colorInput = $(colorId);
  const setSel = v => box.querySelectorAll('.swatch').forEach(b => b.classList.toggle('selected', b.dataset.c === v));
  box.addEventListener('click', e => {
    const sw = e.target.closest('.swatch');
    if (!sw || !sw.dataset.c) return;
    colorInput.value = sw.dataset.c;
    apply(sw.dataset.c);
    setSel(sw.dataset.c);
    scheduleRecompute();
  });
  colorInput.addEventListener('input', () => {
    apply(colorInput.value);
    setSel(colorInput.value);
    scheduleRecompute();
  });
  setSel(colorInput.value);
}

function bindUI() {
  bindToggle('tglField', v => { state.showField = v; });
  bindToggle('tglEqui', v => { state.showEqui = v; });
  bindToggle('tglGrid', v => { state.showGrid = v; });
  bindToggle('tglLockX', v => { state.lockX = v; });
  bindToggle('tglArrows', v => { state.field.arrows = v; });

  bindSlider('fldDensity', v => { state.field.density = v; });
  bindSlider('fldWidth', v => { state.field.width = v; });
  bindSlider('eqLevels', v => { state.equi.levels = v; });
  bindSlider('eqOpacity', v => { state.equi.opacity = v; });

  bindSwatches('fldSwatches', 'fldColor', v => { state.field.color = v; });
  bindSwatches('eqSwatches', 'eqColor', v => { state.equi.color = v; });

  // 线型按钮组
  const styleBtns = $('fldStyle').querySelectorAll('button');
  styleBtns.forEach(b => b.addEventListener('click', () => {
    styleBtns.forEach(x => x.classList.toggle('active', x === b));
    state.field.dashed = b.dataset.style === 'dashed';
    scheduleRecompute();
  }));

  // 添加电荷
  $('addPos').addEventListener('click', () => {
    const w = s2w(W / 2 - 40, H / 2 - 30);
    addCharge(w.x, w.y, 2);
  });
  $('addNeg').addEventListener('click', () => {
    const w = s2w(W / 2 + 40, H / 2 - 30);
    addCharge(w.x, w.y, -2);
  });

  // 图像 tab
  const tabs = $('plotTabs').querySelectorAll('button');
  tabs.forEach(b => b.addEventListener('click', () => {
    tabs.forEach(x => x.classList.toggle('active', x === b));
    state.plot.tab = b.dataset.tab;
    drawPlot();
  }));

  // 图像参数
  $('plotQ0').addEventListener('change', e => {
    const v = parseFloat(e.target.value);
    if (Number.isFinite(v)) state.plot.q0 = v;
    scheduleRecompute();
  });
  $('plotY').addEventListener('change', e => {
    const v = parseFloat(e.target.value);
    if (Number.isFinite(v)) state.plot.yLine = v;
    scheduleRecompute();
  });
  $('plotXMin').addEventListener('change', () => scheduleRecompute());
  $('plotXMax').addEventListener('change', () => scheduleRecompute());

  // 面板折叠 / 恢复
  const setPanelCollapsed = collapsed => {
    $('panel').classList.toggle('collapsed', collapsed);
    $('panelRestore').classList.toggle('hidden', !collapsed);
  };
  $('collapseBtn').addEventListener('click', () => {
    setPanelCollapsed(!$('panel').classList.contains('collapsed'));
  });
  $('panelRestore').addEventListener('click', () => setPanelCollapsed(false));

  // 底部按钮
  $('btnResetView').addEventListener('click', () => {
    state.view.cx = 0; state.view.cy = 0; state.view.scale = 110;
    scheduleRecompute(true);
  });
  $('btnClearAll').addEventListener('click', () => {
    state.charges = [];
    state.selId = null;
    renderChargeList();
    scheduleRecompute(true);
  });
}

// ============================================================
// 初始化
// ============================================================
function resize() {
  W = window.innerWidth;
  H = window.innerHeight;
  DPR = Math.min(window.devicePixelRatio || 1, 2);
  canvas.width = W * DPR; canvas.height = H * DPR;
  staticCanvas.width = W * DPR; staticCanvas.height = H * DPR;
}
window.addEventListener('resize', debounce(() => {
  resize();
  scheduleRecompute(true);
  drawPlot();
}, 120));

function init() {
  resize();
  bindUI();
  // 初始演示电荷
  addCharge(-1.4, 0, 3, true);
  addCharge(1.4, 0, -2, true);
  state.selId = state.charges[0].id;
  renderChargeList();
  scheduleRecompute(true);
  requestAnimationFrame(renderDynamic);
}
init();
