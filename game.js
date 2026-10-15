// 密码推理·数谜迷局 —— 微信小游戏（Canvas 实现）
// 玩法：Mastermind 式数字推理，根据线索卡推断隐藏密码（数字不重复）。

/* ---------------- 屏幕适配 ---------------- */
const sysInfo = (typeof wx.getWindowInfo === 'function') ? wx.getWindowInfo() : wx.getSystemInfoSync();
const W = sysInfo.windowWidth;
const H = sysInfo.windowHeight;
let dpr = sysInfo.pixelRatio || 1;
const insetB = (sysInfo.safeAreaInsets && sysInfo.safeAreaInsets.bottom) ? sysInfo.safeAreaInsets.bottom : 0;
// 顶部安全区：状态栏 / 刘海 / 右上角系统胶囊按钮 三者取最大，避免自定义内容被遮挡
let menuBottom = 0;
try { if (typeof wx.getMenuButtonBoundingClientRect === 'function') { const mr = wx.getMenuButtonBoundingClientRect(); if (mr && mr.bottom) menuBottom = mr.bottom; } } catch (e) {}
let insetT = Math.max(sysInfo.statusBarHeight || 20, (sysInfo.safeArea && sysInfo.safeArea.top) || 0);
if (menuBottom > insetT) insetT = menuBottom;
if (insetT > 100) insetT = 100;

const canvas = (typeof wx.createCanvas === 'function') ? wx.createCanvas() : wx.getGameCanvas();
const ctx = canvas.getContext('2d');
canvas.width = Math.round(W * dpr);
canvas.height = Math.round(H * dpr);
ctx.scale(dpr, dpr);

/* ---------------- 颜色 ---------------- */
const C = {
  paperTop: '#ecdfc6', paperMid: '#e2d2b2', paperBot: '#d6c39c',
  ink: '#3a2c1c', seal: '#8f2b1a', sealDark: '#6d1f12',
  tileBorder: '#7a2415', gold: '#b8860b',
  clueBg: 'rgba(253,248,236,0.78)', clueBorder: 'rgba(122,36,21,0.35)',
  tileFaceTop: '#fdf8ec', tileFaceBot: '#f3ead2',
  btnClearTop: '#f5ecd6', btnClearBot: '#e6d9ba', btnOkTop: '#a63a22', btnOkBot: '#7e2413'
};

const CN = ["零", "一", "两", "三", "四"];
const SAVE_KEY = 'mmTuiLiSave';

/* ---------------- 谜题核心（纯函数） ---------------- */
function analyze(guess, pwd) {
  let bulls = 0; const g = [], p = [];
  for (let i = 0; i < pwd.length; i++) {
    if (guess[i] === pwd[i]) bulls++;
    else { g.push(guess[i]); p.push(pwd[i]); }
  }
  let common = 0; const used = {};
  for (let i = 0; i < g.length; i++) {
    for (let j = 0; j < p.length; j++) {
      if (g[i] === p[j] && !used[j]) { used[j] = true; common++; break; }
    }
  }
  return { bulls: bulls, common: bulls + common };
}
function permutations(arr, k) {
  const res = [];
  (function rec(cur, rest) {
    if (cur.length === k) { res.push(cur); return; }
    for (let i = 0; i < rest.length; i++) rec(cur.concat([rest[i]]), rest.slice(0, i).concat(rest.slice(i + 1)));
  })([], arr);
  return res;
}
function genPuzzle(len) {
  const digits = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
  for (let i = digits.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1)); const t = digits[i]; digits[i] = digits[j]; digits[j] = t;
  }
  const pwd = digits.slice(0, len);
  const all = permutations([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], len);
  let candidates = all.slice();
  const clues = []; const usedGuesses = {}; let guard = 0;
  while (candidates.length > 1 || clues.length < Math.max(3, len + 1)) {
    guard++; if (guard > 400) return genPuzzle(len);
    let guess, g;
    do {
      g = []; for (let k = 0; k < len; k++) g.push(Math.floor(Math.random() * 10));
      guess = g.join(',');
    } while (usedGuesses[guess] || guess === pwd.join(','));
    usedGuesses[guess] = true;
    const a = analyze(g, pwd);
    const next = candidates.filter(function (c) { const r = analyze(g, c); return r.bulls === a.bulls && r.common === a.common; });
    if (next.length === 0) continue;
    if (clues.length >= 3 && next.length === 1) { candidates = next; clues.push({ guess: g, bulls: a.bulls, common: a.common }); break; }
    if (next.length === 1 && clues.length < 3) continue;
    candidates = next; clues.push({ guess: g, bulls: a.bulls, common: a.common });
    if (clues.length >= 7) return genPuzzle(len);
  }
  return { pwd: pwd, clues: clues };
}
function clueText(c) {
  if (c.common === 0) return [{ text: '所有数字都不正确' }];
  const head = CN[c.common] + '个数字正确';
  if (c.bulls === 0) return [{ text: head, bold: true }, { text: '，但位置都不正确' }];
  if (c.bulls === c.common) return [{ text: head, bold: true }, { text: '，且位置也都正确' }];
  return [{ text: head, bold: true }, { text: '，其中' + CN[c.bulls] + '个位置正确' }];
}

/* ---------------- 状态 ---------------- */
const state = { level: 1, score: 0, pwdLen: 3, password: [], input: [], hintIdx: [], hintCount: 0, solved: false, startTime: 0, soundOn: true };
let clues = [];
let scrollY = 0, maxScroll = 0;
let toast = { msg: '', until: 0 };
let levelFloat = { main: '', sub: '', until: 0 };
let showWin = false, winData = { title: '', reveal: '', time: '--', hints: 0, score: '+0' };
let showRules = false;
let shakeUntil = 0;
let popIdx = -1, popUntil = 0;
let L = null;
let spin = [];        // 各数字轮的连续位置（浮点）；静止时等于 input[i]
let snapTo = [];      // 松手后吸附目标（null 表示已静止）

/* ---------------- 音效（WebAudio，无外部资源） ---------------- */
let actx = null;
function getCtx() {
  if (!actx) { try { actx = wx.createWebAudioContext(); } catch (e) { actx = null; } }
  return actx;
}
function beep(freq, dur, type, vol) {
  if (!state.soundOn) return;
  const ac = getCtx(); if (!ac) return;
  try {
    const o = ac.createOscillator(), g = ac.createGain();
    o.type = type || 'sine'; o.frequency.value = freq;
    g.gain.setValueAtTime(vol || 0.12, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001, ac.currentTime + dur);
    o.connect(g); g.connect(ac.destination); o.start(); o.stop(ac.currentTime + dur);
  } catch (e) {}
}
function sndKey() { beep(620, 0.06, 'square', 0.06); }
function sndDel() { beep(380, 0.07, 'square', 0.06); }
function sndErr() { beep(180, 0.25, 'sawtooth', 0.1); }
function sndWin() { const self = this; [523, 659, 784, 1047].forEach(function (f, i) { setTimeout(function () { beep(f, 0.22, 'triangle', 0.14); }, i * 110); }); }

/* ---------------- 存档 ---------------- */
function saveGame() {
  try { wx.setStorageSync(SAVE_KEY, { level: state.level, score: state.score, soundOn: state.soundOn }); } catch (e) {}
}
function loadGame() {
  try {
    const s = wx.getStorageSync(SAVE_KEY) || {};
    if (s.level) state.level = s.level;
    if (s.score) state.score = s.score;
    if (s.soundOn === false) state.soundOn = false;
  } catch (e) {}
}

/* ---------------- 布局 ---------------- */
function computeLayout() {
  const pad = 18;
  const headTop = insetT + 4;          // 头部行顶部（积分 / 关卡 / 图标）
  const headH = 28;
  const titleY = headTop + headH + 24; // 标题垂直中心
  const subY = titleY + 28;            // 副标题垂直中心
  const gap = 14;
  const maxDigit = 70;
  let dw = Math.min(maxDigit, (W - pad * 2 - gap * (state.pwdLen - 1)) / state.pwdLen);
  dw = Math.max(48, dw);
  const dh = dw * 1.16;
  const totalW = dw * state.pwdLen + gap * (state.pwdLen - 1);
  const codeX = (W - totalW) / 2;
  const codeY = subY + 18;
  const digitRects = [];
  for (let i = 0; i < state.pwdLen; i++) digitRects.push({ x: codeX + i * (dw + gap), y: codeY, w: dw, h: dh });
  const codeBottom = codeY + dh;
  const actionH = 52;
  const cluesTop = codeBottom + 16;
  const cluesBottom = H - insetB - 16 - actionH - 16;
  const cluesRect = { x: pad, y: cluesTop, w: W - pad * 2, h: Math.max(40, cluesBottom - cluesTop) };
  const abY = cluesBottom + 16;
  const clearW = Math.round((W - pad * 2) * 0.34);
  const clearRect = { x: pad, y: abY, w: clearW, h: actionH };
  const submitRect = { x: pad + clearW + 12, y: abY, w: (W - pad * 2) - clearW - 12, h: actionH };
  const isz = 30, ig = 14;
  const iy = headTop + (headH - isz) / 2;
  const icons = {
    hint:  { x: W - pad - isz * 3 - ig * 2, y: iy, w: isz, h: isz },
    rules: { x: W - pad - isz * 2 - ig,     y: iy, w: isz, h: isz },
    sound: { x: W - pad - isz,              y: iy, w: isz, h: isz }
  };
  const winBtn = { x: W * 0.12, y: H * 0.5 + 120, w: W * 0.76, h: 50 };
  const rulesBtn = { x: W * 0.1, y: H * 0.5 + 150, w: W * 0.8, h: 50 };
  return { pad, headTop, headH, titleY, subY, codeX, codeY, dw, dh, gap, digitRects, cluesRect, clearRect, submitRect, icons, winBtn, rulesBtn };
}

/* ---------------- 绘制工具 ---------------- */
function roundRect(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}
function inRect(r, x, y) { return r && x >= r.x && x <= r.x + r.w && y >= r.y && y <= r.y + r.h; }
function inIcon(r, x, y) { const m = 7; return r && x >= r.x - m && x <= r.x + r.w + m && y >= r.y - m && y <= r.y + r.h + m; }
function spacedText(text, cx, y, font, color, spacing) {
  ctx.font = font; ctx.fillStyle = color; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
  let total = 0; const ws = [];
  for (let i = 0; i < text.length; i++) { const wdt = ctx.measureText(text[i]).width; ws.push(wdt); total += wdt + (i < text.length - 1 ? spacing : 0); }
  let x = cx - total / 2;
  for (let i = 0; i < text.length; i++) { ctx.fillText(text[i], x, y); x += ws[i] + spacing; }
}
function spacedWidth(text, font, spacing) {
  ctx.font = font; let t = 0;
  for (let i = 0; i < text.length; i++) t += ctx.measureText(text[i]).width + (i < text.length - 1 ? spacing : 0);
  return t;
}
function drawSegments(x, y, segs, fs, normal, boldColor, maxW) {
  ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
  let f = fs;
  // 先按基准字号量总宽，超出可用宽度则整体等比缩小
  if (maxW) {
    let total = 0;
    for (let i = 0; i < segs.length; i++) { ctx.font = (segs[i].bold ? 'bold ' : '') + fs + 'px "Songti SC", serif'; total += ctx.measureText(segs[i].text).width; }
    if (total > maxW) f = Math.max(11, fs * maxW / total);
  }
  let cx = x;
  for (let i = 0; i < segs.length; i++) {
    const s = segs[i];
    ctx.font = (s.bold ? 'bold ' : '') + f + 'px "Songti SC", serif';
    ctx.fillStyle = s.bold ? boldColor : normal;
    ctx.fillText(s.text, cx, y);
    cx += ctx.measureText(s.text).width;
  }
}

/* ---------------- 各区块绘制 ---------------- */
function drawBackground() {
  const g = ctx.createLinearGradient(0, 0, 0, H);
  g.addColorStop(0, C.paperTop); g.addColorStop(0.45, C.paperMid); g.addColorStop(1, C.paperBot);
  ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);
  const r1 = ctx.createRadialGradient(W * 0.2, H * 0.1, 0, W * 0.2, H * 0.1, W * 0.6);
  r1.addColorStop(0, 'rgba(255,244,214,0.35)'); r1.addColorStop(1, 'rgba(255,244,214,0)');
  ctx.fillStyle = r1; ctx.fillRect(0, 0, W, H);
}
function drawHeader() {
  const cy = L.headTop + L.headH / 2;
  ctx.textBaseline = 'middle';
  // 积分（左）
  ctx.textAlign = 'left';
  ctx.fillStyle = 'rgba(58,44,28,0.55)'; ctx.font = '11px "Songti SC", serif';
  ctx.fillText('积分', 20, cy);
  const sw = ctx.measureText('积分').width;
  ctx.fillStyle = C.sealDark; ctx.font = 'bold 21px Georgia, serif';
  ctx.fillText(String(state.score), 20 + sw + 7, cy + 1);
  // 关卡（居中组合）
  ctx.font = '11px "Songti SC", serif'; const lw = ctx.measureText('关卡').width;
  ctx.font = 'bold 21px Georgia, serif'; const nw = ctx.measureText(String(state.level)).width;
  const tw = lw + nw + 7; const x0 = W / 2 - tw / 2;
  ctx.textAlign = 'left';
  ctx.font = '11px "Songti SC", serif'; ctx.fillStyle = 'rgba(58,44,28,0.55)';
  ctx.fillText('关卡', x0, cy);
  ctx.font = 'bold 21px Georgia, serif'; ctx.fillStyle = C.sealDark;
  ctx.fillText(String(state.level), x0 + lw + 7, cy + 1);
  // 图标（右）
  const icons = [['💡', L.icons.hint], ['❔', L.icons.rules], [state.soundOn ? '🔊' : '🔇', L.icons.sound]];
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  for (let i = 0; i < icons.length; i++) {
    const rc = icons[i][1];
    ctx.font = '20px serif';
    ctx.globalAlpha = 0.92;
    ctx.fillText(icons[i][0], rc.x + rc.w / 2, rc.y + rc.h / 2 + 1);
    ctx.globalAlpha = 1;
  }
}
function drawTitle() {
  const ty = L.titleY;
  const tg = ctx.createLinearGradient(0, ty - 20, 0, ty + 20);
  tg.addColorStop(0, '#a8391f'); tg.addColorStop(0.55, '#8f2b1a'); tg.addColorStop(1, '#6f1c0e');
  ctx.save();
  ctx.shadowColor = 'rgba(110,36,16,0.28)'; ctx.shadowBlur = 7; ctx.shadowOffsetY = 2;
  spacedText('高智商数字推理', W / 2, ty, 'bold 36px "Kaiti SC", serif', tg, 10);
  ctx.restore();
  // 副标题 + 两侧细线
  const st = '烧 脑 解 谜 · 抽 丝 剥 茧';
  spacedText(st, W / 2, L.subY, '12px "Songti SC", serif', 'rgba(58,44,28,0.58)', 4);
  const tw = spacedWidth(st, '12px "Songti SC", serif', 4);
  const lw = 24, gp = 14;
  ctx.strokeStyle = 'rgba(122,36,21,0.30)'; ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(W / 2 - tw / 2 - gp - lw, L.subY); ctx.lineTo(W / 2 - tw / 2 - gp, L.subY);
  ctx.moveTo(W / 2 + tw / 2 + gp, L.subY); ctx.lineTo(W / 2 + tw / 2 + gp + lw, L.subY);
  ctx.stroke();
}
// 旋转数字锁：每个密码位是一枚黄铜数字轮，上下滑动切换 0-9，松手吸附
function drawWheels() {
  const now = Date.now();
  let sx = 0;
  if (now < shakeUntil) sx = Math.sin(now / 25) * 7;
  ctx.save(); ctx.translate(sx, 0);
  for (let i = 0; i < state.pwdLen; i++) {
    const r = L.digitRects[i];
    const hinted = state.hintIdx.indexOf(i) >= 0;
    const cx = r.x + r.w / 2, cy = r.y + r.h / 2;
    const dragging = (touch.wheel === i && touch.dragging);

    // ---- 外框：黄铜圈 ----
    const fr = ctx.createLinearGradient(0, r.y, 0, r.y + r.h);
    fr.addColorStop(0, '#d2ab53'); fr.addColorStop(0.5, '#9c7a2e'); fr.addColorStop(1, '#6e521d');
    ctx.save();
    ctx.shadowColor = 'rgba(60,40,10,0.30)'; ctx.shadowBlur = 8; ctx.shadowOffsetY = 3;
    roundRect(r.x, r.y, r.w, r.h, 12); ctx.fillStyle = fr; ctx.fill();
    ctx.restore();
    // 顶部高光环
    ctx.save();
    roundRect(r.x + 1.5, r.y + 1.5, r.w - 3, r.h - 3, 10);
    ctx.strokeStyle = 'rgba(255,238,200,0.55)'; ctx.lineWidth = 1.2; ctx.stroke();
    ctx.restore();
    // 外描边（拖动中更亮）
    ctx.lineWidth = 2;
    ctx.strokeStyle = dragging ? '#ffe9b0' : (hinted ? '#caa24c' : C.gold);
    roundRect(r.x, r.y, r.w, r.h, 12); ctx.stroke();

    // ---- 内窗（凹陷）----
    const inset = Math.max(6, r.w * 0.16);
    const winX = r.x + inset, winW = r.w - inset * 2;
    const winH = r.h * 0.82, winY = cy - winH / 2;
    ctx.save();
    roundRect(winX, winY, winW, winH, 8);
    const wg = ctx.createLinearGradient(0, winY, 0, winY + winH);
    wg.addColorStop(0, '#241a0d'); wg.addColorStop(0.5, '#100b05'); wg.addColorStop(1, '#241a0d');
    ctx.fillStyle = wg; ctx.fill();
    ctx.restore();

    // ---- 数字轮（裁剪到窗口内滚动）----
    ctx.save();
    roundRect(winX, winY, winW, winH, 8); ctx.clip();
    const cell = winH / 3;
    const v = state.solved ? state.password[i] : spin[i];
    for (let k = 0; k < 10; k++) {
      let raw = k - v;
      while (raw > 5) raw -= 10;
      while (raw < -5) raw += 10;
      const y = cy + raw * cell;
      if (y < winY - cell || y > winY + winH + cell) continue;
      const dist = Math.abs(raw);
      const fs = Math.round(cell * (0.82 - dist * 0.12));
      ctx.font = 'bold ' + fs + 'px Georgia, serif';
      ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.globalAlpha = Math.max(0.12, 1 - dist * 0.5);
      ctx.fillStyle = hinted ? '#e8c25a' : '#f3e6c4';
      ctx.fillText(String(k), cx, y + 1);
    }
    ctx.globalAlpha = 1;
    ctx.restore();

    // ---- 窗口上下渐隐 + 中心高亮 ----
    ctx.save();
    roundRect(winX, winY, winW, winH, 8); ctx.clip();
    const fade = cell * 0.9;
    let fg = ctx.createLinearGradient(0, winY, 0, winY + fade);
    fg.addColorStop(0, 'rgba(16,11,5,0.92)'); fg.addColorStop(1, 'rgba(16,11,5,0)');
    ctx.fillStyle = fg; ctx.fillRect(winX, winY, winW, fade);
    fg = ctx.createLinearGradient(0, winY + winH - fade, 0, winY + winH);
    fg.addColorStop(0, 'rgba(16,11,5,0)'); fg.addColorStop(1, 'rgba(16,11,5,0.92)');
    ctx.fillStyle = fg; ctx.fillRect(winX, winY + winH - fade, winW, fade);
    ctx.fillStyle = 'rgba(255,240,205,0.06)';
    ctx.fillRect(winX, cy - cell * 0.5, winW, cell);
    ctx.restore();

    // ---- 窗口描边 ----
    ctx.lineWidth = 1.5; ctx.strokeStyle = 'rgba(20,12,4,0.85)';
    roundRect(winX, winY, winW, winH, 8); ctx.stroke();
    ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(255,235,190,0.22)';
    roundRect(winX + 1, winY + 1, winW - 2, winH - 2, 7); ctx.stroke();

    // ---- 锁标记（提示位已锁定）----
    if (hinted) {
      ctx.save();
      ctx.font = '13px serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillStyle = '#ffe9b0'; ctx.fillText('🔒', r.x + r.w - 11, r.y + 12);
      ctx.restore();
    }
  }
  ctx.restore();
}
// 矢量小锁图标（用于解锁按钮，跨字体稳定）
function drawLockIcon(x, y, s, body, shackle) {
  ctx.save();
  ctx.lineWidth = Math.max(2, s * 0.16); ctx.strokeStyle = shackle; ctx.lineCap = 'round';
  ctx.beginPath(); ctx.arc(x + s / 2, y + s * 0.44, s * 0.27, Math.PI, 0); ctx.stroke();
  roundRect(x + s * 0.15, y + s * 0.42, s * 0.7, s * 0.5, s * 0.14);
  ctx.fillStyle = body; ctx.fill();
  ctx.fillStyle = 'rgba(20,12,4,0.55)';
  ctx.beginPath(); ctx.arc(x + s / 2, y + s * 0.64, s * 0.07, 0, Math.PI * 2); ctx.fill();
  ctx.restore();
}
// 采样纸张背景在任意 y 处的颜色，用于底部渐隐无缝衔接
function paperColorAt(y) {
  const stops = [[0, [236, 223, 198]], [0.45, [226, 210, 178]], [1, [214, 195, 156]]];
  const p = Math.min(1, Math.max(0, y / H));
  let a = stops[0], b = stops[1];
  for (let i = 0; i < stops.length - 1; i++) { if (p >= stops[i][0] && p <= stops[i + 1][0]) { a = stops[i]; b = stops[i + 1]; break; } }
  const t = (p - a[0]) / ((b[0] - a[0]) || 1);
  return [a[1][0] + (b[1][0] - a[1][0]) * t, a[1][1] + (b[1][1] - a[1][1]) * t, a[1][2] + (b[1][2] - a[1][2]) * t];
}
function drawClues() {
  const rowH = 63, gap = 10;
  const area = L.cluesRect;
  const contentH = clues.length > 0 ? clues.length * (rowH + gap) - gap : 0;
  const scrollable = contentH > area.h;
  ctx.save();
  ctx.beginPath(); ctx.rect(area.x, area.y, area.w, area.h); ctx.clip();
  // 内容不足一屏时垂直居中，避免底部留白
  let y = (contentH < area.h) ? area.y + (area.h - contentH) / 2 - scrollY : area.y - scrollY;
  for (let i = 0; i < clues.length; i++) {
    const c = clues[i];
    // 卡片（带阴影）
    ctx.save();
    ctx.shadowColor = 'rgba(90,56,24,0.15)'; ctx.shadowBlur = 7; ctx.shadowOffsetY = 2;
    roundRect(area.x, y, area.w, rowH, 12); ctx.fillStyle = C.clueBg; ctx.fill();
    ctx.restore();
    roundRect(area.x, y, area.w, rowH, 12);
    ctx.lineWidth = 1; ctx.strokeStyle = C.clueBorder; ctx.stroke();
    // 左侧红条
    ctx.save();
    roundRect(area.x, y, area.w, rowH, 12); ctx.clip();
    ctx.fillStyle = 'rgba(143,43,26,0.85)'; ctx.fillRect(area.x, y, 4, rowH);
    ctx.restore();
    // 猜测小牌
    const tileW = 28, tileH = 37, ty = y + (rowH - tileH) / 2;
    let gx = area.x + 14;
    for (let k = 0; k < c.guess.length; k++) {
      roundRect(gx, ty, tileW, tileH, 7);
      const tg = ctx.createLinearGradient(0, ty, 0, ty + tileH);
      tg.addColorStop(0, '#f8f1e0'); tg.addColorStop(1, '#e9ddc1');
      ctx.fillStyle = tg; ctx.fill(); ctx.lineWidth = 1.2; ctx.strokeStyle = 'rgba(90,60,30,0.5)'; ctx.stroke();
      ctx.fillStyle = '#33261a'; ctx.font = 'bold 19px Georgia, serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillText(String(c.guess[k]), gx + tileW / 2, ty + tileH / 2 + 1);
      gx += tileW + 7;
    }
    const segs = clueText(c);
    const textX = gx + 10;
    const maxW = area.x + area.w - 14 - textX;
    drawSegments(textX, y + rowH / 2, segs, 15, '#4a3421', C.sealDark, maxW);
    y += rowH + gap;
  }
  // 可滚动时底部渐隐，暗示还能上滑
  if (scrollable) {
    const bandH = 34, by = area.y + area.h - bandH;
    const fg = ctx.createLinearGradient(0, by, 0, by + bandH);
    for (let i = 0; i <= 5; i++) {
      const cc = paperColorAt(by + bandH * i / 5);
      fg.addColorStop(i / 5, 'rgba(' + (cc[0] | 0) + ',' + (cc[1] | 0) + ',' + (cc[2] | 0) + ',' + (i / 5).toFixed(2) + ')');
    }
    ctx.fillStyle = fg; ctx.fillRect(area.x, by, area.w, bandH);
  }
  ctx.restore();
  maxScroll = scrollable ? contentH - area.h + 6 : 0;
  if (scrollY > maxScroll) scrollY = maxScroll;
  if (scrollY < 0) scrollY = 0;
}
function drawActions() {
  // 清空
  ctx.save();
  ctx.shadowColor = 'rgba(90,56,24,0.16)'; ctx.shadowBlur = 8; ctx.shadowOffsetY = 3;
  let g = ctx.createLinearGradient(0, L.clearRect.y, 0, L.clearRect.y + L.clearRect.h);
  g.addColorStop(0, C.btnClearTop); g.addColorStop(1, C.btnClearBot);
  roundRect(L.clearRect.x, L.clearRect.y, L.clearRect.w, L.clearRect.h, 13); ctx.fillStyle = g; ctx.fill();
  ctx.restore();
  roundRect(L.clearRect.x, L.clearRect.y, L.clearRect.w, L.clearRect.h, 13);
  ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(120,85,40,0.45)'; ctx.stroke();
  spacedText('清 空', L.clearRect.x + L.clearRect.w / 2, L.clearRect.y + L.clearRect.h / 2, 'bold 17px "Kaiti SC", serif', '#6b5236', 4);
  // 解锁（主按钮）
  ctx.save();
  ctx.shadowColor = 'rgba(126,36,19,0.32)'; ctx.shadowBlur = 10; ctx.shadowOffsetY = 3;
  g = ctx.createLinearGradient(0, L.submitRect.y, 0, L.submitRect.y + L.submitRect.h);
  g.addColorStop(0, C.btnOkTop); g.addColorStop(1, C.btnOkBot);
  roundRect(L.submitRect.x, L.submitRect.y, L.submitRect.w, L.submitRect.h, 13); ctx.fillStyle = g; ctx.fill();
  ctx.restore();
  ctx.save();
  roundRect(L.submitRect.x + 2, L.submitRect.y + 3, L.submitRect.w - 4, L.submitRect.h * 0.4, 10);
  ctx.strokeStyle = 'rgba(255,225,190,0.32)'; ctx.lineWidth = 1; ctx.stroke();
  ctx.restore();
  // 锁图标 + 文字（整体居中）
  const ls = 22, lgap = 10;
  const lt = '解 锁';
  const ltw = spacedWidth(lt, 'bold 17px "Kaiti SC", serif', 6);
  const lgw = ls + lgap + ltw;
  const lcx = L.submitRect.x + L.submitRect.w / 2;
  const lcy = L.submitRect.y + L.submitRect.h / 2;
  drawLockIcon(lcx - lgw / 2, lcy - ls / 2, ls, '#f0d089', '#3a2a12');
  spacedText(lt, lcx - lgw / 2 + ls + lgap + ltw / 2, lcy, 'bold 17px "Kaiti SC", serif', '#fdf3dc', 6);
}
function drawToast() {
  const now = Date.now();
  if (now > toast.until) return;
  const a = Math.min(1, (toast.until - now) / 300);
  ctx.globalAlpha = a;
  ctx.font = '14px serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  const tw = ctx.measureText(toast.msg).width + 44;
  roundRect(W / 2 - tw / 2, H * 0.32, tw, 36, 18);
  ctx.fillStyle = 'rgba(40,20,8,0.88)'; ctx.fill();
  ctx.fillStyle = '#f5e8cd'; ctx.fillText(toast.msg, W / 2, H * 0.32 + 18);
  ctx.globalAlpha = 1;
}
function drawLevelFloat() {
  const now = Date.now();
  if (now > levelFloat.until) return;
  const t = (levelFloat.until - now) / 1400;
  const a = t > 0.75 ? (1 - t) / 0.25 : (t < 0.18 ? t / 0.18 : 1);
  ctx.globalAlpha = Math.max(0, a);
  const cx = W / 2, cy = H * 0.40;
  // 半透明底卡，避免与线索卡叠字
  const mw = spacedWidth(levelFloat.main, 'bold 34px "Kaiti SC", serif', 6);
  ctx.font = '13px "Songti SC", serif';
  const sw = ctx.measureText(levelFloat.sub).width;
  const pw = Math.min(W - 48, Math.max(mw, sw) + 64), ph = 106;
  ctx.save();
  ctx.shadowColor = 'rgba(20,10,4,0.35)'; ctx.shadowBlur = 14; ctx.shadowOffsetY = 4;
  roundRect(cx - pw / 2, cy - ph / 2 - 6, pw, ph, 18);
  ctx.fillStyle = 'rgba(30,16,6,0.64)'; ctx.fill();
  ctx.restore();
  roundRect(cx - pw / 2, cy - ph / 2 - 6, pw, ph, 18);
  ctx.strokeStyle = 'rgba(214,180,120,0.45)'; ctx.lineWidth = 1; ctx.stroke();
  spacedText(levelFloat.main, cx, cy - 12, 'bold 34px "Kaiti SC", serif', '#f3dfae', 6);
  ctx.font = '13px "Songti SC", serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillStyle = 'rgba(243,223,174,0.88)'; ctx.fillText(levelFloat.sub, cx, cy + 26);
  ctx.globalAlpha = 1;
}
function drawWin() {
  if (!showWin) return;
  ctx.fillStyle = 'rgba(20,10,4,0.72)'; ctx.fillRect(0, 0, W, H);
  const cw = W * 0.82, cx = W * 0.09, cy = H * 0.26, ch = H * 0.48;
  roundRect(cx, cy, cw, ch, 16);
  const g = ctx.createLinearGradient(0, cy, 0, cy + ch);
  g.addColorStop(0, '#f2e6c9'); g.addColorStop(1, '#e3d2ab');
  ctx.fillStyle = g; ctx.fill(); ctx.lineWidth = 3; ctx.strokeStyle = C.seal; ctx.stroke();
  // 印章
  ctx.save(); ctx.translate(cx + cw / 2, cy + 42); ctx.rotate(-0.2);
  ctx.lineWidth = 3; ctx.strokeStyle = C.seal; roundRect(-26, -26, 52, 52, 26); ctx.stroke();
  ctx.fillStyle = C.seal; ctx.font = 'bold 20px "Kaiti SC", serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText('破解', 0, 0); ctx.restore();
  ctx.fillStyle = C.sealDark; ctx.font = 'bold 23px "Kaiti SC", serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText('宝箱已开启', cx + cw / 2, cy + 92);

  // ---- 宝箱 ----
  const bw = cw * 0.5, bh = bw * 0.62;
  const bx = cx + cw / 2 - bw / 2, by = cy + 132;
  const lidRy = bh * 0.30;
  // 金光
  const glow = ctx.createRadialGradient(cx + cw / 2, by + bh * 0.4, 6, cx + cw / 2, by + bh * 0.4, bw * 1.0);
  glow.addColorStop(0, 'rgba(255,214,120,0.5)'); glow.addColorStop(1, 'rgba(255,214,120,0)');
  ctx.fillStyle = glow; ctx.fillRect(cx, by - bh * 0.6, cw, bh * 1.8);
  // 箱体
  ctx.save();
  ctx.shadowColor = 'rgba(60,40,10,0.30)'; ctx.shadowBlur = 12; ctx.shadowOffsetY = 4;
  roundRect(bx, by, bw, bh, 10); ctx.fillStyle = '#7a4a22'; ctx.fill();
  ctx.restore();
  const bodyG = ctx.createLinearGradient(0, by, 0, by + bh);
  bodyG.addColorStop(0, '#9a6531'); bodyG.addColorStop(1, '#6b3f1c');
  ctx.save(); roundRect(bx, by, bw, bh, 10); ctx.clip(); ctx.fillStyle = bodyG; ctx.fillRect(bx, by, bw, bh); ctx.restore();
  // 拱形顶盖
  ctx.save();
  ctx.beginPath();
  ctx.ellipse(bx + bw / 2, by + 4, bw / 2, lidRy, 0, Math.PI, 0);
  ctx.closePath();
  const lidG = ctx.createLinearGradient(0, by - lidRy, 0, by + 4);
  lidG.addColorStop(0, '#b9823f'); lidG.addColorStop(1, '#8a5a28');
  ctx.fillStyle = lidG; ctx.fill();
  ctx.restore();
  // 金边：盖缝 + 两条竖带
  ctx.strokeStyle = '#e7c45f'; ctx.lineWidth = 3;
  ctx.beginPath(); ctx.moveTo(bx, by + 4); ctx.lineTo(bx + bw, by + 4); ctx.stroke();
  ctx.lineWidth = Math.max(4, bw * 0.07); ctx.strokeStyle = '#d9b24e';
  ctx.beginPath(); ctx.moveTo(bx + bw * 0.22, by); ctx.lineTo(bx + bw * 0.22, by + bh); ctx.stroke();
  ctx.beginPath(); ctx.moveTo(bx + bw * 0.78, by); ctx.lineTo(bx + bw * 0.78, by + bh); ctx.stroke();
  // 锁
  const lkw = bw * 0.2, lkh = bh * 0.26, lkx = bx + bw / 2 - lkw / 2, lky = by + bh * 0.42;
  roundRect(lkx, lky, lkw, lkh, 4);
  const lkG = ctx.createLinearGradient(0, lky, 0, lky + lkh);
  lkG.addColorStop(0, '#ffe39a'); lkG.addColorStop(1, '#caa14a'); ctx.fillStyle = lkG; ctx.fill();
  ctx.fillStyle = '#5a3a14'; ctx.beginPath(); ctx.arc(lkx + lkw / 2, lky + lkh * 0.55, lkw * 0.13, 0, Math.PI * 2); ctx.fill();
  // 溢出的金币
  const coinR = bw * 0.075;
  const coins = [[bx + bw * 0.30, by - bh * 0.18], [bx + bw * 0.5, by - bh * 0.30], [bx + bw * 0.7, by - bh * 0.14]];
  for (let k = 0; k < coins.length; k++) {
    const cg = ctx.createRadialGradient(coins[k][0] - coinR * 0.3, coins[k][1] - coinR * 0.3, 1, coins[k][0], coins[k][1], coinR);
    cg.addColorStop(0, '#ffe9a8'); cg.addColorStop(1, '#c79a3c');
    ctx.beginPath(); ctx.arc(coins[k][0], coins[k][1], coinR, 0, Math.PI * 2);
    ctx.fillStyle = cg; ctx.fill();
    ctx.lineWidth = 1; ctx.strokeStyle = '#a07c2e'; ctx.stroke();
  }
  // 宝石
  function gem(gx, gy, gr, col) {
    ctx.save(); ctx.translate(gx, gy);
    ctx.beginPath(); ctx.moveTo(0, -gr); ctx.lineTo(gr * 0.7, 0); ctx.lineTo(0, gr); ctx.lineTo(-gr * 0.7, 0); ctx.closePath();
    ctx.fillStyle = col; ctx.fill();
    ctx.fillStyle = 'rgba(255,255,255,0.6)'; ctx.beginPath(); ctx.moveTo(0, -gr); ctx.lineTo(gr * 0.7, 0); ctx.lineTo(0, 0); ctx.closePath(); ctx.fill();
    ctx.restore();
  }
  gem(bx + bw * 0.40, by - bh * 0.46, bw * 0.05, '#e0556b');
  gem(bx + bw * 0.62, by - bh * 0.42, bw * 0.05, '#4fb0c4');

  // ---- 密码金币排 ----
  const digits = winData.reveal.split(' ');
  const rc = 15, rgap = 12;
  const rW = digits.length * rc * 2 + (digits.length - 1) * rgap;
  const coinY = by + bh + 30;
  for (let k = 0; k < digits.length; k++) {
    const x = cx + cw / 2 - rW / 2 + rc + k * (rc * 2 + rgap);
    const cg2 = ctx.createRadialGradient(x - rc * 0.3, coinY - rc * 0.3, 1, x, coinY, rc);
    cg2.addColorStop(0, '#ffe9a8'); cg2.addColorStop(1, '#c79a3c');
    ctx.beginPath(); ctx.arc(x, coinY, rc, 0, Math.PI * 2); ctx.fillStyle = cg2; ctx.fill();
    ctx.lineWidth = 1.5; ctx.strokeStyle = '#a07c2e'; ctx.stroke();
    ctx.fillStyle = '#5a3a14'; ctx.font = 'bold 16px Georgia, serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(digits[k], x, coinY + 1);
  }
  ctx.font = '13px serif'; ctx.fillStyle = '#4a3421'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText('用时 ' + winData.time + '   提示 ' + winData.hints + '   得分 ' + winData.score, cx + cw / 2, coinY + rc + 20);
  // 按钮
  const b = L.winBtn;
  const bg = ctx.createLinearGradient(0, b.y, 0, b.y + b.h);
  bg.addColorStop(0, C.btnOkTop); bg.addColorStop(1, C.btnOkBot);
  roundRect(b.x, b.y, b.w, b.h, 12); ctx.fillStyle = bg; ctx.fill();
  spacedText('下一关', b.x + b.w / 2, b.y + b.h / 2, 'bold 17px "Kaiti SC", serif', '#fdf3dc', 4);
}
function drawRules() {
  if (!showRules) return;
  ctx.fillStyle = 'rgba(20,10,4,0.72)'; ctx.fillRect(0, 0, W, H);
  const cw = W * 0.84, cx = W * 0.08, cy = H * 0.22, ch = H * 0.56;
  roundRect(cx, cy, cw, ch, 16);
  const g = ctx.createLinearGradient(0, cy, 0, cy + ch);
  g.addColorStop(0, '#f2e6c9'); g.addColorStop(1, '#e3d2ab');
  ctx.fillStyle = g; ctx.fill(); ctx.lineWidth = 3; ctx.strokeStyle = C.seal; ctx.stroke();
  ctx.fillStyle = C.sealDark; ctx.font = 'bold 20px "Kaiti SC", serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText('玩法说明', cx + cw / 2, cy + 36);
  const lines = [
    '根据下方线索卡，推理出顶部',
    '隐藏的数字密码。',
    '每张线索卡是一组错误尝试：',
    '「几个数字正确」指猜中的个数；',
    '「位置也正确」指站对位置。',
    '密码中数字不重复。上下滑动',
    '顶部的数字轮切换 0-9，点解锁。',
    '💡提示锁定一位数字，扣本关分。',
    '前 3 关为三位密码，之后升级四位。'
  ];
  ctx.font = '14px "Songti SC", serif'; ctx.fillStyle = '#4a3421'; ctx.textAlign = 'left';
  let y = cy + 70;
  for (let i = 0; i < lines.length; i++) { ctx.fillText(lines[i], cx + 22, y); y += 26; }
  const b = L.rulesBtn;
  const bg = ctx.createLinearGradient(0, b.y, 0, b.y + b.h);
  bg.addColorStop(0, C.btnOkTop); bg.addColorStop(1, C.btnOkBot);
  roundRect(b.x, b.y, b.w, b.h, 12); ctx.fillStyle = bg; ctx.fill();
  spacedText('开 始 破 解', b.x + b.w / 2, b.y + b.h / 2, 'bold 17px "Kaiti SC", serif', '#fdf3dc', 4);
}

/* ---------------- 主绘制 ---------------- */
function draw() {
  const now = Date.now();
  L = computeLayout();
  // 数字轮吸附缓动
  for (let i = 0; i < spin.length; i++) {
    if (snapTo[i] != null && spin[i] !== snapTo[i]) {
      spin[i] += (snapTo[i] - spin[i]) * 0.28;
      if (Math.abs(snapTo[i] - spin[i]) < 0.01) { spin[i] = snapTo[i]; snapTo[i] = null; }
    }
  }
  drawBackground();
  drawHeader();
  drawTitle();
  drawWheels();
  drawClues();
  drawActions();
  drawToast();
  drawLevelFloat();
  drawWin();
  drawRules();
  requestAnimationFrame(draw);
}

/* ---------------- 流程 ---------------- */
function startLevel() {
  state.pwdLen = state.level <= 3 ? 3 : 4;
  state.solved = false; state.input = new Array(state.pwdLen).fill(0); state.hintIdx = []; state.hintCount = 0;
  spin = state.input.slice(); snapTo = state.input.map(function () { return null; });
  state.startTime = Date.now();
  const p = genPuzzle(state.pwdLen);
  state.password = p.pwd; clues = p.clues; scrollY = 0;
  showWin = false; showRules = false;
  levelFloat = { main: '第 ' + state.level + ' 关', sub: state.pwdLen + ' 位密码 · 线索 ' + p.clues.length + ' 条', until: Date.now() + 1400 };
}
function toastMsg(m) { toast = { msg: m, until: Date.now() + 1600 }; }
function submit() {
  if (state.input.length < state.pwdLen) { toastMsg('还差 ' + (state.pwdLen - state.input.length) + ' 位'); sndErr(); return; }
  for (let i = 0; i < state.hintIdx.length; i++) {
    if (state.input[state.hintIdx[i]] !== state.password[state.hintIdx[i]]) { toastMsg('提示位数字不对哦'); sndErr(); return; }
  }
  if (state.input.join('') === state.password.join('')) win();
  else {
    sndErr(); toastMsg('密码不对，再想想…');
    shakeUntil = Date.now() + 400;
    setTimeout(function () { if (state.solved) return; state.input = []; }, 520);
  }
}
function win() {
  state.solved = true; sndWin();
  const secs = Math.round((Date.now() - state.startTime) / 1000);
  const base = state.pwdLen * 40;
  const earned = Math.max(10, base - state.hintCount * 15 - Math.max(0, secs - 60));
  state.score += earned;
  const timeStr = secs < 60 ? secs + 's' : Math.floor(secs / 60) + 'm' + (secs % 60) + 's';
  winData = { title: '高智商推理破解成功', reveal: state.password.join(' '), time: timeStr, hints: state.hintCount, score: '+' + earned };
  showWin = true; state.level += 1; saveGame();
}
function useHint() {
  if (state.solved) return;
  let pos = -1;
  for (let i = 0; i < state.pwdLen; i++) { if (state.hintIdx.indexOf(i) < 0) { pos = i; break; } }
  if (pos < 0) { toastMsg('没有可提示的位置了'); return; }
  state.hintIdx.push(pos); state.hintCount++;
  state.input[pos] = state.password[pos]; spin[pos] = state.password[pos]; snapTo[pos] = null;
  beep(880, 0.15, 'triangle', 0.1);
  toastMsg('已揭开第 ' + (pos + 1) + ' 位（-' + (state.hintCount * 15) + ' 分）');
}
function clearInput() { if (state.solved) return; if (state.input.length === 0) return; state.input = new Array(state.pwdLen).fill(0); spin = state.input.slice(); snapTo = state.input.map(function () { return null; }); sndDel(); }
function toggleSound() { state.soundOn = !state.soundOn; saveGame(); if (state.soundOn) beep(660, 0.1); }

/* ---------------- 触摸 ---------------- */
const touch = { sx: 0, sy: 0, x: 0, y: 0, moved: 0, dragging: false, active: false, wheel: -1 };
wx.onTouchStart(function (e) {
  const t = e.touches[0]; if (!t) return;
  touch.sx = t.clientX; touch.sy = t.clientY; touch.x = t.clientX; touch.y = t.clientY;
  touch.moved = 0; touch.dragging = false; touch.active = true; touch.wheel = -1;
  // 起点落在某个非提示数字轮上 → 进入旋转模式
  if (L && !showWin && !showRules) {
    for (let i = 0; i < L.digitRects.length; i++) {
      if (inRect(L.digitRects[i], touch.sx, touch.sy) && state.hintIdx.indexOf(i) < 0) { touch.wheel = i; break; }
    }
  }
});
wx.onTouchMove(function (e) {
  if (!touch.active) return;
  const t = e.touches[0]; if (!t) return;
  const dy = t.clientY - touch.y; touch.x = t.clientX; touch.y = t.clientY;
  touch.moved += Math.abs(t.clientX - touch.sx) + Math.abs(t.clientY - touch.sy);
  if (touch.wheel >= 0) {
    // 上下滑动旋转数字轮：上滑数字增大，松手吸附
    const i = touch.wheel;
    const step = (L.digitRects[i].h * 0.82) / 3;
    spin[i] = ((spin[i] - dy / step) % 10 + 10) % 10;
    snapTo[i] = null; touch.dragging = true;
  } else if (L && inRect(L.cluesRect, touch.sx, touch.sy) && Math.abs(t.clientY - touch.sy) > 5) {
    touch.dragging = true;
    scrollY -= dy; if (scrollY < 0) scrollY = 0; if (scrollY > maxScroll) scrollY = maxScroll;
  }
});
wx.onTouchEnd(function () {
  if (!touch.active) return; touch.active = false;
  if (touch.wheel >= 0) {
    if (touch.dragging) {
      const i = touch.wheel;
      snapTo[i] = Math.round(spin[i]) % 10;
      state.input[i] = snapTo[i];
    }
    touch.wheel = -1;
    return;
  }
  if (touch.dragging || touch.moved > 10) return;
  handleTap(touch.sx, touch.sy);
});

function handleTap(x, y) {
  if (!L) return;
  if (showRules) { if (inRect(L.rulesBtn, x, y)) showRules = false; return; }
  if (showWin) { if (inRect(L.winBtn, x, y)) startLevel(); return; }
  if (inIcon(L.icons.hint, x, y)) { useHint(); return; }
  if (inIcon(L.icons.rules, x, y)) { showRules = true; return; }
  if (inIcon(L.icons.sound, x, y)) { toggleSound(); return; }
  if (inRect(L.clearRect, x, y)) { clearInput(); return; }
  if (inRect(L.submitRect, x, y)) { submit(); return; }
}

/* ---------------- 启动 ---------------- */
loadGame();
startLevel();
requestAnimationFrame(draw);
