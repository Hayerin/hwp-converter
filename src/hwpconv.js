/* hwpconv.js — exam PDF -> HWP (4-1 template format). Port of auto.py + build2.py.
   Environment-agnostic: call HwpConv.init({inflate, deflate, deflateRaw, inflateRaw}, DATA) first. */
(function (root) {
'use strict';
let Z = null, DATA = null;

// ------------------------------------------------------------------ small utils
const S = '[ \\t\\n\\r\\f\\v]';                       // Python bytes \s
function rx(src, flags) {                             // byte-regex helper: \s means ASCII whitespace only (Python bytes)
  let o = '', inCls = false;
  for (let i = 0; i < src.length; i++) {
    const c = src[i];
    if (c === '\\') {
      const n = src[i + 1];
      if (n === 's') o += inCls ? ' \\t\\n\\r\\f\\v' : S;
      else if (n === 'S' && inCls) o += '\\x00-\\x08\\x0e-\\x1f!-\\uffff';
      else o += c + n;
      i++; continue;
    }
    if (c === '[' && !inCls) inCls = true; else if (c === ']' && inCls) inCls = false;
    o += c;
  }
  return new RegExp(o, flags);
}
function bin(u8) {                                   // Uint8Array -> latin1 string
  let s = ''; const CH = 0x8000;
  for (let i = 0; i < u8.length; i += CH) s += String.fromCharCode.apply(null, u8.subarray(i, i + CH));
  return s;
}
function ubin(s) { const u = new Uint8Array(s.length); for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i) & 255; return u; }
function concat(arrs) {
  let n = 0; for (const a of arrs) n += a.length;
  const o = new Uint8Array(n); let p = 0; for (const a of arrs) { o.set(a, p); p += a.length; } return o;
}
function pyRound(x) {                                 // Python round(): half to even
  const f = Math.floor(x), d = x - f;
  if (d > 0.5) return f + 1; if (d < 0.5) return f; return (f % 2 === 0) ? f : f + 1;
}
const isAsciiAlnum = c => /^[A-Za-z0-9]$/.test(c);
const pyStrip = s => s.replace(/^[\s\x1c-\x1f]+|[\s\x1c-\x1f]+$/g, '');
const rstrip = (s, ch) => ch === undefined ? s.replace(/[\s\x1c-\x1f]+$/, '') : s.replace(new RegExp('[' + ch + ']+$'), '');
const lstrip = s => s.replace(/^[\s\x1c-\x1f]+/, '');
function u16(v) { return new Uint8Array([v & 255, (v >>> 8) & 255]); }
function u32(v) { return new Uint8Array([v & 255, (v >>> 8) & 255, (v >>> 16) & 255, (v >>> 24) & 255]); }
function utf16(s) { const o = new Uint8Array(s.length * 2); for (let i = 0; i < s.length; i++) { const c = s.charCodeAt(i); o[2 * i] = c & 255; o[2 * i + 1] = c >> 8; } return o; }
function dv(u8) { return new DataView(u8.buffer, u8.byteOffset, u8.byteLength); }
const CRC = (() => { const t = new Uint32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
function crc32(u8, crc) { let c = (crc === undefined ? 0 : crc) ^ 0xFFFFFFFF; for (let i = 0; i < u8.length; i++) c = CRC[(c ^ u8[i]) & 255] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }
function median(a) { const s = a.slice().sort((x, y) => x - y); const n = s.length; return n % 2 ? s[(n - 1) / 2] : (s[n / 2 - 1] + s[n / 2]) / 2; }
const CIRC = '①②③④⑤';

// ------------------------------------------------------------------ PDF objects (pdfobj.py)
function parsePdf(bytes) {
  const data = bin(bytes);
  const objs = new Map();
  const re = rx('(\\d+)\\s+0\\s+obj\\b', 'g'); let m;
  while ((m = re.exec(data))) {
    const n = parseInt(m[1]); const s = m.index + m[0].length; let e = data.indexOf('endobj', s); if (e < 0) e = data.length;
    const body = data.slice(s, e);
    const i = body.indexOf('stream');
    if (i >= 0 && body.slice(0, i).replace(/[ \t\n\r\f\v]+$/, '').endsWith('>>')) {
      const d = body.slice(0, i); let j = i + 6;
      if (body.slice(j, j + 2) === '\r\n') j += 2; else if (body[j] === '\n') j += 1;
      const L = rx('/Length\\s+(\\d+)(\\s+0\\s+R)?').exec(d);
      let st;
      if (L && !L[2]) st = body.slice(j, j + parseInt(L[1]));
      else st = body.slice(j, body.lastIndexOf('endstream'));
      objs.set(n, { d, st });
    } else objs.set(n, { d: body, st: null });
  }
  return objs;
}

// ------------------------------------------------------------------ analysis (auto.py)
function analyze(pdfBytes, filename, overrides) {
  const objs = parsePdf(pdfBytes);
  const REVIEW = [];
  const review = (kind, msg, extra) => REVIEW.push(Object.assign({ kind, msg }, extra || {}));
  const OVR = Object.assign({}, DATA.overrides, overrides || {});
  const ref = (b, key) => { const m = rx('/' + key + '\\s+(\\d+)\\s+0\\s+R').exec(b); return m ? parseInt(m[1]) : null; };
  const inflateS = st => bin(Z.inflate(ubin(st)));
  function parseCmap(st) {
    const t = inflateS(st); const m = new Map();
    const hexs = h => { let o = ''; for (let i = 0; i < h.length; i += 4) o += String.fromCharCode(parseInt(h.slice(i, i + 4), 16)); return o; };
    for (const blk of t.matchAll(/beginbfchar([\s\S]*?)endbfchar/g))
      for (const x of blk[1].matchAll(/<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>/g)) m.set(parseInt(x[1], 16), hexs(x[2]));
    for (const blk of t.matchAll(/beginbfrange([\s\S]*?)endbfrange/g))
      for (const x of blk[1].matchAll(/<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>\s*(<[0-9A-Fa-f]+>|\[[^\]]*\])/g)) {
        const a = parseInt(x[1], 16), b = parseInt(x[2], 16), c = x[3];
        if (c[0] === '<') { const base = parseInt(c.slice(1, -1), 16); for (let i = a; i <= b; i++) m.set(i, String.fromCodePoint(base + i - a)); }
        else { let i = 0; for (const h of c.matchAll(/<([0-9A-Fa-f]+)>/g)) { m.set(a + i, hexs(h[1])); i++; } }
      }
    return m;
  }
  function unesc(s) {
    let out = ''; let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (c === '\\') {
        const n = s[i + 1];
        if (n >= '0' && n <= '7') { let j = i + 1, v = 0; while (j < s.length && j < i + 4 && s[j] >= '0' && s[j] <= '7') { v = v * 8 + s.charCodeAt(j) - 48; j++; } out += String.fromCharCode(v & 255); i = j; continue; }
        out += ({ n: '\n', r: '\r', t: '\t', b: '\b', f: '\f' })[n] || n; i += 2; continue;
      }
      out += c; i++;
    }
    return out;
  }
  const pages = [...objs.keys()].sort((a, b) => a - b).filter(n => rx('/Type\\s*/Page\\b').test(objs.get(n).d));
  function pageGlyphs(pn) {
    const d = objs.get(pn).d; const res = objs.get(ref(d, 'Resources')).d;
    const fonts = {};
    const fd = rx('/Font\\s*<<([\\s\\S]*?)>>').exec(res)[1];
    for (const x of fd.matchAll(rx('/(\\w+)\\s+(\\d+)\\s+0\\s+R', 'g'))) {
      const fo = objs.get(parseInt(x[2])).d; const tu = ref(fo, 'ToUnicode');
      const W = new Map(); let DW = 1000;
      const df = rx('/DescendantFonts\\s*\\[\\s*(\\d+)\\s+0\\s+R').exec(fo);
      if (df) {
        const dfo = objs.get(parseInt(df[1])).d;
        const m_ = rx('/DW\\s+(\\d+)').exec(dfo); DW = m_ ? parseInt(m_[1]) : 1000;
        let wr = rx('/W\\s*(\\[[\\s\\S]*\\])').exec(dfo) || rx('/W\\s+(\\d+)\\s+0\\s+R').exec(dfo);
        if (wr) {
          const arr = wr[1][0] === '[' ? wr[1] : objs.get(parseInt(wr[1])).d;
          const inner = arr.trim()[0] === '[' ? arr.slice(1, arr.lastIndexOf(']')) : arr;
          const toks = inner.match(/\[|\]|[-\d.]+/g) || [];
          let i = 0;
          while (i < toks.length) {
            const a = parseInt(toks[i]);
            if (toks[i + 1] === '[') { let j = i + 2, k = 0; while (toks[j] !== ']') { W.set(a + k, parseFloat(toks[j])); k++; j++; } i = j + 1; }
            else { const b_ = parseInt(toks[i + 1]), w = parseFloat(toks[i + 2]); for (let c_ = a; c_ <= b_; c_++) W.set(c_, w); i += 3; }
          }
        }
      }
      fonts[x[1]] = { cm: parseCmap(objs.get(tu).st), bf: rx('/BaseFont\\s*/([^ \\t\\n\\r\\f\\v]+)').exec(fo)[1], W, DW };
    }
    const c = inflateS(objs.get(ref(d, 'Contents')).st);
    const out = []; let font = null, size = 0, lx = 0, ly = 0;
    const re = rx('\\((?:\\\\[\\s\\S]|[^\\\\)])*\\)\\s*Tj|/(\\w+)\\s+([\\d.]+)\\s+Tf|([-\\d.]+)\\s+([-\\d.]+)\\s+([-\\d.]+)\\s+([-\\d.]+)\\s+([-\\d.]+)\\s+([-\\d.]+)\\s+Tm|([-\\d.]+)\\s+([-\\d.]+)\\s+Td', 'g');
    let m;
    while ((m = re.exec(c))) {
      const g = m[0];
      if (g.endsWith('Tf')) { font = m[1]; size = parseFloat(m[2]); }
      else if (g.endsWith('Tm')) { lx = parseFloat(m[7]); ly = parseFloat(m[8]); }
      else if (g.endsWith('Td')) { lx += parseFloat(m[9]); ly += parseFloat(m[10]); }
      else {
        const s = unesc(g.slice(1, g.lastIndexOf(')')));
        const F = fonts[font]; let txt = '', adv = 0;
        for (let i = 0; i + 1 < s.length || i < s.length; i += 2) {
          const cid = (s.charCodeAt(i) << 8) | (i + 1 < s.length ? s.charCodeAt(i + 1) : 0);
          txt += F.cm.has(cid) ? F.cm.get(cid) : '?';
          adv += F.W.has(cid) ? F.W.get(cid) : F.DW;
        }
        out.push({ x: lx, y: ly, t: txt, sz: size, bf: F.bf, adv: adv / 1000 * size });
      }
    }
    return out;
  }
  function pageContent(pn) { const d = objs.get(pn).d; return [inflateS(objs.get(ref(d, 'Contents')).st), d]; }
  function pagePathsImages(pn) {
    const [c, d] = pageContent(pn);
    const segs = [], imgs = []; let pts = [], clip = null, stack = [], cm = null;
    const re = /([-\d.]+) ([-\d.]+) ([-\d.]+) ([-\d.]+) ([-\d.]+) ([-\d.]+) cm|([-\d.]+) ([-\d.]+) (m|l)\b|(?<![\w/])(h|S|s|f\*?|n|W\*?|q|Q|BT)(?=[ \t\n\r\f\v])|\/(\w+) Do/g;
    let t;
    while ((t = re.exec(c))) {
      if (t[1] !== undefined) { cm = [1, 2, 3, 4, 5, 6].map(i => parseFloat(t[i])); continue; }
      if (t[9]) {
        const p = [parseFloat(t[7]), parseFloat(t[8])];
        if (t[9] === 'm') pts = pts.length ? pts.concat([[p]]) : [[p]]; else if (pts.length) pts[pts.length - 1].push(p);
        continue;
      }
      const op = t[10];
      if (op === 'h') { if (pts.length && pts[pts.length - 1].length > 1) pts[pts.length - 1].push(pts[pts.length - 1][0]); }
      else if (op === 'S' || op === 's') { for (const sp of pts) for (let k = 0; k + 1 < sp.length; k++) segs.push([sp[k][0], sp[k][1], sp[k + 1][0], sp[k + 1][1]]); pts = []; }
      else if (op === 'W' || op === 'W*') {
        if (pts.length) { const xs = [], ys = []; for (const sp of pts) for (const p of sp) { xs.push(p[0]); ys.push(p[1]); } clip = [Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys)]; }
      }
      else if (op === 'n' || op === 'f' || op === 'f*') pts = [];
      else if (op === 'q') stack.push([clip, cm]);
      else if (op === 'Q') { const p = stack.length ? stack.pop() : [null, null]; clip = p[0]; cm = p[1]; }
      if (t[11]) { if (cm) imgs.push({ name: t[11], x: cm[4], y: cm[5], w: cm[0], h: cm[3], clip }); }
    }
    const res = objs.get(ref(d, 'Resources')).d;
    const xo = rx('/XObject\\s*<<([\\s\\S]*?)>>').exec(res);
    const names = {};
    if (xo) for (const x of xo[1].matchAll(rx('/(\\w+)\\s+(\\d+)\\s+0\\s+R', 'g'))) names[x[1]] = parseInt(x[2]);
    for (const im of imgs) im.obj = names[im.name] === undefined ? null : names[im.name];
    return [segs, imgs];
  }
  // ---- images
  const IMAGES = {};          // filename -> Uint8Array
  function exportImage(objn) {
    const { d, st } = objs.get(objn);
    const W = parseInt(rx('/Width\\s+(\\d+)').exec(d)[1]), H = parseInt(rx('/Height\\s+(\\d+)').exec(d)[1]);
    const fm = rx('/Filter\\s*/(\\w+)').exec(d); const flt = fm ? fm[1] : null;
    const bpc = parseInt(rx('/BitsPerComponent\\s+(\\d+)').exec(d)[1]);
    let csm = rx('/ColorSpace\\s*(/\\w+|\\[[^\\]]*\\]|\\d+\\s+0\\s+R)').exec(d)[1];
    if (rx('^\\d+\\s+0\\s+R').test(csm)) csm = pyStrip(objs.get(parseInt(csm)).d);
    const smask = rx('/SMask\\s+(\\d+)\\s+0\\s+R').exec(d);
    if (flt === 'DCTDecode') {
      if (smask) review('image', `JPEG with SMask obj ${objn}`);
      const fn = `img${objn}.jpg`; IMAGES[fn] = ubin(st); return [fn, W, H];
    }
    if (flt !== 'FlateDecode') throw new Error(`이미지 형식을 지원하지 않습니다 (obj ${objn}, ${flt})`);
    const raw = Z.inflate(ubin(st));
    const pred = rx('/Predictor\\s+(\\d+)').exec(d);
    let plte = null, ct, nch, m = null;
    if (csm.startsWith('[/Indexed') || csm.startsWith('[ /Indexed')) {
      ct = 3; nch = 1;
      m = rx('(\\d+)\\s+0\\s+R\\s*\\]').exec(csm);
      if (m) plte = ubin(objs.get(parseInt(m[1])).st);
      else { const hx = rx('<([0-9A-Fa-f\\s]+)>').exec(csm); plte = hx ? ubin(hx[1].replace(/\s/g, '').match(/../g).map(h => String.fromCharCode(parseInt(h, 16))).join('')) : null; }
      const base = rx('/Indexed\\s*/(\\w+)').exec(csm);
      if (!base || base[1] !== 'DeviceRGB') throw new Error('Indexed 색상공간 형식 미지원');
      if (plte && plte.length && m && /\/Filter/.test(objs.get(parseInt(m[1])).d)) plte = Z.inflate(plte);
    } else if (csm.includes('DeviceRGB')) { ct = 2; nch = 3; }
    else if (csm.includes('DeviceGray')) { ct = 0; nch = 1; }
    else if (csm.includes('ICCBased')) {
      const n = parseInt(rx('/N\\s+(\\d+)').exec(objs.get(parseInt(rx('(\\d+)\\s+0\\s+R').exec(csm)[1])).d)[1]);
      ct = { 1: 0, 3: 2 }[n]; nch = n;
    } else throw new Error('색상공간 미지원: ' + csm);
    if (bpc !== 8) throw new Error('BitsPerComponent ' + bpc + ' 미지원');
    const stride = W * nch;
    let rows;
    const predOK = pred && parseInt(pred[1]) >= 10;
    if (predOK) rows = raw;
    else { rows = new Uint8Array(H * (stride + 1)); for (let y = 0; y < H; y++) rows.set(raw.subarray(y * stride, (y + 1) * stride), y * (stride + 1) + 1); }
    let alpha = null;
    if (smask) {
      const sm = objs.get(parseInt(smask[1]));
      alpha = Z.inflate(ubin(sm.st));
      if (/\/Predictor/.test(sm.d)) review('image', `smask predictor obj ${objn}`);
    }
    if (alpha && (ct === 0 || ct === 2) && !predOK) {
      const o = new Uint8Array(H * (W * (nch + 1) + 1)); let p = 0;
      for (let y = 0; y < H; y++) {
        o[p++] = 0;
        for (let x = 0; x < W; x++) { for (let k = 0; k < nch; k++) o[p++] = raw[y * stride + x * nch + k]; o[p++] = alpha[y * W + x]; }
      }
      rows = o; ct = ct === 0 ? 4 : 6;
    } else if (alpha) review('image', `alpha not merged obj ${objn}`);
    const chunk = (t, b) => { const tb = concat([ubin(t), b]); const L = new Uint8Array(4); dv(L).setUint32(0, b.length); const C = new Uint8Array(4); dv(C).setUint32(0, crc32(tb)); return concat([L, tb, C]); };
    const ih = new Uint8Array(13); const v = dv(ih); v.setUint32(0, W); v.setUint32(4, H); ih[8] = 8; ih[9] = ct;
    const parts = [new Uint8Array([0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]), chunk('IHDR', ih)];
    if (ct === 3) parts.push(chunk('PLTE', plte));
    parts.push(chunk('IDAT', Z.deflate(rows)), chunk('IEND', new Uint8Array(0)));
    const fn = `img${objn}.png`; IMAGES[fn] = concat(parts); return [fn, W, H];
  }
  // ---- geometry
  const COLX = 297.6; const colof = x => x < COLX ? 0 : 1;
  function components(segs, tol = 1.6) {
    const n = segs.length, par = [...Array(n).keys()];
    const f = i => { while (par[i] !== i) { par[i] = par[par[i]]; i = par[i]; } return i; };
    const bb = segs.map(s => [Math.min(s[0], s[2]) - tol, Math.min(s[1], s[3]) - tol, Math.max(s[0], s[2]) + tol, Math.max(s[1], s[3]) + tol]);
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const a = bb[i], b = bb[j];
      if (a[0] <= b[2] && b[0] <= a[2] && a[1] <= b[3] && b[1] <= a[3]) par[f(i)] = f(j);
    }
    const g = new Map();
    for (let i = 0; i < n; i++) { const r = f(i); if (!g.has(r)) g.set(r, []); g.get(r).push(segs[i]); }
    return [...g.values()];
  }
  function classifyPaths(segs) {
    const hs = segs.filter(s => Math.abs(s[1] - s[3]) < 0.3 && Math.abs(s[0] - s[2]) > 0.3);
    const vs = segs.filter(s => Math.abs(s[0] - s[2]) < 0.3 && Math.abs(s[1] - s[3]) > 0.3);
    let boxes = []; const tables = []; let unders = [];
    for (const comp of components(hs.concat(vs))) {
      const ch = comp.filter(s => Math.abs(s[1] - s[3]) < 0.3), cv = comp.filter(s => Math.abs(s[0] - s[2]) < 0.3);
      if (!cv.length) { if (ch.length === 1 && Math.abs(ch[0][2] - ch[0][0]) < 250) unders.push(ch[0]); else unders = unders.concat(ch); continue; }
      const xs = new Set(cv.map(s => pyRound(s[0])));
      const xmin = Math.min(...comp.map(s => Math.min(s[0], s[2]))), xmax = Math.max(...comp.map(s => Math.max(s[0], s[2])));
      const ymin = Math.min(...comp.map(s => Math.min(s[1], s[3]))), ymax = Math.max(...comp.map(s => Math.max(s[1], s[3])));
      const innerH = ch.filter(h => ymin + 2 < h[1] && h[1] < ymax - 2 && Math.abs(h[2] - h[0]) > 0.9 * (xmax - xmin));
      if (xs.size <= 2 && !innerH.length) boxes.push({ x0: xmin, x1: xmax, y0: ymin, y1: ymax, h: ch, v: cv });
      else tables.push({ x0: xmin, x1: xmax, y0: ymin, y1: ymax, h: ch, v: cv });
    }
    const lone = boxes.filter(b => b.x1 - b.x0 < 1 && Math.abs(b.x0 - COLX) > 3);
    boxes = boxes.filter(b => b.x1 - b.x0 >= 1);
    const used = new Set();
    lone.forEach((a, i) => lone.forEach((c, j) => {
      if (i === j || used.has(i) || used.has(j) || !(a.x0 < c.x0) || colof(a.x0) !== colof(c.x0)) return;
      if (c.x0 - a.x0 < 60) return;
      const y0 = Math.max(a.y0, c.y0), y1 = Math.min(a.y1, c.y1);
      if (y1 - y0 > 0.5 * Math.min(a.y1 - a.y0, c.y1 - c.y0)) { boxes.push({ x0: a.x0, x1: c.x0, y0, y1, h: [], v: a.v.concat(c.v) }); used.add(i); used.add(j); }
    }));
    return [boxes, tables, unders];
  }
  function gridCells(t) {
    const uniq = (vals, tol = 1.2) => { const o = []; for (const v of vals.slice().sort((a, b) => a - b)) if (!o.length || v - o[o.length - 1] > tol) o.push(v); return o; };
    let xs = uniq(t.v.map(s => s[0])), ys = uniq(t.h.map(s => s[1]));
    if (ys.length < 2 || ys[0] > t.y0 + 1.5) ys = uniq(ys.concat([t.y0]));
    if (ys[ys.length - 1] < t.y1 - 1.5) ys = uniq(ys.concat([t.y1]));
    if (xs[0] > t.x0 + 1.5) xs = uniq([t.x0].concat(xs));
    if (xs[xs.length - 1] < t.x1 - 1.5) xs = uniq(xs.concat([t.x1]));
    ys = ys.slice().reverse();
    const R = ys.length - 1, C = xs.length - 1;
    const vline = (x, ya, yb) => { const mid = (ya + yb) / 2; return t.v.some(s => Math.abs(s[0] - x) < 1.2 && Math.min(s[1], s[3]) - 1 <= mid && mid <= Math.max(s[1], s[3]) + 1); };
    const hline = (y, xa, xb) => { const mid = (xa + xb) / 2; return t.h.some(s => Math.abs(s[1] - y) < 1.2 && Math.min(s[0], s[2]) - 1 <= mid && mid <= Math.max(s[0], s[2]) + 1); };
    const owner = [...Array(R)].map(() => Array(C).fill(null)); const cells = [];
    for (let r = 0; r < R; r++) for (let c = 0; c < C; c++) {
      if (owner[r][c] !== null) continue;
      let cs = 1; while (c + cs < C && !vline(xs[c + cs], ys[r], ys[r + 1])) cs++;
      let rs = 1; while (r + rs < R && !hline(ys[r + rs], xs[c], xs[c + 1])) rs++;
      const cell = { r, c, rs, cs, x0: xs[c], x1: xs[c + cs], y1: ys[r], y0: ys[r + rs] };
      for (let rr = r; rr < r + rs; rr++) for (let cc = c; cc < c + cs; cc++) owner[rr][cc] = cells.length;
      cells.push(cell);
    }
    return { xs, ys, R, C, cells };
  }
  // ---- glyph lines
  function pageItems(pi) {
    const pn = pages[pi];
    const g = pageGlyphs(pn).filter(a => a.sz > 2).map(a => ({ x: a.x, y: a.y, t: a.t, sz: a.sz, f: a.bf.split('+').pop(), adv: a.adv }));
    for (const a of g) if (a.t === '\x00') { a.t = '□'; review('glyph', `p${pi + 1} 유니코드 정보가 없는 글자를 □로 넣음`, { page: pi, y: a.y, x: a.x }); }
    const [segs, imgs] = pagePathsImages(pn);
    const [boxes, tables, unders] = classifyPaths(segs);
    for (const u of unders) {
      const y = u[1], xa = Math.min(u[0], u[2]), xb = Math.max(u[0], u[2]);
      for (const gl of g) if (0.5 < gl.y - y && gl.y - y < 4 && xa - 1 <= gl.x && gl.x <= xb - 1) gl.ul = true;
    }
    return [g, boxes, tables, imgs];
  }
  function makeLines(glyphs) {
    const lines = new Map();
    for (const gl of glyphs) {
      const col = colof(gl.x); let key = null;
      for (const k of lines.keys()) if (k.col === col && Math.abs(k.y - gl.y) < 1.5) { key = k; break; }
      if (!key) { key = { col, y: gl.y }; lines.set(key, []); }
      lines.get(key).push(gl);
    }
    const out = [];
    for (const [k, gl] of lines) {
      gl.sort((a, b) => a.x - b.x);
      out.push({ col: k.col, y: k.y, x0: gl[0].x, g: gl, font: gl[0].f, sz: Math.max(...gl.map(a => a.sz)) });
    }
    return out;
  }
  function lineText(L, markUl = true) {
    let s = '', prev = null, ul = false;
    for (const a of L.g) {
      const t = a.t;
      if (prev !== null && t !== ' ' && !s.endsWith(' ')) {
        const gap = a.x - prev.x - prev.adv;
        if (gap > prev.sz * 0.2) s += gap < prev.sz * 0.9 ? ' ' : ' '.repeat(Math.max(1, pyRound(gap / (prev.sz * 0.3))));
      }
      if (markUl) {
        const aUl = !!a.ul && t !== ' ';
        if (aUl && !ul) { s += '⟦'; ul = true; }
        else if (!aUl && ul && t !== ' ') { const e = s.endsWith(' '); s = rstrip(s, ' ') + '⟧' + (e ? ' ' : ''); ul = false; }
      }
      s += t; prev = a;
    }
    if (ul) { const tr = s.length - rstrip(s, ' ').length; s = rstrip(s, ' ') + '⟧' + ' '.repeat(tr); }
    return s;
  }
  const plain = t => t.replace(/[⟦⟧]/g, '');
  function join2(at, aL, bt, bL) {
    if (at.endsWith(' ') || at.endsWith('\n')) return at + bt;
    const last = aL.g.filter(g => g.t !== ' ');
    if (last.length && last[last.length - 1].ul) {
      const key = plain(at).slice(-8) + '|' + plain(bt).slice(0, 8);
      if (Object.prototype.hasOwnProperty.call(OVR, key)) return at + OVR[key] + bt;
      review('ULJOIN', key, { page: aL.page, y: aL.y, col: aL.col, key });
      return at + bt;
    }
    return at + bt;
  }
  function lineEndX(L) { const nz = L.g.filter(g => g.t !== ' '); if (!nz.length) return L.g[0].x; const a = nz[nz.length - 1]; return a.x + a.adv; }
  // ---- flow assembly
  const pagesItems = []; const allBody = [];
  for (let pi = 0; pi < pages.length; pi++) {
    const [g, boxes, tables, imgs] = pageItems(pi);
    const banners = imgs.filter(im => im.w > 400 && (im.y > 700 || im.y + im.h < 90));
    const inBanner = a => banners.some(b => b.x - 1 <= a.x && a.x <= b.x + b.w + 1 && b.y - 1 <= a.y && a.y <= b.y + b.h + 1);
    const body = g.filter(a => 55 < a.y && a.y < 775 && !inBanner(a));
    for (const a of body) allBody.push(a);
    const tblElems = [];
    for (const t of tables) {
      const grid = gridCells(t);
      const tg = body.filter(a => t.x0 - 1 <= a.x && a.x <= t.x1 + 1 && t.y0 - 1 <= a.y && a.y <= t.y1 + 1);
      for (const a of tg) a.inTable = true;
      const cells = [];
      for (const c of grid.cells) {
        const cg = tg.filter(a => c.x0 - 1 <= a.x && a.x < c.x1 - 0.5 && c.y0 - 1 <= a.y && a.y < c.y1 - 0.5);
        const ls = makeLines(cg).sort((p, q) => q.y - p.y);
        const paras = []; let prevy = null;
        for (const L of ls) {
          const tx = lineText(L);
          if (prevy !== null && prevy - L.y <= 14.6 * L.sz / 9.12) paras[paras.length - 1] += tx; else paras.push(tx);
          prevy = L.y;
        }
        c.paras = paras.map(p => rstrip(p));
        const cen = ls.map(L => Math.abs((L.x0 - c.x0) - (c.x1 - lineEndX(L))) < 4);
        c.center = ls.length ? cen.filter(Boolean).length >= Math.max(1, cen.length * 0.6) : true;
        cells.push(c);
      }
      tblElems.push({ kind: 'table', col: colof((t.x0 + t.x1) / 2), y: t.y1, y0: t.y0, x0: t.x0, x1: t.x1, grid, cells, page: pi });
    }
    const lines = makeLines(body.filter(a => !a.inTable)).filter(L => L.g.some(x => x.t !== ' '));
    const bxs = [];
    for (const b of boxes) { if (b.x1 - b.x0 < 60 || b.y1 - b.y0 < 8) continue; bxs.push({ col: colof((b.x0 + b.x1) / 2), x0: b.x0, x1: b.x1, y0: b.y0, y1: b.y1 }); }
    const boxOf = (col, x, y) => {
      let best = null;
      bxs.forEach((b, k) => {
        if (b.col === col && b.x0 - 1 <= x && x <= b.x1 + 1 && b.y0 - 2 <= y && y <= b.y1 + 2) {
          const ar = (b.x1 - b.x0) * (b.y1 - b.y0);
          if (best === null || ar < (bxs[best].x1 - bxs[best].x0) * (bxs[best].y1 - bxs[best].y0)) best = k;
        }
      });
      return best;
    };
    const elems = [];
    for (const L of lines) { L.box = boxOf(L.col, L.x0, L.y); L.page = pi; }
    for (let k = 0; k < bxs.length; k++) {
      const inb = lines.filter(L => L.box === k).sort((p, q) => q.y - p.y);
      if (inb.length && /^[<〈][^<>〈〉]{1,10}[>〉]$/.test(pyStrip(plain(lineText(inb[0], false))))) inb[0].title = true;
    }
    for (const L of lines) elems.push({ kind: 'line', col: L.col, y: L.y, L });
    for (const t of tblElems) for (const c of t.cells) if (!c.items) c.items = [];
    for (const im of imgs) {
      if (banners.includes(im) || im.obj === null) continue;
      const cx = im.x + im.w / 2, cy = im.y + im.h / 2;
      for (const t of tblElems) {
        for (const c of t.cells) if (c.x0 <= cx && cx <= c.x1 && c.y0 <= cy && cy <= c.y1) { c.items.push({ im, page: pi }); im.inTable = true; break; }
        if (im.inTable) break;
      }
    }
    for (const im of imgs) {
      if (im.inTable || banners.includes(im) || im.obj === null) continue;
      const col = colof(im.x + im.w / 2);
      elems.push({ kind: 'image', col, y: im.y + im.h, im, page: pi, box: boxOf(col, im.x + im.w / 2, im.y + im.h / 2) });
    }
    for (const t of tblElems) { t.box = boxOf(t.col, (t.x0 + t.x1) / 2, (t.y + t.y0) / 2); elems.push(t); }
    elems.sort((a, b) => (a.col - b.col) || (b.y - a.y));
    for (const e of elems) { e.page = pi; e.boxkey = [pi, e.kind !== 'line' ? (e.box === undefined ? null : e.box) : e.L.box]; }
    pagesItems.push({ elems, boxes: bxs });
  }
  const bkEq = (a, b) => a[0] === b[0] && a[1] === b[1];
  const seq = []; for (const P of pagesItems) for (const e of P.elems) seq.push(e);
  let ansStart = seq.findIndex(e => e.kind === 'line' && /^\d+\)\s*\[정답\]/.test(lineText(e.L, false)));
  if (ansStart < 0) throw new Error('정답 및 해설 부분("1)[정답]")을 찾지 못했습니다. 지원하는 시험지 양식의 PDF인지 확인해 주세요.');
  let qseq = seq.slice(0, ansStart); const aseq = seq.slice(ansStart);
  for (const e of qseq) if (e.kind === 'line' && e.page >= aseq[0].page) for (const g of e.L.g) g.excl = true;   // date / ID lines on the answer page
  // answers
  let atext = '', prevL = null;
  for (const e of aseq) {
    if (e.kind !== 'line') { if (e.kind === 'image' && e.im.w > 400) continue; review('answers', `정답 영역의 텍스트 아닌 요소: ${e.kind} p${e.page + 1}`); continue; }
    const t = lineText(e.L, false);
    atext = (prevL !== null && atext) ? join2(atext, prevL, t, e.L) : atext + t;
    prevL = e.L;
  }
  const ANS = {};
  for (const m of atext.matchAll(/(\d+)\)\s*\[정답\]\s*([\s\S]*?)\s*\[해설\]\s*([\s\S]*?)\s*(?=\d+\)\s*\[정답\]|$)/g))
    ANS[parseInt(m[1])] = ' [정답] ' + pyStrip(m[2]) + ' [해설] ' + pyStrip(m[3]);
  for (const m of atext.matchAll(/(\d+)\)\s*\[정답\]/g)) if (!(parseInt(m[1]) in ANS)) review('answers', `${m[1]}번 정답에 [해설]이 없음`);
  // question/passage flow
  const IS_STEM = /^(\d+)\.\s*([\s\S]*)$/;
  const isBold = L => L.font.includes('Bold') || L.font.includes('Malgun');
  const images = new Map();
  function imgRef(e) {
    const obj = e.im.obj;
    if (!images.has(obj)) { const [fn, W, H] = exportImage(obj); images.set(obj, { file: fn, W, H }); }
    const im = e.im;
    if (im.clip) {
      const [cx0, cy0, cx1, cy1] = im.clip;
      if (cx0 > im.x + 2 || cy0 > im.y + 2 || cx1 < im.x + im.w - 2 || cy1 < im.y + im.h - 2) review('image', `p${e.page + 1}: PDF에서 일부만 보이도록 잘린 이미지 — 원본 전체를 넣음`, { page: e.page });
    }
    const I = images.get(obj);
    return { image: I.file, px: [I.W, I.H], disp: [pyRound(im.w * 100), pyRound(im.h * 100)] };
  }
  function tableSpec(e) {
    const g = e.grid;
    const widths = []; for (let i = 0; i < g.C; i++) widths.push(pyRound((g.xs[i + 1] - g.xs[i]) * 100));
    const heights = []; for (let i = 0; i < g.R; i++) heights.push(pyRound((g.ys[i] - g.ys[i + 1]) * 100));
    return { kind: 'table', widths, heights, cells: e.cells.map(c => ({ r: c.r, c: c.c, rs: c.rs, cs: c.cs, paras: c.paras.concat((c.items || []).map(imgRef)), center: c.center })) };
  }
  function groupParas(lines, stem = false) {
    const paras = []; let prev = null;
    for (const L of lines) {
      const tx = lineText(L, !stem);
      let cont = prev !== null && prev.col === L.col && prev.page === L.page && 0 < prev.y - L.y && prev.y - L.y <= 14.6 * L.sz / 9.12;
      if (prev !== null && (prev.page !== L.page || prev.col !== L.col)) cont = null;
      if (cont === null) cont = !!L.cont;
      if (CIRC.includes(lstrip(tx).slice(0, 1)) && lstrip(tx).length || L.title || (prev !== null && prev.title)) cont = false;
      if (cont && paras.length) {
        const pt = paras[paras.length - 1];
        if (prev.short) paras[paras.length - 1] = rstrip(pt, ' ') + '\n' + tx;
        else paras[paras.length - 1] = join2(pt, prev, tx, L);
      } else paras.push(tx);
      prev = L;
    }
    return paras.map(p => rstrip(p.replace(/⟧\s*⟦/g, m => m.replace(/[⟧⟦]/g, ''))));
  }
  const ANS_PAGE = aseq[0].page;
  for (const e of qseq) if (e.page >= ANS_PAGE && e.kind === 'line' && IS_STEM.test(pyStrip(lineText(e.L, false))) && isBold(e.L)) review('numbers', '정답 페이지에 있는 문항이 빠졌을 수 있음: ' + lineText(e.L, false).slice(0, 40));
  qseq = qseq.filter(e => e.page < ANS_PAGE);
  for (const P of pagesItems) {
    const ls = P.elems.filter(e => e.kind === 'line').map(e => e.L);
    const rr = new Map(); const rk = L => L.col + ':' + L.box;
    for (const L of ls) rr.set(rk(L), Math.max(rr.has(rk(L)) ? rr.get(rk(L)) : 0, lineEndX(L)));
    const by = ls.slice().sort((a, b) => (a.col - b.col) || (b.y - a.y));
    for (let k = 0; k + 1 < by.length; k++) {
      const a = by[k], b = by[k + 1];
      if (a.col === b.col && a.box === b.box && 0 < a.y - b.y && a.y - b.y <= 14.6 * b.sz / 9.12) {
        const gap = rr.get(rk(a)) - lineEndX(a);
        const at = rstrip(lineText(a, false)), bt = lineText(b, false);
        const wordWrap = (isAsciiAlnum(at.slice(-1)) && isAsciiAlnum(bt.slice(0, 1))) || (bt.length > 0 && ')].,’”」』:;!?·…'.includes(bt[0]));
        if (a.page >= ANS_PAGE) continue;
        if (gap > 1.6 * a.sz && !wordWrap && !a.title && !isBold(a) && !(pyStrip(at).length && CIRC.includes(pyStrip(at)[0]))) {
          a.short = true;
          review('linebreak', `p${a.page + 1} 줄 끝이 짧아 줄바꿈으로 처리: …${lineText(a, false).slice(-30)}`, { page: a.page, y: a.y, col: a.col });
        }
      }
    }
  }
  const regionLines = L => pagesItems[L.page].elems.filter(e => e.kind === 'line' && e.L.col === L.col && e.L.box === L.box).map(e => e.L);
  function indentStyle(L) {
    const ls = regionLines(L).sort((p, q) => q.y - p.y);
    const firsts = [], conts = [];
    for (let k = 0; k + 1 < ls.length; k++) {
      const a = ls[k], b = ls[k + 1];
      const bs = pyStrip(lineText(b, false)); if (bs.length && CIRC.includes(bs[0])) continue;
      (0 < a.y - b.y && a.y - b.y <= 14.6 * b.sz / 9.12 ? conts : firsts).push(b.x0);
    }
    if (!firsts.length || !conts.length) return [0, null];
    const f = median(firsts), c = median(conts);
    return [f - c > 2 ? 1 : c - f > 2 ? -1 : 0, c];
  }
  function crossCont(P, L) {
    const pt = lineText(P, false);
    const punct = /[.?!"”’):]$/.test(rstrip(pt));
    if (P.short) return false;
    const [st, cx] = indentStyle(L); let res;
    if (st === 1) res = !(L.x0 > cx + 2);
    else if (st === -1) res = cx !== null ? L.x0 > cx - 2 : !punct;
    else res = !punct;
    if ((punct && res) || (!punct && !res)) review('crosscol', `p${L.page + 1} ${res ? '이어 붙임' : '새 문단'}: …${pt.slice(-15)} | ${lineText(L, false).slice(0, 15)}…`, { page: L.page, y: L.y, col: L.col });
    return res;
  }
  const DOC = []; let state = null, cur = null, pending = [];
  function flush() {
    if (!pending.length) return;
    if (state === 'passage') for (const p of groupParas(pending)) cur.items.push({ text: p });
    else if (state === 'q') cur.items.push({ kind: 'lines', box: pending[0].boxkey, paras: groupParas(pending) });
    else review('orphan', '첫 문항 앞의 텍스트: ' + pending.map(L => lineText(L, false)).join(' / ').slice(0, 120));
    pending = [];
  }
  let i = 0;
  while (i < qseq.length) {
    const e = qseq[i];
    if (e.kind === 'line') {
      const L = e.L; L.boxkey = [e.page, L.box]; const tx = pyStrip(lineText(L, false));
      if (tx.startsWith('※')) { flush(); state = 'passage'; cur = { kind: 'passage', head: rstrip(lineText(L, false)), items: [] }; DOC.push(cur); i++; continue; }
      const m = IS_STEM.exec(tx);
      if (m && isBold(L) && L.box === null && L.sz >= 9) {
        flush();
        const st = [L]; let j = i + 1;
        while (j < qseq.length && qseq[j].kind === 'line' && qseq[j].L.font.includes('Bold') && qseq[j].L.box === null
          && !IS_STEM.test(pyStrip(lineText(qseq[j].L, false))) && !pyStrip(lineText(qseq[j].L, false)).startsWith('※')) { st.push(qseq[j].L); j++; }
        let raw = lineText(st[0], false);
        for (let k = 0; k + 1 < st.length; k++) raw = join2(raw, st[k], lineText(st[k + 1], false), st[k + 1]);
        raw = pyStrip(raw);
        const mm = /^(\d+)\.\s*([\s\S]*)$/.exec(raw);
        const stem = mm[1] + '. ' + pyStrip(mm[2]);
        state = 'q'; cur = { kind: 'q', num: parseInt(mm[1]), stem, items: [] }; DOC.push(cur); i = j; continue;
      }
      if (pending.length) {
        const P = pending[pending.length - 1];
        const same = (P.box === null) === (L.box === null);
        if ((P.page !== L.page || P.col !== L.col) && same) L.cont = crossCont(P, L);
        else if (!bkEq(P.boxkey, L.boxkey) && state === 'q') flush();
      }
      pending.push(L); i++; continue;
    }
    flush();
    if (state === null) { review('orphan', `첫 문항 앞의 ${e.kind} p${e.page + 1}`); i++; continue; }
    if (e.kind === 'image') { const it = imgRef(e); it.box = e.boxkey; cur.items.push(it); }
    else if (e.kind === 'table') { const it = tableSpec(e); it.box = e.boxkey; cur.items.push(it); }
    i++;
  }
  flush();
  // organise
  const normChoice = p => p[0] + ' ' + lstrip(p.slice(1));
  const stripBox = it => { const o = {}; for (const k in it) if (k !== 'box') o[k] = it[k]; return o; };
  const TITLE_RE = /^[<〈][^<>〈〉]{1,10}[>〉]$/;
  function tableTitle(t) {
    if (t.kind !== 'table') return [null, t];
    const r0 = t.cells.filter(c => c.r === 0);
    if (r0.length === 1 && r0[0].paras.length === 1 && typeof r0[0].paras[0] === 'string' && TITLE_RE.test(pyStrip(plain(r0[0].paras[0]))) && t.heights.length > 1) {
      const nt = Object.assign({}, t); nt.heights = t.heights.slice(1);
      nt.cells = t.cells.filter(c => c.r > 0).map(c => Object.assign({}, c, { r: c.r - 1 }));
      return [pyStrip(plain(r0[0].paras[0])), nt];
    }
    return [null, t];
  }
  const TITLES = { '<보기>': '<보 기>', '<조건>': '<조 건>', '〈보기〉': '<보 기>', '〈조건〉': '<조 건>' };
  const OUTDOC = [];
  for (const b of DOC) {
    if (b.kind === 'passage') {
      const items = [];
      for (const it of b.items) { if ('text' in it) { if (pyStrip(it.text)) items.push(it.text); } else items.push(stripBox(it)); }
      OUTDOC.push({ kind: 'passage', head: b.head, paras: items }); continue;
    }
    const q = { kind: 'q', num: b.num, stem: b.stem, items: [] };
    const groups = [];
    for (const it of b.items) {
      const key = it.box; const inbox = key !== undefined && key !== null && key[1] !== null;
      const last = groups[groups.length - 1];
      if (last && last.inbox && inbox && bkEq(last.key, key)) last.items.push(it); else groups.push({ key, inbox, items: [it] });
    }
    let nch = 0;
    for (const gr of groups) {
      if (gr.inbox) {
        const paras = []; let title = null;
        for (const it of gr.items) {
          if (it.kind === 'lines') {
            for (const p of it.paras) {
              const pt = pyStrip(p.replace(/[⟦⟧]/g, ''));
              if (title === null && !paras.length && TITLE_RE.test(pt)) { title = pt; continue; }
              paras.push(p);
            }
          } else {
            const [tt_, nt] = tableTitle(stripBox(it));
            if (tt_ && title === null && !paras.length) { title = tt_; review('box', `${b.num}번: 표 첫 줄을 박스 제목으로 사용 ${tt_}`); }
            paras.push(tt_ ? nt : stripBox(it));
          }
        }
        if (title === null) review('box', `${b.num}번: 제목 없는 박스 → 테두리 박스로 처리`);
        const tt = title === null ? null : (TITLES[title] || title);
        if (title && tt !== '<보 기>' && tt !== '<조 건>') review('box', `${b.num}번: 박스 제목 ${title}`);
        if (nch) review('order', `${b.num}번: 선택지 뒤에 박스가 있음`);
        q.items.push({ kind: 'box', title: tt, paras });
      } else {
        for (const it of gr.items) {
          if (it.kind === 'lines') {
            for (const p of it.paras) {
              const pt = pyStrip(p);
              if (pt.length && CIRC.includes(pt[0])) {
                const parts = pt.split(/\s+(?=[①②③④⑤])/);
                if (parts.length > 1) review('choices', `${b.num}번: 한 줄의 여러 선택지를 나눔: ${pt.slice(0, 60)}`);
                for (const x of parts) { q.items.push({ kind: 'choice', text: normChoice(x) }); nch++; }
              } else if (q.items.length && q.items[q.items.length - 1].kind === 'choice') {
                q.items[q.items.length - 1].text += '\n' + p;
                review('choicecont', `${b.num}번: 선택지가 여러 줄로 이어짐: ${p.slice(0, 40)}`);
              } else { q.items.push({ kind: 'para', text: p }); review('extra', `${b.num}번: 문항 아래 별도 문단: ${p.slice(0, 60)}`); }
            }
          } else if (it.kind === 'table' && it.cells.length >= 2 && it.cells.every(c => c.r === 0) && it.cells[0].paras.length === 1
            && typeof it.cells[0].paras[0] === 'string' && pyStrip(it.cells[0].paras[0]).length === 1 && CIRC.includes(pyStrip(it.cells[0].paras[0]))) {
            const rest = []; for (const c of it.cells.slice(1)) for (const x of c.paras) rest.push(x);
            const txt = rest.filter(x => typeof x === 'string').join(' ');
            q.items.push({ kind: 'choice', text: pyStrip(it.cells[0].paras[0]) + ' ' + txt, images: rest.filter(x => typeof x !== 'string') });
            nch++; review('choices', `${b.num}번: 칸 안의 선택지를 일반 선택지로 변환 ${it.cells[0].paras[0]}`);
          } else {
            if (nch) review('order', `${b.num}번: 선택지 뒤에 ${it.kind || 'image'}`);
            const [tt_, nt] = tableTitle(stripBox(it));
            if (tt_) { review('box', `${b.num}번: 제목 줄이 있는 표 → ${tt_} 박스`); q.items.push({ kind: 'box', title: TITLES[tt_] || tt_, paras: [nt] }); }
            else q.items.push(stripBox(it));
          }
        }
      }
    }
    q.nchoices = nch; OUTDOC.push(q);
  }
  const nums = OUTDOC.filter(b => b.kind === 'q').map(b => b.num);
  const sortedNums = nums.slice().sort((a, b) => a - b);
  if (sortedNums.some((n, k) => n !== k + 1)) review('numbers', '문항 번호가 1부터 차례대로가 아님: ' + nums.join(','));
  const miss = nums.filter(n => !(n in ANS)); if (miss.length) review('answers', '정답이 없는 문항: ' + miss.join(','));
  for (const b of OUTDOC) {
    if (b.kind === 'q' && !b.nchoices && !/쓰시오|서술하시오|쓰고|쓰라|고쳐|완성하시오|답하시오/.test(b.stem)) review('choices', `${b.num}번: 선택지가 없음`);
    if (b.kind === 'q' && b.nchoices && b.nchoices !== 5) review('choices', `${b.num}번: 선택지가 ${b.nchoices}개`);
  }
  const tm = /\] (.*?)_중2/.exec(filename || '');
  const title = tm ? tm[1] : (filename || '').replace(/\.pdf$/i, '');
  const ans = {}; for (const k of Object.keys(ANS)) ans[k] = ANS[k];
  const expected = (/\[(\d+)문제\]/.exec(filename || '') || [])[1];
  const bodyText = allBody.filter(a => !a.excl).map(a => a.t).join('').replace(/(\d+)\)\s*\[정답\]/g, '[정답]');
  return { title, doc: OUTDOC, ans, review: REVIEW, images: IMAGES, pages: pages.length, expected: expected ? parseInt(expected) : null, bodyText,
           counts: { questions: nums.length, answers: Object.keys(ANS).length, passages: OUTDOC.filter(b => b.kind === 'passage').length, images: images.size } };
}

// ------------------------------------------------------------------ CFB read/write, records
function cfbRead(u8) {
  const v = dv(u8);
  const ss = 1 << v.getUint16(0x1E, true), mss = 1 << v.getUint16(0x20, true);
  const nfat = v.getUint32(0x2C, true), dirstart = v.getUint32(0x30, true), cutoff = v.getUint32(0x38, true), mfstart = v.getUint32(0x3C, true), dfstart = v.getUint32(0x44, true), ndf = v.getUint32(0x48, true);
  const sec = i => u8.subarray(512 + i * ss, 512 + (i + 1) * ss);
  const difat = []; for (let k = 0; k < 109; k++) difat.push(v.getUint32(0x4C + 4 * k, true));
  let d = dfstart;
  for (let k = 0; k < ndf; k++) { const s = dv(sec(d)); const n = ss / 4 - 1; for (let q = 0; q < n; q++) difat.push(s.getUint32(4 * q, true)); d = s.getUint32(n * 4, true); }
  const fat = []; for (const f of difat.slice(0, nfat)) { const s = dv(sec(f)); for (let q = 0; q < ss / 4; q++) fat.push(s.getUint32(4 * q, true)); }
  const chain = s => { const o = []; while (s < 0xFFFFFFFA) { o.push(s); s = fat[s]; } return o; };
  const dirdata = concat(chain(dirstart).map(sec)); const dd = dv(dirdata);
  const raw = [];
  for (let o = 0; o < dirdata.length; o += 128) {
    const nl = dd.getUint16(o + 0x40, true);
    if (!nl) { raw.push(null); continue; }
    let name = ''; for (let k = 0; k < nl - 2; k += 2) name += String.fromCharCode(dd.getUint16(o + k, true));
    raw.push({ name, typ: dirdata[o + 0x42], l: dd.getInt32(o + 0x44, true), r: dd.getInt32(o + 0x48, true), c: dd.getInt32(o + 0x4C, true), st: dd.getUint32(o + 0x74, true), sz: dd.getUint32(o + 0x78, true) });
  }
  const root = raw[0]; const ms = concat(chain(root.st).map(sec)).subarray(0, root.sz);
  const mf = []; for (const k of chain(mfstart)) { const s = dv(sec(k)); for (let q = 0; q < ss / 4; q++) mf.push(s.getUint32(4 * q, true)); }
  const get = e => {
    if (e.sz < cutoff) { const parts = []; let s = e.st; while (s < 0xFFFFFFFA) { parts.push(ms.subarray(s * mss, (s + 1) * mss)); s = mf[s]; } return concat(parts).subarray(0, e.sz); }
    return concat(chain(e.st).map(sec)).subarray(0, e.sz);
  };
  const out = {};
  const walk = (i, prefix) => {
    if (i < 0 || i >= raw.length || !raw[i]) return;
    const e = raw[i]; walk(e.l, prefix); walk(e.r, prefix);
    if (e.typ === 2) out[prefix + e.name] = get(e); else if (e.typ === 1) walk(e.c, prefix + e.name + '/'); else if (e.typ === 5) walk(e.c, '');
  };
  walk(0, ''); return out;
}
function cfbWrite(streams) {
  const SS = 512, MSS = 64, CUT = 4096, FREE = 0xFFFFFFFF, ENDC = 0xFFFFFFFE, FATSECT = 0xFFFFFFFD;
  const root = { name: 'Root Entry', type: 5, children: new Map() };
  for (const path of Object.keys(streams)) {
    const parts = path.split('/'); let node = root;
    for (const p of parts.slice(0, -1)) { if (!node.children.has(p)) node.children.set(p, { name: p, type: 1, children: new Map() }); node = node.children.get(p); }
    node.children.set(parts[parts.length - 1], { name: parts[parts.length - 1], type: 2, data: streams[path] });
  }
  const entries = [];
  const cmp = (a, b) => (a.name.length - b.name.length) || (a.name.toUpperCase() < b.name.toUpperCase() ? -1 : a.name.toUpperCase() > b.name.toUpperCase() ? 1 : 0);
  const add = node => {
    node.id = entries.length; entries.push(node);
    if (node.type === 1 || node.type === 5) {
      const kids = [...node.children.values()].sort(cmp);
      for (const k of kids) add(k);
      const bst = lst => { if (!lst.length) return -1; const m = lst.length >> 1; lst[m].left = bst(lst.slice(0, m)); lst[m].right = bst(lst.slice(m + 1)); return lst[m].id; };
      node.child = bst(kids);
    }
  };
  add(root);
  const miniParts = []; let miniLen = 0; const minifat = [];
  for (const e of entries) {
    if (e.type === 2 && e.data.length < CUT && e.data.length > 0) {
      const n = Math.ceil(e.data.length / MSS); e.start = minifat.length;
      for (let k = 0; k < n - 1; k++) minifat.push(minifat.length + 1); minifat.push(ENDC);
      const pad = new Uint8Array(n * MSS); pad.set(e.data); miniParts.push(pad); miniLen += pad.length;
    } else if (e.type === 2 && e.data.length === 0) e.start = ENDC;
  }
  const sectors = [], fat = [];
  const alloc = data => {
    if (!data.length) return ENDC;
    const n = Math.ceil(data.length / SS), start = sectors.length;
    for (let k = 0; k < n; k++) { const s = new Uint8Array(SS); s.set(data.subarray(k * SS, Math.min((k + 1) * SS, data.length))); sectors.push(s); fat.push(k < n - 1 ? start + k + 1 : ENDC); }
    return start;
  };
  for (const e of entries) if (e.type === 2 && e.data.length >= CUT) e.start = alloc(e.data);
  const mini = concat(miniParts);
  root.start = mini.length ? alloc(mini) : ENDC; root.size = mini.length;
  const mfb = new Uint8Array(minifat.length * 4); minifat.forEach((x, k) => dv(mfb).setUint32(4 * k, x, true));
  const mfStart = minifat.length ? alloc(mfb) : ENDC; const mfCount = Math.ceil(mfb.length / SS);
  let dlen = entries.length * 128; while (dlen % SS) dlen += 128;
  const d = new Uint8Array(dlen); const dd = dv(d);
  entries.forEach((e, k) => {
    const o = k * 128; for (let q = 0; q < e.name.length; q++) dd.setUint16(o + 2 * q, e.name.charCodeAt(q), true);
    dd.setUint16(o + 0x40, (e.name.length + 1) * 2, true); d[o + 0x42] = e.type; d[o + 0x43] = 1;
    dd.setInt32(o + 0x44, e.left === undefined ? -1 : e.left, true); dd.setInt32(o + 0x48, e.right === undefined ? -1 : e.right, true); dd.setInt32(o + 0x4C, e.child === undefined ? -1 : e.child, true);
    if (e.type === 2) { dd.setUint32(o + 0x74, e.start, true); dd.setUint32(o + 0x78, e.data.length, true); }
    else if (e.type === 5) { dd.setUint32(o + 0x74, root.start, true); dd.setUint32(o + 0x78, root.size, true); }
  });
  for (let o = entries.length * 128; o < dlen; o += 128) { dd.setInt32(o + 0x44, -1, true); dd.setInt32(o + 0x48, -1, true); dd.setInt32(o + 0x4C, -1, true); }
  const dirStart = alloc(d);
  let nfat = 0;
  for (;;) { const need = Math.ceil((sectors.length + nfat) / (SS / 4)); if (need <= nfat) break; nfat = need; }
  if (nfat > 109) throw new Error('파일이 너무 큽니다');
  const fatStart = sectors.length;
  for (let k = 0; k < nfat; k++) fat.push(FATSECT);
  while (fat.length < nfat * (SS / 4)) fat.push(FREE);
  const fb = new Uint8Array(fat.length * 4); fat.forEach((x, k) => dv(fb).setUint32(4 * k, x, true));
  for (let k = 0; k < nfat; k++) sectors.push(fb.subarray(k * SS, (k + 1) * SS));
  const h = new Uint8Array(512); const hv = dv(h);
  h.set([0xD0, 0xCF, 0x11, 0xE0, 0xA1, 0xB1, 0x1A, 0xE1], 0);
  hv.setUint16(0x18, 0x3E, true); hv.setUint16(0x1A, 3, true); hv.setUint16(0x1C, 0xFFFE, true); hv.setUint16(0x1E, 9, true); hv.setUint16(0x20, 6, true);
  hv.setUint32(0x2C, nfat, true); hv.setUint32(0x30, dirStart, true); hv.setUint32(0x38, CUT, true);
  hv.setUint32(0x3C, mfStart, true); hv.setUint32(0x40, mfCount, true); hv.setUint32(0x44, ENDC, true); hv.setUint32(0x48, 0, true);
  for (let k = 0; k < 109; k++) hv.setUint32(0x4C + 4 * k, k < nfat ? fatStart + k : FREE, true);
  return concat([h].concat(sectors));
}
function recsParse(b) {
  const v = dv(b); let o = 0; const out = [];
  while (o < b.length) {
    const h = v.getUint32(o, true); o += 4; const tag = h & 0x3FF, lvl = (h >>> 10) & 0x3FF; let size = h >>> 20;
    if (size === 0xFFF) { size = v.getUint32(o, true); o += 4; }
    out.push([tag, lvl, b.slice(o, o + size)]); o += size;
  }
  return out;
}
function recsBuild(recs) {
  const parts = [];
  for (const [tag, lvl, p] of recs) {
    if (p.length >= 0xFFF) { parts.push(u32((tag | (lvl << 10) | (0xFFF << 20)) >>> 0), u32(p.length)); }
    else parts.push(u32((tag | (lvl << 10) | (p.length << 20)) >>> 0));
    parts.push(p);
  }
  return concat(parts);
}

// ------------------------------------------------------------------ builder (build2.py)
function buildHwp(A) {
  const tpl = cfbRead(b64(DATA.template));
  const sec = recsParse(Z.inflateRaw(tpl['BodyText/Section0']));
  const docinfo = recsParse(Z.inflateRaw(tpl['DocInfo']));
  const PARA_HEADER = 66, PARA_TEXT = 67, PARA_CHAR_SHAPE = 68, PARA_LINE_SEG = 69, CTRL_HEADER = 71, LIST_HEADER = 72, TABLE = 77;
  const dec16 = p => { let s = ''; for (let k = 0; k + 1 < p.length; k += 2) s += String.fromCharCode(p[k] | (p[k + 1] << 8)); return s; };
  const findText = prefix => { for (let k = 0; k < sec.length; k++) if (sec[k][0] === PARA_TEXT && dec16(sec[k][2]).startsWith(prefix)) return k - 1; throw new Error(prefix); };
  const subtree = k => { const lvl = sec[k][1]; let j = k + 1; while (j < sec.length && sec[j][1] > lvl) j++; return sec.slice(k, j).map(r => [r[0], r[1], r[2]]); };
  const head4 = p => String.fromCharCode(p[0], p[1], p[2], p[3]);
  const SEC_PARA = subtree(0);
  const q1 = findText('1. 윗글');
  const EN = subtree(q1);
  const enI = EN.findIndex(r => r[0] === CTRL_HEADER && head4(r[2]) === '  ne');
  const EN_CTRL = EN.slice(enI);
  const BOGI = subtree(q1 + subtree(q1).length);
  const PIC_I = sec.map((r, k) => (r[0] === CTRL_HEADER && head4(r[2]) === ' osg' && r[1] === 1) ? k : -1).filter(k => k >= 0)[1];
  const PIC = subtree(PIC_I);
  const clone = recs => recs.map(r => [r[0], r[1], r[2].slice()]);
  const shift = (recs, dd) => recs.map(r => [r[0], r[1] + dd, r[2]]);
  // line segments
  const LS_SPACING = { 2: 272 }, LS_START = { 12: 500 }, LS_INDENT = { 12: 700, 2: -1310 };
  function linesegs(ps, avail, chars, objH) {
    const ind = LS_INDENT[ps] || 0;
    if (ps === 12) avail -= 1000;
    const wordMode = ps === 1 || ps === 132;
    const cap = n => ind > 0 ? avail - (n === 0 ? ind : 0) : ind < 0 ? avail - (n > 0 ? -ind : 0) : avail;
    const starts = [0]; let cur = 0, i = 0, ls0 = 0;
    while (i < chars.length) {
      const [pos, c, w] = chars[i];
      if (c === '\n') { if (i + 1 < chars.length) { starts.push(chars[i + 1][0]); ls0 = i + 1; } cur = 0; i++; continue; }
      if (c !== ' ' && cur + w > cap(starts.length - 1) && i > ls0) {
        let j = i;
        if (wordMode) { while (j > ls0 && chars[j - 1][1] !== ' ') j--; if (j === ls0) j = i; }
        else if (isAsciiAlnum(c)) { while (j > ls0 && isAsciiAlnum(chars[j - 1][1])) j--; if (j === ls0) j = i; }
        starts.push(chars[j][0]); ls0 = j;
        cur = 0; for (let k = j; k < i; k++) cur += chars[k][2]; continue;
      }
      cur += w; i++;
    }
    const h = objH || 900, sp = LS_SPACING[ps] !== undefined ? LS_SPACING[ps] : 540;
    const out = new Uint8Array(36 * starts.length); const v = dv(out);
    starts.forEach((s, k) => {
      let flags = 0x00060000; if ((ind > 0 && k === 0) || (ind < 0 && k > 0)) flags |= 0x00100000;
      const o = 36 * k;
      v.setUint32(o, s, true); v.setInt32(o + 4, k * (h + sp), true); v.setInt32(o + 8, h, true); v.setInt32(o + 12, h, true);
      v.setInt32(o + 16, Math.trunc(h * 0.85), true); v.setInt32(o + 20, sp, true); v.setInt32(o + 24, LS_START[ps] || 0, true); v.setInt32(o + 28, avail, true); v.setUint32(o + 32, flags >>> 0, true);
    });
    return [out, starts.length];
  }
  const cw = (c, cs) => {
    const ls = (cs === 37 || cs === 143) ? -45 : 0;
    if (c === ' ') return 450 + ls;
    if ('‘’“”'.includes(c)) return 250 + ls;
    if (c.charCodeAt(0) < 128) { const a = DATA.adv[c] !== undefined ? DATA.adv[c] : 500; return (a < 0 ? 500 : a) * 0.95 + ls; }
    return 855 + ls;
  };
  const CTRL_CHARS = { 'secd': 2, 'cold': 2, 'tbl ': 11, 'gso ': 11, 'en  ': 17, 'atno': 18 };
  const DEF_CS = 34, CS_BODY = 34, CS_PASS = 37, CS_EN = 36, CS_BOLD = 142, CS_UL = 143;
  const PS_BODY = 3, PS_PASS = 12, PS_EN = 2, PS_CENTER = 1;
  function para(level, ps, style, items, last = false, width = 42520) {
    const text = []; const csRuns = []; let mask = 0; let ctrlRecs = []; let pos = 0; const chars = []; let objH = null;
    for (const it of items) {
      if (it[0] === 'ctrl') {
        const [, cid, recs] = it; const code = CTRL_CHARS[cid];
        const idb = ubin(cid.split('').reverse().join(''));
        text.push(concat([u16(code), idb, new Uint8Array(8), u16(code)]));
        if (cid === 'tbl ' || cid === 'gso ') { const v = dv(recs[0][2]); const ow = v.getUint32(16, true); objH = v.getUint32(20, true); chars.push([pos, '\x00', ow]); }
        else if (cid === 'atno') chars.push([pos, '\x00', 900]);
        else if (cid === 'en  ') chars.push([pos, '\x00', 0]);
        mask |= 1 << code; pos += 8; ctrlRecs = ctrlRecs.concat(recs);
      } else {
        const [cs, s] = it; if (!s) continue;
        if (!csRuns.length || csRuns[csRuns.length - 1][1] !== cs) csRuns.push([pos, cs]);
        for (const c of s) {
          if (c === '\n') { text.push(u16(10)); mask |= 1 << 10; } else text.push(utf16(c));
          chars.push([pos, c, cw(c, cs)]); pos += 1;
        }
      }
    }
    const n = pos + 1;
    if (!csRuns.length) csRuns.push([0, items.length && items[0][0] !== 'ctrl' ? items[0][0] : DEF_CS]);
    if (csRuns[0][0] !== 0) csRuns[0] = [0, csRuns[0][1]];
    const [lsb, nls] = linesegs(ps, width, chars, objH);
    const hdr = concat([u32((n | (last ? 0x80000000 : 0)) >>> 0), u32(mask >>> 0), u16(ps), new Uint8Array([style, 0]), u16(csRuns.length), u16(0), u16(nls), u32(0)]);
    const recs = [[PARA_HEADER, level, hdr]];
    if (n > 1) recs.push([PARA_TEXT, level + 1, concat(text.concat([u16(13)]))]);
    recs.push([PARA_CHAR_SHAPE, level + 1, concat(csRuns.map(([p, c]) => concat([u32(p), u32(c)])))]);
    recs.push([PARA_LINE_SEG, level + 1, lsb]);
    for (const r of ctrlRecs) recs.push([r[0], r[1], r[2]]);
    return recs;
  }
  const runs = (s, base) => s.split(/[⟦⟧]/).map((part, k) => [k % 2 ? CS_UL : base, part]);
  function endnote(num, text, baseLevel) {
    let recs = clone(EN_CTRL); recs = shift(recs, baseLevel - recs[0][1]);
    dv(recs[0][2]).setUint32(4, num, true);
    const out = [recs[0], recs[1]]; const plv = recs[1][1];
    const atno = recs.find(r => r[0] === CTRL_HEADER && head4(r[2]) === 'onta');
    const a = atno[2].slice(); dv(a).setUint32(8, num, true);
    return out.concat(para(plv, PS_EN, 181, [['ctrl', 'atno', [[CTRL_HEADER, plv + 1, a]]], [CS_EN, text]], false, 42520),
      para(plv, PS_EN, 181, [[54, '']]), para(plv, PS_EN, 181, [[54, '']], true));
  }
  // images
  const BINS = [];
  const binId = fn => { const k = BINS.findIndex(b => b[0] === fn); if (k >= 0) return k + 1; BINS.push([fn, fn.split('.').pop().toLowerCase()]); return BINS.length; };
  const fit = (disp, maxw) => { let [w, h] = disp; if (w > maxw) { h = Math.trunc(h * maxw / w); w = maxw; } return [Math.max(w, 100), Math.max(h, 100)]; };
  function picture(level, img, maxw) {
    const recs = shift(clone(PIC), level - PIC[0][1]);
    const [pw, ph] = img.px; const ow = pw * 75, oh = ph * 75; const [W, H] = fit(img.disp, maxw);
    const c = recs[0][2].slice(0, 46); const cv = dv(c); cv.setUint32(16, W, true); cv.setUint32(20, H, true); cv.setUint16(44, 0, true); recs[0][2] = c;
    const s = recs[1][2]; const sv = dv(s);
    sv.setUint32(20, ow, true); sv.setUint32(24, oh, true); sv.setUint32(28, W, true); sv.setUint32(32, H, true);
    sv.setInt32(42, Math.floor(W / 2), true); sv.setInt32(46, Math.floor(H / 2), true);
    const mats = [[1, 0, 0, 0, 1, 0], [W / ow, 0, 0, 0, H / oh, 0], [1, 0, 0, 0, 1, 0]];
    mats.forEach((m, k) => m.forEach((x, q) => sv.setFloat64(52 + 48 * k + 8 * q, x, true)));
    const p = recs[2][2]; const pv = dv(p);
    [0, 0, ow, 0, ow, oh, 0, oh].forEach((x, q) => pv.setInt32(12 + 4 * q, x, true));
    [0, 0, ow, oh].forEach((x, q) => pv.setInt32(44 + 4 * q, x, true));
    pv.setUint16(71, binId(img.image), true);
    return [recs, H];
  }
  // tables
  const TBL_CTRL = BOGI[BOGI.findIndex(r => r[0] === CTRL_HEADER)];
  const CELL_LH = BOGI.filter(r => r[0] === LIST_HEADER);
  function cellLh(level, npara, col, row, cs, rs, w, h, bf, center = false, margins = null) {
    const b = CELL_LH[0][2].slice(); const v = dv(b);
    v.setInt32(0, npara, true); v.setUint32(4, center ? 0x01000020 : 0x20, true);
    v.setUint16(8, col, true); v.setUint16(10, row, true); v.setUint16(12, cs, true); v.setUint16(14, rs, true);
    v.setUint32(16, w, true); v.setUint32(20, h, true);
    if (margins) margins.forEach((m, k) => v.setUint16(24 + 2 * k, m, true));
    v.setUint16(32, bf, true); v.setUint32(34, w, true);
    return [LIST_HEADER, level, b];
  }
  function tableCtrl(level, w, h, rows, cols, rowcells, bf = 6) {
    const c = TBL_CTRL[2].slice(); dv(c).setUint32(16, w, true); dv(c).setUint32(20, h, true);
    const t = concat([u32(0x04000004), u16(rows), u16(cols), u16(0), new Uint8Array(8)].concat(rowcells.map(u16), [u16(bf), u16(0)]));
    return [[CTRL_HEADER, level, c], [TABLE, level + 1, t]];
  }
  const estH = (s, width) => { const per = Math.max(4, Math.trunc(width / 870)); let lines = 0; for (const x of s.split('\n')) lines += Math.max(1, Math.ceil(x.length / per)); return lines * 1440; };
  function content(level, items, width, psText, csText, psObj, style = 0) {
    let recs = []; let h = 0; items = items && items.length ? items : [''];
    items.forEach((it, k) => {
      const last = k === items.length - 1;
      if (typeof it === 'object' && it.image) { const [pr, ph] = picture(level + 1, it, width); recs = recs.concat(para(level, psObj, style, [['ctrl', 'gso ', pr]], last, width)); h += ph + 400; }
      else if (typeof it === 'object' && it.kind === 'table') { const [tr, th] = dataTable(level + 1, it, width); recs = recs.concat(para(level, psObj, style, [['ctrl', 'tbl ', tr]], last, width)); h += th + 400; }
      else { recs = recs.concat(para(level, psText, style, runs(it, csText), last, width)); h += estH(it, width); }
    });
    return [recs, h];
  }
  function dataTable(level, t, maxw) {
    let W = t.widths.slice(); const H = t.heights.slice(); const tot = W.reduce((a, b) => a + b, 0);
    if (tot > maxw) W = W.map(w => Math.trunc(w * maxw / tot));
    const R = H.length, C = W.length;
    const cells = t.cells.slice().sort((a, b) => (a.r - b.r) || (a.c - b.c));
    const rowcells = []; for (let r = 0; r < R; r++) rowcells.push(cells.filter(c => c.r === r).length);
    const body = []; const need = H.slice();
    const sum = (a, s, n) => a.slice(s, s + n).reduce((x, y) => x + y, 0);
    for (const c of cells) {
      const cw_ = sum(W, c.c, c.cs);
      const ps = (c.center === undefined || c.center) ? PS_CENTER : PS_BODY;
      const [rc, hh] = content(level + 1, c.paras, cw_ - 282, ps, CS_BODY, PS_CENTER);
      if (c.rs === 1) need[c.r] = Math.max(need[c.r], hh + 282);
      body.push([c, cw_, rc]);
    }
    let out = [];
    for (const [c, cw_, rc] of body) {
      const ch_ = sum(need, c.r, c.rs);
      const npara = rc.filter(r => r[0] === PARA_HEADER && r[1] === level + 1).length;
      out.push(cellLh(level + 1, npara, c.c, c.r, c.cs, c.rs, cw_, ch_, 6, true, [141, 141, 141, 141])); out = out.concat(rc);
    }
    const total = need.reduce((a, b) => a + b, 0);
    return [tableCtrl(level, W.reduce((a, b) => a + b, 0), total, R, C, rowcells).concat(out), total];
  }
  const BOX_W = 24003;
  function box(level, b) {
    if (!b.title) {
      const [rc, hh] = content(level + 1, b.paras, BOX_W - 566, PS_BODY, CS_BODY, PS_CENTER);
      const npara = rc.filter(r => r[0] === PARA_HEADER && r[1] === level + 1).length;
      return tableCtrl(level, BOX_W, hh + 566, 1, 1, [1]).concat([cellLh(level + 1, npara, 0, 0, 1, 1, BOX_W, hh + 566, 6, false, [283, 283, 283, 283])], rc);
    }
    let t = clone(BOGI); const ci = t.findIndex(r => r[0] === CTRL_HEADER); t = shift(t.slice(ci), level - t[ci][1]);
    let out = []; let k = 0, contentH = 0;
    while (k < t.length) {
      const r = t[k];
      if (r[0] === LIST_HEADER) {
        let j = k + 1; while (j < t.length && !(t[j][0] === LIST_HEADER && t[j][1] === r[1])) j++;
        const cell = t.slice(k, j); const col = dv(r[2]).getUint16(8, true), row = dv(r[2]).getUint16(10, true);
        const ctext = cell.filter(x => x[0] === PARA_TEXT).map(x => dec16(x[2])).join('');
        if (ctext.includes('<보 기>')) {
          for (const x of cell) {
            if (x[0] === PARA_HEADER && x[1] === r[1]) dv(x[2]).setUint32(0, ((b.title.length + 1) | 0x80000000) >>> 0, true);
            if (x[0] === PARA_TEXT) x[2] = concat([utf16(b.title), u16(13)]);
          }
          out = out.concat(cell);
        } else if (col === 1 && row === 2) {
          const W = 23384 - 425 - 141;
          const [inner, ch] = content(r[1], b.paras, W, PS_BODY, CS_BODY, PS_CENTER); contentH = ch;
          const npara = inner.filter(x => x[0] === PARA_HEADER && x[1] === r[1]).length;
          const lh = r[2].slice(); dv(lh).setInt32(0, npara, true); dv(lh).setUint32(20, Math.max(1998, contentH + 566), true);
          out.push([LIST_HEADER, r[1], lh]); out = out.concat(inner);
        } else {
          if ((col === 0 || col === 4) && row === 2) { const lh = r[2].slice(); dv(lh).setUint32(20, Math.max(1732, contentH + 300), true); cell[0][2] = lh; }
          out = out.concat(cell);
        }
        k = j;
      } else { out.push(r); k++; }
    }
    dv(out[0][2]).setUint32(20, 1100 + Math.max(1998, contentH + 566) + 200, true);
    return out;
  }
  // body
  let body = [];
  const sp = clone(SEC_PARA);
  sp[1][2] = concat([sp[1][2].slice(0, 32), u16(13)]);
  dv(sp[0][2]).setUint32(0, 17, true);
  sp[2][2] = concat([u32(0), u32(CS_BODY)]);
  body = body.concat(sp);
  const blank = (n = 1) => { let o = []; for (let k = 0; k < n; k++) o = o.concat(para(0, PS_BODY, 0, [[CS_BODY, '']])); return o; };
  const COLW = 42520, PASSW = 41520; let enNo = 0;
  for (const blk of A.doc) {
    if (blk.kind === 'passage') {
      body = body.concat(blank(2), para(0, PS_BODY, 0, [[CS_BOLD, pyStrip(blk.head)]]), para(0, PS_PASS, 1, [[CS_PASS, '']]));
      for (const p of blk.paras) {
        if (typeof p === 'object' && p.image) { const [pr] = picture(1, p, PASSW); body = body.concat(para(0, PS_PASS, 1, [['ctrl', 'gso ', pr]])); }
        else if (typeof p === 'object') { const [tr] = dataTable(1, p, PASSW); body = body.concat(para(0, PS_PASS, 1, [['ctrl', 'tbl ', tr]])); }
        else body = body.concat(para(0, PS_PASS, 1, runs(p, CS_PASS)));
      }
      body = body.concat(blank(1)); continue;
    }
    enNo++;
    body = body.concat(enNo > 1 ? blank(3) : blank(1));
    body = body.concat(para(0, PS_BODY, 0, [[CS_BODY, blk.stem], ['ctrl', 'en  ', endnote(enNo, A.ans[String(blk.num)] || ' [정답]  [해설] ', 1)]]));
    for (const it of blk.items) {
      const k = it.kind;
      if (k === 'box') body = body.concat(para(0, PS_BODY, 0, [['ctrl', 'tbl ', box(1, it)]]));
      else if (k === 'table') { const [tr] = dataTable(1, it, COLW); body = body.concat(para(0, PS_CENTER, 0, [['ctrl', 'tbl ', tr]])); }
      else if (it.image) { const [pr] = picture(1, it, COLW); body = body.concat(para(0, PS_BODY, 0, [['ctrl', 'gso ', pr]])); }
      else if (k === 'para') body = body.concat(para(0, PS_BODY, 0, runs(it.text, CS_BODY)));
      else if (k === 'choice') {
        const items = runs(it.text, CS_BODY);
        for (const im of it.images || []) { const [pr] = picture(1, im, COLW); items.push([CS_BODY, ' '], ['ctrl', 'gso ', pr]); }
        body = body.concat(para(0, PS_BODY, 0, items));
      } else throw new Error('unknown item');
    }
  }
  body = body.concat(blank(2));
  for (let k = body.length - 1; k >= 0; k--) if (body[k][0] === PARA_HEADER && body[k][1] === 0) { const v = dv(body[k][2]); v.setUint32(0, (v.getUint32(0, true) | 0x80000000) >>> 0, true); break; }
  // DocInfo
  const newDi = []; let binDone = false;
  for (const [t, l, p0] of docinfo) {
    let p = p0;
    if (t === 17) { p = p0.slice(); dv(p).setUint32(0, BINS.length, true); }
    if (t === 18) {
      if (binDone) continue;
      BINS.forEach(([fn, ext], k) => newDi.push([18, l, concat([u16(0x0021), u16(k + 1), u16(ext.length), utf16(ext)])]));
      binDone = true; continue;
    }
    newDi.push([t, l, p]);
  }
  const prv = [A.title].concat(A.doc.filter(b => b.kind === 'q').slice(0, 6).map(b => b.stem)).join('\r\n');
  const out = {
    'FileHeader': tpl['FileHeader'],
    'DocInfo': Z.deflateRaw(recsBuild(newDi)),
    'BodyText/Section0': Z.deflateRaw(recsBuild(body)),
    '\x05HwpSummaryInformation': tpl['\x05HwpSummaryInformation'],
    'PrvText': utf16(prv).slice(0, 2048),
    'PrvImage': blankPng(177, 250),
    'DocOptions/_LinkDoc': tpl['DocOptions/_LinkDoc'],
    'Scripts/DefaultJScript': tpl['Scripts/DefaultJScript'],
    'Scripts/JScriptVersion': tpl['Scripts/JScriptVersion'],
  };
  BINS.forEach(([fn, ext], k) => { out['BinData/BIN' + (k + 1).toString(16).toUpperCase().padStart(4, '0') + '.' + ext] = A.images[fn]; });
  return { bytes: cfbWrite(out), questions: enNo, images: BINS.length };
}
function blankPng(w, h) {
  const chunk = (t, b) => { const tb = concat([ubin(t), b]); const L = new Uint8Array(4); dv(L).setUint32(0, b.length); const C = new Uint8Array(4); dv(C).setUint32(0, crc32(tb)); return concat([L, tb, C]); };
  const raw = new Uint8Array(h * (w * 3 + 1)).fill(255); for (let y = 0; y < h; y++) raw[y * (w * 3 + 1)] = 0;
  const ih = new Uint8Array(13); const v = dv(ih); v.setUint32(0, w); v.setUint32(4, h); ih[8] = 8; ih[9] = 2;
  return concat([new Uint8Array([0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]), chunk('IHDR', ih), chunk('IDAT', Z.deflate(raw)), chunk('IEND', new Uint8Array(0))]);
}
function b64(s) {
  if (typeof atob === 'function') { const b = atob(s); return ubin(b); }
  return new Uint8Array(Buffer.from(s, 'base64'));
}

// ------------------------------------------------------------------ verification
function hwpText(bytes) {                     // hwp.py text mode
  const st = cfbRead(bytes); const props = dv(st['FileHeader']).getUint32(36, true);
  const names = Object.keys(st).filter(k => k.startsWith('BodyText/Section')).sort((a, b) => parseInt(a.slice(16)) - parseInt(b.slice(16)));
  const lines = [];
  for (const nm of names) {
    let b = st[nm]; if (props & 1) b = Z.inflateRaw(b);
    for (const [tag, , rec] of recsParse(b)) {
      if (tag !== 67) continue;
      const v = dv(rec); let t = ''; let i = 0; const n = rec.length >> 1;
      while (i < n) {
        const c = v.getUint16(i * 2, true);
        if (c < 32) {
          if (c === 0 || c === 10 || c === 13 || (c >= 24 && c <= 31)) { if (c === 10 || c === 13) t += '\n'; i++; }
          else { if (c === 9) t += '\t'; i += 8; }
        } else { t += String.fromCharCode(c); i++; }
      }
      lines.push(t.replace(/\n+$/, ''));
    }
  }
  return lines.join('\n');
}
function verify(pdfBytes, hwpBytes, A) {
  const norm = s => s.replace(/\s/g, '').replace(/〈/g, '<').replace(/〉/g, '>');
  const count = s => { const m = new Map(); for (const ch of s) m.set(ch, (m.get(ch) || 0) + 1); return m; };
  const P = count(norm(A.bodyText)), H = count(norm(hwpText(hwpBytes)));
  const diff = (a, b) => { const o = {}; for (const [k, v] of a) { const d = v - (b.get(k) || 0); if (d > 0) o[k] = d; } return o; };
  return { onlyPdf: diff(P, H), onlyHwp: diff(H, P) };
}

// ------------------------------------------------------------------ zip (stored, UTF-8 names)
function makeZip(files) {
  const enc = new TextEncoder(); const parts = [], cdir = []; let off = 0;
  for (const f of files) {
    const name = enc.encode(f.name); const crc = crc32(f.data); const n = f.data.length;
    const lh = new Uint8Array(30); const v = dv(lh);
    v.setUint32(0, 0x04034b50, true); v.setUint16(4, 20, true); v.setUint16(6, 0x0800, true); v.setUint16(8, 0, true);
    v.setUint16(10, 0, true); v.setUint16(12, 0x21, true); v.setUint32(14, crc, true); v.setUint32(18, n, true); v.setUint32(22, n, true); v.setUint16(26, name.length, true);
    parts.push(lh, name, f.data);
    const ch = new Uint8Array(46); const c = dv(ch);
    c.setUint32(0, 0x02014b50, true); c.setUint16(4, 20, true); c.setUint16(6, 20, true); c.setUint16(8, 0x0800, true); c.setUint16(14, 0x21, true);
    c.setUint32(16, crc, true); c.setUint32(20, n, true); c.setUint32(24, n, true); c.setUint16(28, name.length, true); c.setUint32(42, off, true);
    cdir.push(ch, name); off += 30 + name.length + n;
  }
  const cd = concat(cdir); const end = new Uint8Array(22); const e = dv(end);
  e.setUint32(0, 0x06054b50, true); e.setUint16(8, files.length, true); e.setUint16(10, files.length, true); e.setUint32(12, cd.length, true); e.setUint32(16, off, true);
  return concat(parts.concat([cd, end]));
}

const HwpConv = {
  init(z, data) { Z = z; DATA = data; },
  analyze,
  buildHwp, hwpText, verify, makeZip,
};
root.HwpConv = HwpConv;
if (typeof module !== 'undefined') module.exports = HwpConv;
})(typeof window !== 'undefined' ? window : globalThis);
