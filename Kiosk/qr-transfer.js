'use strict';
/*
  qr-transfer.js  —  Griffin Museum wayfinding: kiosk → phone hand-off.

  Two independent pieces, no external dependencies (works offline / on GitHub Pages):

  1. MuseumQR.encode(text, ecl)         -> { size, modules[][], version, mask, ecl }
     A self-contained QR (Model 2) byte-mode encoder, versions 1..10, EC L/M/Q/H.
     Module placement, masking, Reed-Solomon and format/version info follow ISO/IEC
     18004. Verified end-to-end by decoding generated symbols with a real QR reader
     (libzbar): RS syndromes are zero and payloads round-trip at every EC level.

  2. MuseumTransfer.*                    -> build the mobile URL + paint the QR canvas.
     The mobile base URL is DERIVED from the current kiosk page location (sibling
     "mobile/" folder). No usernames, repo names or museum data are hardcoded here.
*/
(function (global) {

  /* ============================ QR ENCODER ============================ */
  var EXP = new Array(512), LOG = new Array(256);
  (function () { var x = 1; for (var i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 0x100) x ^= 0x11D; } for (var i2 = 255; i2 < 512; i2++) EXP[i2] = EXP[i2 - 255]; })();
  function gfMul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }
  function rsGenPoly(deg) { var g = [1]; for (var i = 0; i < deg; i++) { var ng = new Array(g.length + 1).fill(0); for (var j = 0; j < g.length; j++) { ng[j] ^= g[j]; ng[j + 1] ^= gfMul(g[j], EXP[i]); } g = ng; } return g; }
  function rsEc(data, ecLen) { var gen = rsGenPoly(ecLen); var res = new Array(ecLen).fill(0); for (var i = 0; i < data.length; i++) { var coef = data[i] ^ res[0]; res.shift(); res.push(0); if (coef !== 0) for (var j = 0; j < ecLen; j++) res[j] ^= gfMul(gen[j + 1], coef); } return res; }

  // [ecPerBlock, g1blocks, g1data, g2blocks, g2data]
  var EC = {
    L: { 1:[7,1,19,0,0],2:[10,1,34,0,0],3:[15,1,55,0,0],4:[20,1,80,0,0],5:[26,1,108,0,0],6:[18,2,68,0,0],7:[20,2,78,0,0],8:[24,2,97,0,0],9:[30,2,116,0,0],10:[18,2,68,2,69] },
    M: { 1:[10,1,16,0,0],2:[16,1,28,0,0],3:[26,1,44,0,0],4:[18,2,32,0,0],5:[24,2,43,0,0],6:[16,4,27,0,0],7:[18,4,31,0,0],8:[22,2,38,2,39],9:[22,3,36,2,37],10:[26,4,43,1,44] },
    Q: { 1:[13,1,13,0,0],2:[22,1,22,0,0],3:[18,2,17,0,0],4:[26,2,24,0,0],5:[18,2,15,2,16],6:[24,4,19,0,0],7:[18,2,14,4,15],8:[22,4,18,2,19],9:[20,4,16,4,17],10:[24,6,19,2,20] },
    H: { 1:[17,1,9,0,0],2:[28,1,16,0,0],3:[22,2,13,0,0],4:[16,4,9,0,0],5:[22,2,11,2,12],6:[28,4,15,0,0],7:[26,4,13,1,14],8:[26,4,14,2,15],9:[24,4,12,4,13],10:[28,6,15,2,16] }
  };
  var ALIGN = { 1:[],2:[6,18],3:[6,22],4:[6,26],5:[6,30],6:[6,34],7:[6,22,38],8:[6,24,42],9:[6,26,46],10:[6,28,50] };
  var ECL_BITS = { L:1, M:0, Q:3, H:2 };

  function totalDataCw(ecl, ver) { var t = EC[ecl][ver]; return t[1]*t[2] + t[3]*t[4]; }
  function capacityBytes(ecl, ver) { var cw = totalDataCw(ecl, ver); var countBits = ver < 10 ? 8 : 16; return Math.floor((cw * 8 - 4 - countBits) / 8); }
  function chooseVersion(byteLen, ecl) {
    for (var v = 1; v <= 10; v++) if (byteLen <= capacityBytes(ecl, v)) return v;
    return null; // caller decides how to handle overflow
  }
  function toBytes(str) { var out = []; for (var i = 0; i < str.length; i++) { var c = str.charCodeAt(i); if (c < 0x80) out.push(c); else if (c < 0x800) { out.push(0xC0 | (c >> 6), 0x80 | (c & 0x3F)); } else { out.push(0xE0 | (c >> 12), 0x80 | ((c >> 6) & 0x3F), 0x80 | (c & 0x3F)); } } return out; }

  function buildCodewords(bytes, ecl, ver) {
    var cw = totalDataCw(ecl, ver);
    var countBits = ver < 10 ? 8 : 16;
    var bits = [];
    var push = function (val, n) { for (var i = n - 1; i >= 0; i--) bits.push((val >> i) & 1); };
    push(0x4, 4);                 // byte mode
    push(bytes.length, countBits);
    bytes.forEach(function (b) { push(b, 8); });
    var cap = cw * 8;
    for (var i = 0; i < 4 && bits.length < cap; i++) bits.push(0);   // terminator
    while (bits.length % 8 !== 0) bits.push(0);                       // byte align
    var data = [];
    for (var k = 0; k < bits.length; k += 8) { var b = 0; for (var j = 0; j < 8; j++) b = (b << 1) | bits[k + j]; data.push(b); }
    var pads = [0xEC, 0x11], pi = 0;
    while (data.length < cw) data.push(pads[pi++ % 2]);

    var t = EC[ecl][ver], ecLen = t[0], g1b = t[1], g1d = t[2], g2b = t[3], g2d = t[4];
    var blocks = [], idx = 0, i2;
    for (i2 = 0; i2 < g1b; i2++) { blocks.push(data.slice(idx, idx + g1d)); idx += g1d; }
    for (i2 = 0; i2 < g2b; i2++) { blocks.push(data.slice(idx, idx + g2d)); idx += g2d; }
    var ecs = blocks.map(function (bl) { return rsEc(bl, ecLen); });

    var out = [];
    var maxData = Math.max(g1d, g2d);
    for (var kk = 0; kk < maxData; kk++) for (var bb = 0; bb < blocks.length; bb++) if (kk < blocks[bb].length) out.push(blocks[bb][kk]);
    for (var ke = 0; ke < ecLen; ke++) for (var be = 0; be < blocks.length; be++) out.push(ecs[be][ke]);
    return out;
  }

  function encode(text, ecl) {
    ecl = ecl || 'M';
    var bytes = toBytes(text);
    var ver = chooseVersion(bytes.length, ecl);
    if (ver === null) throw new Error('QR payload too long for versions 1..10 at EC ' + ecl + ': ' + bytes.length + ' bytes');
    var size = 17 + 4 * ver;
    var codewords = buildCodewords(bytes, ecl, ver);

    var mod = Array.from({ length: size }, function () { return new Array(size).fill(false); });
    var fn = Array.from({ length: size }, function () { return new Array(size).fill(false); });
    var setF = function (x, y, v) { mod[y][x] = v; fn[y][x] = true; };

    var i;
    for (i = 0; i < size; i++) { setF(6, i, i % 2 === 0); setF(i, 6, i % 2 === 0); }
    function finder(cx, cy) { for (var dy = -4; dy <= 4; dy++) for (var dx = -4; dx <= 4; dx++) { var x = cx + dx, y = cy + dy; if (x < 0 || y < 0 || x >= size || y >= size) continue; var d = Math.max(Math.abs(dx), Math.abs(dy)); setF(x, y, d !== 2 && d !== 4); } }
    finder(3, 3); finder(size - 4, 3); finder(3, size - 4);
    var ap = ALIGN[ver];
    for (i = 0; i < ap.length; i++) for (var j = 0; j < ap.length; j++) {
      var cx = ap[i], cy = ap[j];
      if ((cx <= 8 && cy <= 8) || (cx <= 8 && cy >= size - 9) || (cx >= size - 9 && cy <= 8)) continue;
      for (var dy = -2; dy <= 2; dy++) for (var dx = -2; dx <= 2; dx++) setF(cx + dx, cy + dy, Math.max(Math.abs(dx), Math.abs(dy)) !== 1);
    }
    setF(8, size - 8, true);
    for (i = 0; i < 9; i++) { if (!fn[i][8]) setF(8, i, false); if (!fn[8][i]) setF(i, 8, false); }
    for (i = 0; i < 8; i++) { if (!fn[size - 1 - i][8]) setF(8, size - 1 - i, false); if (!fn[8][size - 1 - i]) setF(size - 1 - i, 8, false); }
    if (ver >= 7) for (i = 0; i < 18; i++) { var a = size - 11 + (i % 3), bb = Math.floor(i / 3); setF(a, bb, false); setF(bb, a, false); }

    var bit = 0, nbits = codewords.length * 8, right = size - 1;
    while (right >= 1) {
      if (right === 6) right = 5;
      for (var v = 0; v < size; v++) for (var jj = 0; jj < 2; jj++) {
        var x = right - jj;
        var upward = ((right + 1) & 2) === 0;
        var y = upward ? size - 1 - v : v;
        if (fn[y][x]) continue;
        var dark = false;
        if (bit < nbits) { dark = ((codewords[bit >> 3] >> (7 - (bit & 7))) & 1) === 1; bit++; }
        mod[y][x] = dark;
      }
      right -= 2;
    }

    if (ver >= 7) {
      var rem = ver; for (i = 0; i < 12; i++) rem = (rem << 1) ^ ((rem >> 11) * 0x1F25);
      var vbits = (ver << 12) | rem;
      for (i = 0; i < 18; i++) { var vb = ((vbits >> i) & 1) === 1; var a2 = size - 11 + (i % 3), c2 = Math.floor(i / 3); mod[c2][a2] = vb; mod[a2][c2] = vb; }
    }

    var maskCond = function (m, x, y) {
      switch (m) {
        case 0: return (x + y) % 2 === 0;
        case 1: return y % 2 === 0;
        case 2: return x % 3 === 0;
        case 3: return (x + y) % 3 === 0;
        case 4: return (Math.floor(y / 2) + Math.floor(x / 3)) % 2 === 0;
        case 5: return (x * y) % 2 + (x * y) % 3 === 0;
        case 6: return ((x * y) % 2 + (x * y) % 3) % 2 === 0;
        case 7: return ((x + y) % 2 + (x * y) % 3) % 2 === 0;
      }
    };
    function drawFormat(m, target) {
      var data = (ECL_BITS[ecl] << 3) | m;
      var rem = data; for (var i2 = 0; i2 < 10; i2++) rem = (rem << 1) ^ ((rem >> 9) * 0x537);
      var bits = ((data << 10) | rem) ^ 0x5412;
      var gb = function (i3) { return ((bits >> i3) & 1) === 1; };
      for (var k = 0; k <= 5; k++) target[k][8] = gb(k);
      target[7][8] = gb(6); target[8][8] = gb(7); target[8][7] = gb(8);
      for (var k2 = 9; k2 < 15; k2++) target[8][14 - k2] = gb(k2);
      for (var k3 = 0; k3 < 8; k3++) target[8][size - 1 - k3] = gb(k3);
      for (var k4 = 8; k4 < 15; k4++) target[size - 15 + k4][8] = gb(k4);
      target[size - 8][8] = true;
    }
    function penalty(m2) {
      var p = 0, x, y, run;
      for (y = 0; y < size; y++) { run = 1; for (x = 1; x < size; x++) { if (m2[y][x] === m2[y][x - 1]) { run++; if (run === 5) p += 3; else if (run > 5) p++; } else run = 1; } }
      for (x = 0; x < size; x++) { run = 1; for (y = 1; y < size; y++) { if (m2[y][x] === m2[y - 1][x]) { run++; if (run === 5) p += 3; else if (run > 5) p++; } else run = 1; } }
      for (y = 0; y < size - 1; y++) for (x = 0; x < size - 1; x++) { var c = m2[y][x]; if (c === m2[y][x + 1] && c === m2[y + 1][x] && c === m2[y + 1][x + 1]) p += 3; }
      var pat = [true, false, true, true, true, false, true];
      function check(get) { for (var i3 = 0; i3 < size; i3++) for (var jj = 0; jj <= size - 7; jj++) { var ok = true; for (var k = 0; k < 7; k++) if (get(i3, jj + k) !== pat[k]) { ok = false; break; } if (ok) { var before = true, after = true; for (var k2 = jj - 4; k2 < jj; k2++) { if (k2 < 0 || get(i3, k2)) { before = false; break; } } for (var k3 = jj + 7; k3 < jj + 11; k3++) { if (k3 >= size || get(i3, k3)) { after = false; break; } } if (before || after) p += 40; } } }
      check(function (i3, k) { return m2[i3][k]; }); check(function (i3, k) { return m2[k][i3]; });
      var dark = 0; for (y = 0; y < size; y++) for (x = 0; x < size; x++) if (m2[y][x]) dark++;
      var ratio = dark * 100 / (size * size); var dev = Math.floor(Math.abs(ratio - 50) / 5); p += dev * 10;
      return p;
    }

    var best = null, bestMask = 0;
    for (var m = 0; m < 8; m++) {
      var cp = mod.map(function (r) { return r.slice(); });
      for (var yy = 0; yy < size; yy++) for (var xx = 0; xx < size; xx++) if (!fn[yy][xx] && maskCond(m, xx, yy)) cp[yy][xx] = !cp[yy][xx];
      drawFormat(m, cp);
      var pen = penalty(cp);
      if (best === null || pen < best) { best = pen; bestMask = m; }
    }
    for (var y2 = 0; y2 < size; y2++) for (var x2 = 0; x2 < size; x2++) if (!fn[y2][x2] && maskCond(bestMask, x2, y2)) mod[y2][x2] = !mod[y2][x2];
    drawFormat(bestMask, mod);

    return { size: size, modules: mod, version: ver, mask: bestMask, ecl: ecl };
  }

  var MuseumQR = { encode: encode, capacityBytes: capacityBytes };

  /* ============================ CANVAS PAINT ============================ */
  // Paints the QR onto a <canvas>, crisp (nearest-neighbour) with a quiet zone.
  function paint(canvas, qr, opts) {
    opts = opts || {};
    var dark = opts.dark || '#2A140A';
    var light = opts.light || '#ffffff';
    var quiet = (opts.quiet == null ? 4 : opts.quiet);
    var ctx = canvas.getContext('2d');
    var pxW = canvas.width, pxH = canvas.height;
    var dim = qr.size + quiet * 2;
    var cell = Math.floor(Math.min(pxW, pxH) / dim);
    if (cell < 1) cell = 1;
    var drawn = cell * dim;
    var offX = Math.floor((pxW - drawn) / 2);
    var offY = Math.floor((pxH - drawn) / 2);
    ctx.fillStyle = light; ctx.fillRect(0, 0, pxW, pxH);
    ctx.fillStyle = dark;
    for (var y = 0; y < qr.size; y++) for (var x = 0; x < qr.size; x++) {
      if (qr.modules[y][x]) ctx.fillRect(offX + (x + quiet) * cell, offY + (y + quiet) * cell, cell, cell);
    }
  }

  // Encode + paint, automatically stepping DOWN the EC level if a long URL would
  // overflow the versions we support (keeps error-correction as high as fits).
  function renderToCanvas(canvas, text, opts) {
    opts = opts || {};
    var order = ['M', 'L']; // default M for robust scanning; fall back to L for very long URLs
    if (opts.ecl) order = [opts.ecl].concat(order.filter(function (e) { return e !== opts.ecl; }));
    var lastErr = null;
    for (var i = 0; i < order.length; i++) {
      try { var qr = encode(text, order[i]); paint(canvas, qr, opts); return qr; }
      catch (e) { lastErr = e; }
    }
    throw lastErr || new Error('Unable to encode QR');
  }

  /* ============================ TRANSFER URLs ============================ */
  // Derive the absolute base URL of the mobile app from the current kiosk page.
  // Deployment convention (see project structure): /<repo>/kiosk/<file> and
  // /<repo>/mobile/ are sibling folders. We resolve "../mobile/" against the
  // kiosk directory so nothing about the host/user/repo is hardcoded.
  // An explicit override wins if provided: window.MUSEUM_MOBILE_URL, or a
  // data-mobile-base="..." attribute on this script tag.
  function scriptOverride() {
    try {
      var s = document.currentScript;
      if (s && s.getAttribute('data-mobile-base')) return s.getAttribute('data-mobile-base');
      var all = document.getElementsByTagName('script');
      for (var i = 0; i < all.length; i++) {
        var mb = all[i].getAttribute && all[i].getAttribute('data-mobile-base');
        if (mb) return mb;
      }
    } catch (e) {}
    return null;
  }
  function mobileBaseURL() {
    if (global.MUSEUM_MOBILE_URL) { try { return new URL(global.MUSEUM_MOBILE_URL, global.location.href).href; } catch (e) {} }
    var ov = scriptOverride();
    if (ov) { try { return new URL(ov, global.location.href).href; } catch (e) {} }
    var here = global.location.href;
    var dir = here.replace(/[?#].*$/, '').replace(/[^/]*$/, ''); // strip query/hash + filename -> directory
    try {
      // If we're inside a ".../kiosk/" folder, hop to the sibling ".../mobile/".
      if (/\/kiosk\/$/i.test(dir)) return new URL('../mobile/', dir).href;
      // Otherwise assume a sibling "mobile/" next to wherever the kiosk page lives.
      return new URL('mobile/', dir).href;
    } catch (e) {
      return dir + 'mobile/';
    }
  }

  function boolParam(v) { return v ? 'true' : 'false'; }

  function buildDirectionsURL(startId, destinationId, avoidStairs) {
    var base = mobileBaseURL();
    var q = 'mode=directions'
      + '&start=' + encodeURIComponent(startId)
      + '&destination=' + encodeURIComponent(destinationId)
      + '&avoidStairs=' + boolParam(avoidStairs);
    return base + (base.indexOf('?') >= 0 ? '&' : '?') + q;
  }

  function buildPlanURL(stopIds, startId, avoidStairs) {
    var base = mobileBaseURL();
    var stops = (stopIds || []).filter(Boolean).join(',');
    var q = 'mode=plan'
      + '&stops=' + encodeURIComponent(stops)
      + (startId ? '&start=' + encodeURIComponent(startId) : '')
      + '&avoidStairs=' + boolParam(avoidStairs);
    return base + (base.indexOf('?') >= 0 ? '&' : '?') + q;
  }

  // Convenience: build the directions URL and paint the QR in one call.
  // Returns the URL (so callers can also expose an "open on this device" link).
  function renderDirectionsQR(canvas, startId, destinationId, avoidStairs, opts) {
    var url = buildDirectionsURL(startId, destinationId, avoidStairs);
    if (canvas) renderToCanvas(canvas, url, opts);
    return url;
  }
  function renderPlanQR(canvas, stopIds, startId, avoidStairs, opts) {
    var url = buildPlanURL(stopIds, startId, avoidStairs);
    if (canvas) renderToCanvas(canvas, url, opts);
    return url;
  }

  var MuseumTransfer = {
    mobileBaseURL: mobileBaseURL,
    buildDirectionsURL: buildDirectionsURL,
    buildPlanURL: buildPlanURL,
    renderToCanvas: renderToCanvas,
    renderDirectionsQR: renderDirectionsQR,
    renderPlanQR: renderPlanQR
  };

  global.MuseumQR = MuseumQR;
  global.MuseumTransfer = MuseumTransfer;
  if (typeof module !== 'undefined' && module.exports) module.exports = { MuseumQR: MuseumQR, MuseumTransfer: MuseumTransfer };

})(typeof window !== 'undefined' ? window : this);
