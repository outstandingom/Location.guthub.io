/* Auto-trace ward regions from a scanned line map (no dependencies).
   Works on a grayscale Uint8Array (W*H). Dark pixels = boundary lines. */
(function (root) {
  function buildBarrier(gray, W, H, threshold, gap) {
    let b = new Uint8Array(W * H);
    for (let i = 0; i < b.length; i++) b[i] = gray[i] < threshold ? 1 : 0;
    // close small gaps in lines: 4-neighbour dilation `gap` times
    for (let g = 0; g < gap; g++) {
      const n = b.slice();
      for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
        const i = y * W + x;
        if (b[i]) continue;
        if ((x > 0 && b[i - 1]) || (x < W - 1 && b[i + 1]) || (y > 0 && b[i - W]) || (y < H - 1 && b[i + W])) n[i] = 1;
      }
      b = n;
    }
    return b;
  }

  // 4-connected fill of non-barrier pixels starting at seed(s)
  function floodFill(barrier, W, H, seeds) {
    const mask = new Uint8Array(W * H);
    const stack = new Int32Array(W * H);
    let sp = 0, count = 0;
    seeds.forEach(i => { if (!barrier[i] && !mask[i]) { mask[i] = 1; stack[sp++] = i; } });
    while (sp) {
      const i = stack[--sp]; count++;
      const x = i % W;
      if (x > 0 && !mask[i - 1] && !barrier[i - 1]) { mask[i - 1] = 1; stack[sp++] = i - 1; }
      if (x < W - 1 && !mask[i + 1] && !barrier[i + 1]) { mask[i + 1] = 1; stack[sp++] = i + 1; }
      if (i >= W && !mask[i - W] && !barrier[i - W]) { mask[i - W] = 1; stack[sp++] = i - W; }
      if (i < W * (H - 1) && !mask[i + W] && !barrier[i + W]) { mask[i + W] = 1; stack[sp++] = i + W; }
    }
    return { mask, count };
  }

  // grow region into the line pixels so neighbouring wards meet at the line centre
  function growIntoBarrier(mask, barrier, W, H, iters) {
    for (let k = 0; k < iters; k++) {
      const add = [];
      for (let i = 0; i < mask.length; i++) {
        if (mask[i] || !barrier[i]) continue;
        const x = i % W;
        if ((x > 0 && mask[i - 1]) || (x < W - 1 && mask[i + 1]) || (i >= W && mask[i - W]) || (i < W * (H - 1) && mask[i + W])) add.push(i);
      }
      add.forEach(i => mask[i] = 1);
    }
    return mask;
  }

  // keep only the largest 4-connected component of a mask
  function largestComponent(mask, W, H) {
    const inv = new Uint8Array(W * H);
    for (let i = 0; i < inv.length; i++) inv[i] = mask[i] ? 0 : 1; // barrier = not in mask
    const seen = new Uint8Array(W * H);
    let best = null, bestCount = 0;
    for (let i = 0; i < mask.length; i++) {
      if (!mask[i] || seen[i]) continue;
      const r = floodFill(inv, W, H, [i]);
      for (let j = 0; j < r.mask.length; j++) if (r.mask[j]) seen[j] = 1;
      if (r.count > bestCount) { bestCount = r.count; best = r.mask; }
    }
    return { mask: best, count: bestCount };
  }

  // Follow the outer boundary along pixel edges. Returns corner points [x,y].
  function traceOuter(mask, W, H) {
    const inside = (x, y) => x >= 0 && y >= 0 && x < W && y < H && mask[y * W + x] === 1;
    let start = -1;
    for (let i = 0; i < mask.length; i++) if (mask[i]) { start = i; break; }
    if (start < 0) return [];
    const x0 = start % W, y0 = (start / W) | 0;
    const DX = [1, 0, -1, 0], DY = [0, 1, 0, -1];
    let vx = x0, vy = y0, d = 0;
    const pts = [[vx, vy]];
    const maxSteps = 4 * W * H;
    for (let s = 0; s < maxSteps; s++) {
      vx += DX[d]; vy += DY[d];
      let al, ar; // pixels ahead-left / ahead-right of vertex (vx,vy) for direction d
      if (d === 0) { al = inside(vx, vy - 1); ar = inside(vx, vy); }
      else if (d === 1) { al = inside(vx, vy); ar = inside(vx - 1, vy); }
      else if (d === 2) { al = inside(vx - 1, vy); ar = inside(vx - 1, vy - 1); }
      else { al = inside(vx - 1, vy - 1); ar = inside(vx, vy - 1); }
      const nd = al ? (d + 3) % 4 : ar ? d : (d + 1) % 4;
      if (vx === x0 && vy === y0 && nd === 0) break;
      if (nd !== d) pts.push([vx, vy]);
      d = nd;
    }
    return pts;
  }

  // Ramer–Douglas–Peucker on a closed ring
  function simplifyRing(pts, tol) {
    if (pts.length < 4) return pts;
    const rdp = (a) => {
      if (a.length < 3) return a;
      const [x1, y1] = a[0], [x2, y2] = a[a.length - 1];
      const dx = x2 - x1, dy = y2 - y1, len = Math.hypot(dx, dy);
      let maxD = -1, idx = 0;
      for (let i = 1; i < a.length - 1; i++) {
        const [px, py] = a[i];
        const dist = len === 0 ? Math.hypot(px - x1, py - y1) : Math.abs(dy * px - dx * py + x2 * y1 - y2 * x1) / len;
        if (dist > maxD) { maxD = dist; idx = i; }
      }
      if (maxD <= tol) return [a[0], a[a.length - 1]];
      const l = rdp(a.slice(0, idx + 1)), r = rdp(a.slice(idx));
      return l.slice(0, -1).concat(r);
    };
    // split ring at the point farthest from the first point
    let far = 0, fd = -1;
    pts.forEach((p, i) => { const d = Math.hypot(p[0] - pts[0][0], p[1] - pts[0][1]); if (d > fd) { fd = d; far = i; } });
    const a = rdp(pts.slice(0, far + 1));
    const b = rdp(pts.slice(far).concat([pts[0]]));
    return a.slice(0, -1).concat(b.slice(0, -1));
  }

  // Region containing pixel (sx,sy)
  function traceRegion(gray, W, H, sx, sy, opt) {
    const barrier = opt.barrier || buildBarrier(gray, W, H, opt.threshold, opt.gap);
    // if the click landed on a line, move to the nearest open pixel
    let seed = -1;
    for (let r = 0; r <= 6 && seed < 0; r++)
      for (let dy = -r; dy <= r && seed < 0; dy++) for (let dx = -r; dx <= r; dx++) {
        const x = sx + dx, y = sy + dy;
        if (x >= 0 && y >= 0 && x < W && y < H && !barrier[y * W + x]) { seed = y * W + x; break; }
      }
    if (seed < 0) return { error: "Clicked on a thick line — click a bit further inside the ward." };
    const { mask, count } = floodFill(barrier, W, H, [seed]);
    // touching the image edge means we are outside the municipality (or a line has a gap)
    for (let x = 0; x < W; x++) if (mask[x] || mask[(H - 1) * W + x]) return { error: "Leaked outside the boundary — increase 'Gap fill' or click inside a ward.", leak: true };
    for (let y = 0; y < H; y++) if (mask[y * W] || mask[y * W + W - 1]) return { error: "Leaked outside the boundary — increase 'Gap fill' or click inside a ward.", leak: true };
    growIntoBarrier(mask, barrier, W, H, opt.gap + 1);
    const ring = simplifyRing(traceOuter(mask, W, H), opt.tolerance);
    return { ring, pixels: count };
  }

  // Whole municipality = everything not reachable from the image edge
  function traceOutline(gray, W, H, opt) {
    const barrier = buildBarrier(gray, W, H, opt.threshold, opt.gap);
    const seeds = [];
    for (let x = 0; x < W; x++) seeds.push(x, (H - 1) * W + x);
    for (let y = 0; y < H; y++) seeds.push(y * W, y * W + W - 1);
    const outside = floodFill(barrier, W, H, seeds).mask;
    const muni = new Uint8Array(W * H);
    for (let i = 0; i < muni.length; i++) muni[i] = outside[i] ? 0 : 1;
    const big = largestComponent(muni, W, H);
    if (!big.mask) return { error: "No closed outline found." };
    const ring = simplifyRing(traceOuter(big.mask, W, H), opt.tolerance);
    return { ring, pixels: big.count };
  }

  // Seed is a ward label (a small circle). Try points around it so we fill the ward, not the circle.
  function traceNearLabel(gray, W, H, lx, ly, opt) {
    const offs = [[0, -15], [0, 15], [-15, 0], [15, 0], [-12, -12], [12, -12], [-12, 12], [12, 12], [0, -22], [0, 22], [-22, 0], [22, 0]];
    let best = null;
    for (const [dx, dy] of offs) {
      const r = traceRegion(gray, W, H, Math.round(lx + dx), Math.round(ly + dy), opt);
      if (r.error || r.pixels < (opt.minPixels || 400)) continue;
      if (!best || r.pixels > best.pixels) best = r;
      if (best) break;
    }
    return best || { error: "Could not find the ward area around its label." };
  }

  function pointInRing(x, y, ring) {
    let c = false;
    for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
      const [xi, yi] = ring[i], [xj, yj] = ring[j];
      if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c;
    }
    return c;
  }

  // seeds: [{n, x, y}] label positions in pixels. If a fill swallows another ward's label
  // (dashed boundary leaked), retry with stronger gap filling.
  function traceLabels(gray, W, H, seeds, opt) {
    const results = [], skipped = [];
    const maxGap = opt.maxGap || 6;
    const barriers = {};
    const getBarrier = g => (barriers[g] || (barriers[g] = buildBarrier(gray, W, H, opt.threshold, g)));
    seeds.forEach((s, idx) => {
      if (results.some(r => r.n === s.n && pointInRing(s.x, s.y, r.ring))) { skipped.push({ ...s, reason: 'same piece as another label' }); return; }
      let accepted = null;
      for (let g = opt.gap; g <= maxGap && !accepted; g++) {
        const r = traceNearLabel(gray, W, H, s.x, s.y, { ...opt, gap: g, barrier: getBarrier(g) });
        if (r.error) continue;
        const swallows = seeds.some((o, j) => j !== idx && o.n !== s.n && pointInRing(o.x, o.y, r.ring));
        if (!swallows) accepted = { ...s, ring: r.ring, pixels: r.pixels, gap: g };
      }
      accepted ? results.push(accepted) : skipped.push({ ...s, reason: 'boundary not closed' });
    });
    return { results, skipped };
  }

  const api = { buildBarrier, floodFill, traceOuter, simplifyRing, traceRegion, traceOutline, traceNearLabel, traceLabels, pointInRing };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.AutoTrace = api;
})(this);
