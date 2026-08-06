/* ============================================================
   Griffin Museum — Mobile Companion (prototype)
   Reuses the kiosk routing model verbatim:
     - within-floor edges weighted by Euclidean pixel distance
     - cross-floor movement ONLY through connectorId groups,
       each hop costing a fixed 60px
     - step-free (accessible) mode allows floor changes via
       elevator↔elevator connector pairs only
   Consumes the kiosk's exported graph schema directly:
     floors: [{id,name,level,width,height,image}]
     nodes:  [{id,name,type,x,y,floorId,connectorId?,
               visitorDestination?,visitorCategory?}]
     edges:  [{id,from,to}]

   The kiosk QR carries the plan in the URL, e.g.
     mobile/index.html?plan=Science%20Storms,U-505%20Submarine&origin=n84
   Params: plan=<names|ids>  done=<names>  origin=<id>  access=1
   ============================================================ */

'use strict';

const CONNECTOR_WEIGHT = 60;   // kiosk: nominal cost of a vertical connector
const WALK_PX_PER_MIN = 520;   // ~scale for "~X min" on a 1920px-wide floor
const ROUTE_ANIM_MS = 9000;    // kiosk route animation (9s ease-out)

const State = {
  nodes: {}, order: [], edges: [],
  floors: {}, floorByLevel: {},
  accessible: false,
  origin: null,
  plan: [], done: new Set(), planIndex: 0,
  lastNodeId: null,
  navContext: 'plan', navDest: null,
  route: null, segments: [], segIndex: 0,
  _nextIndex: null,
};

/* ---------------- helpers ---------------- */
const $ = s => document.querySelector(s);
const el = (t, c, x) => { const e = document.createElement(t); if (c) e.className = c; if (x != null) e.textContent = x; return e; };
const pick = (o, ks, d) => { for (const k of ks) if (o[k] !== undefined && o[k] !== null) return o[k]; return d; };
const isVertical = t => t === 'stairs' || t === 'elevator' || t === 'escalator';
const euclid = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const levelOf = n => (State.floors[n.floorId] ? State.floors[n.floorId].level : 0);
const floorName = lvl => (State.floorByLevel[lvl] ? State.floorByLevel[lvl].name : 'Level ' + lvl);
const nodeLabel = n => (n.visitorDestination || n.name || n.id);

function deriveCategory(n) {
  if (n.visitorCategory) return n.visitorCategory;
  const t = n.type;
  if (/exhibit/.test(t)) return 'exhibits';
  if (t === 'restroom') return 'amenities';
  if (isVertical(t)) return 'transit';
  if (t === 'exit') return /park/i.test(n.visitorDestination || n.name || '') ? 'parking' : 'exit';
  return 'hidden';
}

/* ---------------- graph loading ---------------- */
function normalizeGraph(raw) {
  State.floors = {}; State.floorByLevel = {};
  pick(raw, ['floors', 'levels'], []).forEach(f => {
    const o = {
      id: String(pick(f, ['id'], pick(f, ['level'], 0))),
      name: String(pick(f, ['name', 'label', 'title'], 'Level')),
      level: Number(pick(f, ['level', 'floor'], 0)),
      width: Number(pick(f, ['width', 'w'], 1920)),
      height: Number(pick(f, ['height', 'h'], 1080)),
      image: pick(f, ['image', 'img', 'map'], null),
    };
    State.floors[o.id] = o; State.floorByLevel[o.level] = o;
  });

  State.nodes = {}; State.order = []; State.nodesByExhibitId = {};
  pick(raw, ['nodes', 'points'], []).forEach(r => {
    const id = String(pick(r, ['id', 'nodeId'], ''));
    if (!id) return;
    const n = {
      id,
      name: String(pick(r, ['name', 'label', 'title'], id)),
      type: String(pick(r, ['type', 'kind'], 'intersection')),
      x: Number(pick(r, ['x', 'left'], 0)),
      y: Number(pick(r, ['y', 'top'], 0)),
      floorId: String(pick(r, ['floorId', 'floor'], '')),
      connectorId: pick(r, ['connectorId', 'connector'], '') || '',
      visitorDestination: pick(r, ['visitorDestination'], '') || '',
      visitorCategory: pick(r, ['visitorCategory', 'category'], '') || '',
      exhibitId: String(pick(r, ['exhibitId'], '')) || '',
    };
    n.level = levelOf(n);
    n.label = nodeLabel(n);
    n.category = deriveCategory(n);
    State.nodes[id] = n; State.order.push(id);
    if (n.exhibitId) (State.nodesByExhibitId[n.exhibitId] = State.nodesByExhibitId[n.exhibitId] || []).push(id);
  });

  State.edges = [];
  pick(raw, ['edges', 'links'], []).forEach(e => {
    const from = String(pick(e, ['from', 'source', 'a'], ''));
    const to = String(pick(e, ['to', 'target', 'b'], ''));
    if (State.nodes[from] && State.nodes[to]) State.edges.push({ from, to });
  });
  // tolerate per-node connection lists too (alternate exports)
  pick(raw, ['nodes'], []).forEach(r => {
    const from = String(pick(r, ['id'], ''));
    (pick(r, ['connections', 'neighbors', 'adj'], []) || []).forEach(c => {
      const to = String(typeof c === 'object' ? pick(c, ['id', 'to'], '') : c);
      if (State.nodes[from] && State.nodes[to]) State.edges.push({ from, to });
    });
  });

  State.origin = String(pick(raw, ['activeKioskId', 'origin', 'kioskOrigin'], '')) || '';
}

/* ---------------- routing (mirrors kiosk buildAdj + dijkstra) -------------- */
function buildAdj(accessible) {
  const adj = {};
  State.order.forEach(id => (adj[id] = []));
  State.edges.forEach(e => {
    const a = State.nodes[e.from], b = State.nodes[e.to];
    if (!a || !b) return;
    const w = euclid(a, b);
    adj[e.from].push({ to: e.to, w });
    adj[e.to].push({ to: e.from, w });
  });
  const groups = {};
  Object.values(State.nodes).forEach(n => {
    if (isVertical(n.type) && String(n.connectorId).trim()) {
      const k = String(n.connectorId).trim();
      (groups[k] = groups[k] || []).push(n);
    }
  });
  Object.values(groups).forEach(g => {
    for (let i = 0; i < g.length; i++) for (let j = i + 1; j < g.length; j++) {
      if (g[i].floorId === g[j].floorId) continue;
      if (accessible && !(g[i].type === 'elevator' && g[j].type === 'elevator')) continue;
      adj[g[i].id].push({ to: g[j].id, w: CONNECTOR_WEIGHT });
      adj[g[j].id].push({ to: g[i].id, w: CONNECTOR_WEIGHT });
    }
  });
  return adj;
}

function dijkstra(startId, goalSet, accessible) {
  if (!State.nodes[startId]) return null;
  const adj = buildAdj(accessible);
  const dist = {}, prev = {}, done = {};
  State.order.forEach(id => (dist[id] = Infinity));
  dist[startId] = 0;
  while (true) {
    let u = null, best = Infinity;
    for (const id in dist) if (!done[id] && dist[id] < best) { best = dist[id]; u = id; }
    if (u === null) break;
    done[u] = true;
    if (goalSet.has(u)) {
      const path = []; let c = u;
      while (c !== undefined) { path.unshift(c); c = prev[c]; }
      return { path, dist: dist[u] };
    }
    adj[u].forEach(e => { const nd = dist[u] + e.w; if (nd < dist[e.to]) { dist[e.to] = nd; prev[e.to] = u; } });
  }
  return null;
}

const selIds = sel => (sel && Array.isArray(sel.ids)) ? sel.ids : (typeof sel === 'string' ? [sel] : []);

// nearest reachable node in the destination group (kiosk behavior)
function buildRoute(startSel, destSel, accessible) {
  const starts = selIds(startSel);
  const destSet = new Set(selIds(destSel));
  let best = null;
  for (const s of starts) {
    const r = dijkstra(s, destSet, accessible);
    if (r && (!best || r.dist < best.dist)) best = r;
  }
  return best;
}

function splitSegments(path) {
  const segs = [];
  let cur = { level: State.nodes[path[0]].level, nodes: [path[0]], transfer: null };
  for (let i = 1; i < path.length; i++) {
    const a = State.nodes[path[i - 1]], b = State.nodes[path[i]];
    if (a.level !== b.level) {
      cur.transfer = {
        label: String(a.connectorId || b.connectorId || a.name).trim(),
        type: isVertical(a.type) ? a.type : b.type,
        toLevel: b.level,
        toName: floorName(b.level),
        dir: b.level > a.level ? 'Up' : 'Down',
      };
      segs.push(cur);
      cur = { level: b.level, nodes: [b.id], transfer: null };
    } else {
      cur.nodes.push(b.id);
    }
  }
  segs.push(cur);
  return segs;
}

/* ---------------- search entries ---------------- */
const SEARCH_TABS = [
  { id: 'all', label: 'All', match: () => true },
  { id: 'exhibits', label: 'Exhibits', match: e => e.kind === 'exhibits' },
  { id: 'amenities', label: 'Amenities', match: e => e.kind === 'amenities' },
  { id: 'transit', label: 'Stairs & elevators', match: e => e.kind === 'transit' },
  { id: 'exits', label: 'Exits & parking', match: e => e.kind === 'exit' || e.kind === 'parking' },
];

function searchEntries() {
  const entries = [];
  // exhibits grouped by name (handles multi-entrance / same name on two floors)
  const ex = {};
  Object.values(State.nodes).forEach(n => { if (/exhibit/.test(n.type)) (ex[n.name] = ex[n.name] || []).push(n.id); });
  Object.keys(ex).sort().forEach(name =>
    entries.push({ kind: 'exhibits', label: name, ids: ex[name], sample: State.nodes[ex[name][0]] }));
  // transit grouped by connectorId (named shafts: Yellow Stairs, Silver Elevator…)
  const tr = {};
  Object.values(State.nodes).forEach(n => {
    if (isVertical(n.type) && String(n.connectorId).trim()) {
      const k = String(n.connectorId).trim(); (tr[k] = tr[k] || []).push(n.id);
    }
  });
  Object.keys(tr).sort().forEach(k =>
    entries.push({ kind: 'transit', label: k, ids: tr[k], sample: State.nodes[tr[k][0]] }));
  // labeled amenities / exits / parking grouped by visitorDestination
  const vd = {};
  Object.values(State.nodes).forEach(n => {
    const v = String(n.visitorDestination || '').trim();
    if (!v || isVertical(n.type)) return;
    (vd[v] = vd[v] || []).push(n.id);
  });
  Object.keys(vd).sort().forEach(v => {
    const ids = vd[v], sample = State.nodes[ids[0]];
    entries.push({ kind: deriveCategory(sample), label: v, ids, sample });
  });
  return entries;
}

/* ---------------- screen router ---------------- */
function show(id) {
  document.querySelectorAll('.screen').forEach(s => s.classList.remove('is-active'));
  const scr = document.getElementById(id);
  scr.classList.add('is-active');
  scr.scrollTop = 0;
}

/* ---------------- MY PLAN ---------------- */
function planList() { return State.plan; }
function doneCount() { return State.plan.filter(p => State.done.has(p.label)).length; }

function renderPlan() {
  const list = planList();
  const total = list.length;
  const dc = doneCount();
  const pct = total ? Math.round((dc / total) * 100) : 0;
  $('#plan-progress-fill').style.width = pct + '%';
  $('#plan-progress-meta').innerHTML =
    `<span>${dc} of ${total} exhibits</span><span>${pct}% complete</span>`;

  const ul = $('#plan-stops'); ul.innerHTML = '';
  list.forEach((p, i) => {
    const isDone = State.done.has(p.label);
    const li = el('li', 'stop' + (isDone ? ' done' : ''));
    li.appendChild(el('span', 'stop-dot', isDone ? '✓' : String(i + 1)));
    const body = el('div');
    body.appendChild(el('div', 'stop-name', p.label));
    body.appendChild(el('div', 'stop-sub', floorName(p.sample.level)));
    li.appendChild(body); ul.appendChild(li);
  });

  const hasProgress = dc > 0 && dc < total;
  $('#plan-continue').classList.toggle('hidden', !hasProgress);
  $('#plan-start').textContent = dc === 0 ? 'Start visit' : 'Restart visit';
}

function firstUnvisited() {
  const list = planList();
  for (let i = 0; i < list.length; i++) if (!State.done.has(list[i].label)) return i;
  return list.length;
}

function goToStop(index, isFirst) {
  const list = planList();
  if (index >= list.length) { renderAllDone(); return; }
  State.planIndex = index;
  State.navContext = 'plan';
  const dest = list[index];
  State.navDest = dest;
  $('#stop-kicker').textContent = isFirst ? 'Your first stop is' : 'Your next stop is';
  $('#stop-name').textContent = dest.label;
  $('#stop-meta').textContent = floorName(dest.sample.level);
  $('#stop-ticket').classList.toggle('hidden', !dest.sample.ticketed);
  show('screen-stop');
}

function renderAllDone() {
  State.navContext = 'plan';
  $('#arrival-title').textContent = 'Visit complete';
  $('#arrival-sub').textContent = "You've reached every stop on your plan.";
  $('#arrival-continue').classList.add('hidden');
  $('#arrival-back-plan').classList.remove('hidden');
  $('#arrival-else').classList.remove('hidden');
  show('screen-arrival');
}

function walkMinutes(dist, transfers) { return Math.max(1, Math.round(dist / WALK_PX_PER_MIN) + transfers); }

/* ---------------- NAVIGATION ---------------- */
function startNavigation(destSel) {
  const route = buildRoute({ ids: [State.origin] }, destSel, State.accessible);
  if (!route) { alert('No step-free route is available there. Try turning step-free off.'); return; }
  State.navDest = destSel; State.route = route;
  State.segments = splitSegments(route.path); State.segIndex = 0;
  renderNav(); show('screen-nav');
}

function recalcFromNewStart(startSel) {
  const route = buildRoute(startSel, State.navDest, State.accessible);
  if (!route) { alert('No route found from there. Pick another spot.'); return; }
  State.origin = route.path[0]; State.route = route;
  State.segments = splitSegments(route.path); State.segIndex = 0;
  renderNav(); show('screen-nav');
}

function destText() {
  if (State.navDest && State.navDest.label) return State.navDest.label;
  return State.nodes[State.route.path.slice(-1)[0]].label;
}

function renderNav() {
  const seg = State.segments[State.segIndex];
  const isLast = State.segIndex === State.segments.length - 1;
  $('#nav-dest').textContent = destText();
  $('#nav-floor').textContent = floorName(seg.level);
  drawMap(seg, isLast);
  renderDirections(seg, isLast);

  // Continue action is the primary button below the instructions: advance to
  // the next floor, or (on the final floor) confirm arrival and continue.
  const advance = $('#nav-advance');
  advance.textContent = isLast ? "I've Arrived" : 'Navigate to Next Floor →';

  requestAnimationFrame(() => animateRoute());
}

function advanceFloor() {
  if (State.segIndex < State.segments.length - 1) { State.segIndex++; renderNav(); }
}

function goPrevFloor() {
  if (State.segIndex > 0) { State.segIndex--; renderNav(); }
}

// Top-left back button: step back a floor if we're past the first one,
// otherwise leave navigation and return to the previous screen.
function navBack() {
  if (State.segIndex > 0) { goPrevFloor(); return; }
  if (State.navContext === 'plan') show('screen-stop');
  else show('screen-find-start');
}

function continueNav() {
  if (State.segIndex < State.segments.length - 1) advanceFloor();
  else arrive();
}

function arrive() { State.navContext === 'plan' ? renderArrivalPlan() : renderArrivalFind(); show('screen-arrival'); }

function renderArrivalPlan() {
  const reached = planList()[State.planIndex];
  if (reached) {
    State.done.add(reached.label);
    // set current position to the reached node (nearest instance we routed to)
    State.origin = State.route ? State.route.path.slice(-1)[0] : State.origin;
    State.lastNodeId = State.origin;
  }
  const next = firstUnvisited();
  const hasNext = next < planList().length;
  $('#arrival-title').textContent = 'Destination reached';
  $('#arrival-sub').textContent = reached ? `You've arrived at ${reached.label}.` : "You've arrived.";
  $('#arrival-continue').classList.toggle('hidden', !hasNext);
  if (hasNext) $('#arrival-continue').textContent = 'Continue to next stop';
  $('#arrival-back-plan').classList.remove('hidden');
  $('#arrival-else').classList.remove('hidden');
  State._nextIndex = next;
}

function renderArrivalFind() {
  const last = State.route.path.slice(-1)[0];
  State.origin = last; State.lastNodeId = last;
  $('#arrival-title').textContent = 'Destination reached';
  $('#arrival-sub').textContent = `You've arrived at ${State.nodes[last].label}.`;
  $('#arrival-continue').classList.add('hidden');
  $('#arrival-back-plan').classList.add('hidden');
  $('#arrival-else').classList.remove('hidden');
}

/* ---------------- MAP (real floor image + cropped viewBox) ---------------- */
const SVGNS = 'http://www.w3.org/2000/svg';
const XLINK = 'http://www.w3.org/1999/xlink';
function svgEl(tag, attrs) { const e = document.createElementNS(SVGNS, tag); for (const k in attrs) e.setAttribute(k, attrs[k]); return e; }
function pointToSegmentDistance(px, py, a, b){
  const vx = b.x - a.x;
  const vy = b.y - a.y;
  const lengthSquared = vx * vx + vy * vy;

  let t = 0;

  if(lengthSquared > 0){
    t = (
      (px - a.x) * vx +
      (py - a.y) * vy
    ) / lengthSquared;

    t = Math.max(0, Math.min(1, t));
  }

  const closestX = a.x + t * vx;
  const closestY = a.y + t * vy;

  return Math.hypot(
    px - closestX,
    py - closestY
  );
}

function chooseStartLabelPosition(start, routePoints, W, H, sw){
  const distanceFromMarker = sw * 5.8;

  const directions = [
    -Math.PI / 2,       // above
     Math.PI / 2,       // below
     Math.PI,           // left
     0,                 // right
    -3 * Math.PI / 4,   // upper left
    -Math.PI / 4,       // upper right
     3 * Math.PI / 4,   // lower left
     Math.PI / 4        // lower right
  ];

  const horizontalPadding = sw * 8.5;
  const verticalPadding = sw * 4.5;

  let best = {
    x: start.x,
    y: start.y - distanceFromMarker,
    score: -Infinity
  };

  directions.forEach(angle => {
    const rawX =
      start.x +
      Math.cos(angle) * distanceFromMarker;

    const rawY =
      start.y +
      Math.sin(angle) * distanceFromMarker;

    const x = Math.max(
      horizontalPadding,
      Math.min(W - horizontalPadding, rawX)
    );

    const y = Math.max(
      verticalPadding,
      Math.min(H - verticalPadding, rawY)
    );

    let routeDistance = Infinity;

    if(routePoints.length < 2){
      routeDistance = distanceFromMarker;
    }else{
      for(let i = 0; i < routePoints.length - 1; i++){
        routeDistance = Math.min(
          routeDistance,
          pointToSegmentDistance(
            x,
            y,
            routePoints[i],
            routePoints[i + 1]
          )
        );
      }
    }

    const edgePenalty =
      Math.hypot(rawX - x, rawY - y) * 2;

    const score =
      routeDistance - edgePenalty;

    if(score > best.score){
      best = { x, y, score };
    }
  });

  return best;
}
function drawMap(seg, isLast) {
  const floor = State.floorByLevel[seg.level] || { width: 1920, height: 1080, image: null };
  const svg = $('#nav-map'); svg.innerHTML = '';
  const pts = seg.nodes.map(id => State.nodes[id]);
  const W = floor.width || 1920, H = floor.height || 1080;

  // Always show the whole floor so the visitor keeps full context of where
  // they are. The map is centred in the card; the route sits in its true
  // location on the floor rather than being zoomed into.
  svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
  svg.style.aspectRatio = `${W} / ${H}`;

  if (floor.image) {
    const img = svgEl('image', { x: 0, y: 0, width: W, height: H, preserveAspectRatio: 'none' });
    img.setAttributeNS(XLINK, 'href', floor.image);
    img.setAttribute('href', floor.image);
    svg.appendChild(img);
  }

const sw = Math.max(14, Math.min(W, H) * 0.017);

const d = seg.nodes
  .map((id, i) =>
    (i ? 'L' : 'M') +
    State.nodes[id].x + ' ' +
    State.nodes[id].y
  )
  .join(' ');

/* Wider white outline behind the route */
const halo = svgEl('path', {
  class: 'route-halo',
  d
});

halo.setAttribute('stroke-width', sw * 2.6);
svg.appendChild(halo);

/* Thicker orange route */
const rp = svgEl('path', {
  class: 'route-line',
  d
});

rp.id = 'route-path';
rp.setAttribute('stroke-width', sw);
svg.appendChild(rp);

const s = pts[0];
const e = pts[pts.length - 1];

/* Large You Are Here marker */
const startHalo = svgEl('circle', {
  class: 'origin-halo',
  cx: s.x,
  cy: s.y,
  r: sw * 3.1
});
svg.appendChild(startHalo);

const startRing = svgEl('circle', {
  class: 'origin-ring',
  cx: s.x,
  cy: s.y,
  r: sw * 1.75,
  'stroke-width': sw * 0.55
});
svg.appendChild(startRing);

const startCore = svgEl('circle', {
  class: 'origin-core',
  cx: s.x,
  cy: s.y,
  r: sw * 0.75
});
svg.appendChild(startCore);

const labelPosition =
  chooseStartLabelPosition(
    s,
    pts,
    W,
    H,
    sw
  );

const startLabel = svgEl('text', {
  class: 'origin-label',
  x: labelPosition.x,
  y: labelPosition.y,
  'text-anchor': 'middle',
  'dominant-baseline': 'middle',
  'font-size': sw * 2.35
});

startLabel.textContent = 'You Are Here';
svg.appendChild(startLabel);

/* Destination marker remains orange */
if (isLast) {
  svg.appendChild(svgEl('circle', {
    class: 'pin',
    cx: e.x,
    cy: e.y,
    r: sw * 2
  }));

  svg.appendChild(svgEl('circle', {
    class: 'pin-core',
    cx: e.x,
    cy: e.y,
    r: sw * 0.75
  }));
}
}

function animateRoute() {
  const path = $('#route-path');
  if (!path) return;
  if (window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches) return;
  const len = path.getTotalLength();
  path.style.transition = 'none';
  path.style.strokeDasharray = len;
  path.style.strokeDashoffset = len;
  void path.getBoundingClientRect();
  path.style.transition = `stroke-dashoffset ${ROUTE_ANIM_MS}ms cubic-bezier(0.16,0.84,0.32,1)`;
  path.style.strokeDashoffset = '0';
}

function renderDirections(seg, isLast) {
  const box = $('#nav-directions'); box.innerHTML = '';
  const steps = [];
  const start = State.nodes[seg.nodes[0]];
  steps.push(State.segIndex === 0 ? `Start at ${start.label}` : `Continue from ${floorName(seg.level)}`);
  for (let i = 1; i < seg.nodes.length - 1; i++) {
    const n = State.nodes[seg.nodes[i]];
    if (n.type === 'intersection' || n.type === 'entrance') continue;
    if (/exhibit/.test(n.type) && !isLast) steps.push(`Pass ${n.name}`);
    else if (n.visitorDestination) steps.push(`Pass ${n.visitorDestination}`);
  }
  const end = State.nodes[seg.nodes.slice(-1)[0]];
  if (isLast) steps.push(`Arrive at ${end.label}`);
  else if (seg.transfer) steps.push(`Take ${seg.transfer.label} ${seg.transfer.dir} to ${seg.transfer.toName}`);

  steps.slice(0, 8).forEach((t, i) => {
    const row = el('div', 'direction');
    row.appendChild(el('span', 'step-n', String(i + 1)));
    row.appendChild(el('span', 'step-text', t));
    box.appendChild(row);
  });
}

/* ---------------- SEARCH UI ---------------- */
let _searchTarget = null, _searchTab = 'all', _startSel = null;

function openSearch(target, title, subtitle) {
  _searchTarget = target; _searchTab = 'all';
  $('#search-title').textContent = title;
  $('#search-sub').textContent = subtitle || '';
  $('#search-input').value = '';
  renderTabs(); renderResults();
  show('screen-search');
  setTimeout(() => $('#search-input').focus(), 300);
}

function renderTabs() {
  const wrap = $('#search-tabs'); wrap.innerHTML = '';
  SEARCH_TABS.forEach(t => {
    const b = el('button', 'tab' + (t.id === _searchTab ? ' is-active' : ''), t.label);
    b.onclick = () => { _searchTab = t.id; renderTabs(); renderResults(); };
    wrap.appendChild(b);
  });
}

function renderResults() {
  const q = $('#search-input').value.trim().toLowerCase();
  const tab = SEARCH_TABS.find(t => t.id === _searchTab);
  const box = $('#search-results'); box.innerHTML = '';
  const items = searchEntries().filter(e => tab.match(e)).filter(e => !q || e.label.toLowerCase().includes(q));
  if (!items.length) { box.appendChild(el('div', 'empty', 'No matches. Try another word.')); return; }
  items.forEach(e => {
    const btn = el('button', 'result');
    const body = el('div');
    body.appendChild(el('div', 'result-name', e.label));
    const levels = [...new Set(e.ids.map(id => floorName(State.nodes[id].level)))];
    body.appendChild(el('div', 'result-meta', levels.join(' · ')));
    btn.appendChild(body);
    btn.onclick = () => chooseSearch(e);
    box.appendChild(btn);
  });
}

function chooseSearch(entry) {
  if (_searchTarget === 'start') {
    _startSel = entry;
    openSearch('dest', 'Where do you want to go?', 'Starting from ' + entry.label);
  } else if (_searchTarget === 'dest') {
    State.navContext = 'find';
    const route = buildRoute(_startSel, entry, State.accessible);
    if (!route) { alert('No route found between those two. Try step-free off, or a different pair.'); return; }
    State.origin = route.path[0]; State.navDest = entry; State.route = route;
    State.segments = splitSegments(route.path); State.segIndex = 0;
    renderNav(); show('screen-nav');
  } else if (_searchTarget === 'recover') {
    recalcFromNewStart(entry);
  }
}

/* ---------------- accessibility toggle ---------------- */
function setAccessible(on) {
  State.accessible = on;

  document.querySelectorAll('[data-access-toggle]').forEach(button => {
    button.setAttribute('aria-pressed', String(on));
    button.classList.toggle('is-active', on);

    button.textContent = on
      ? 'Accessible Route: On'
      : 'Accessible Route: Off';
  });
}
/* ---------------- wiring ---------------- */
function wire() {
  const reload = document.getElementById('error-reload');
  if (reload) reload.onclick = () => location.reload();
  $('#go-plan').onclick = () => { renderPlan(); show('screen-plan'); };
  $('#go-find').onclick = () => show('screen-find-start');
  document.querySelectorAll('[data-access-toggle]').forEach(t => t.onclick = () => setAccessible(!State.accessible));

  $('#plan-back').onclick = () => show('screen-home');
  $('#plan-start').onclick = () => {
    if (doneCount() > 0) {
      // "Restart visit" — clear all progress and show the reset plan (0%, nothing ticked)
      State.done.clear();
      State.planIndex = 0;
      State._nextIndex = null;
      renderPlan();
    } else {
      // "Start visit" — begin from the first stop
      goToStop(0, true);
    }
  };
  $('#plan-continue').onclick = () => goToStop(firstUnvisited(), false);

  $('#stop-back').onclick = () => { renderPlan(); show('screen-plan'); };
  $('#stop-go').onclick = () => startNavigation(State.navDest);

  $('#find-start-back').onclick = () => show('screen-home');
  $('#find-last').onclick = () => {
    const startId = State.lastNodeId || State.origin;
    _startSel = { kind: 'node', label: State.nodes[startId].label, ids: [startId], sample: State.nodes[startId] };
    openSearch('dest', 'Where do you want to go?', 'Starting from ' + State.nodes[startId].label);
  };
  $('#find-new').onclick = () => openSearch('start', 'Where are you starting?', 'Pick a place you can see near you');

  $('#search-back').onclick = () => {
    if (_searchTarget === 'dest') show('screen-find-start');
    else if (_searchTarget === 'recover') show('screen-nav');
    else show('screen-find-start');
  };
  $('#search-input').oninput = renderResults;

  $('#nav-back').onclick = () => navBack();
  $('#nav-advance').onclick = () => continueNav();
  $('#nav-recover').onclick = () => openSearch('recover', 'Set your location', 'Pick a place you can see near you');
  $('#nav-exit').onclick = () => show('screen-home');

  $('#arrival-continue').onclick = () => goToStop(State._nextIndex != null ? State._nextIndex : firstUnvisited(), false);
  $('#arrival-else').onclick = () => show('screen-find-start');
  $('#arrival-back-plan').onclick = () => { renderPlan(); show('screen-plan'); };
}

/* ---------------- boot ---------------- */
function resolvePlanToken(tok) {
  if (State.nodes[tok]) { // node id
    const n = State.nodes[tok];
    // Expand to every graph node that shares this exhibit's stable id, so the
    // router can pick the nearest reachable entrance. Association is by id only.
    let ids = [tok];
    if (n.exhibitId && State.nodesByExhibitId && State.nodesByExhibitId[n.exhibitId]) {
      ids = State.nodesByExhibitId[n.exhibitId].slice();
    }
    return { kind: 'exhibits', label: n.name, ids, sample: n };
  }
  // exhibitId token (forward-compatible: a QR could carry an exhibitId directly)
  if (State.nodesByExhibitId && State.nodesByExhibitId[tok] && State.nodesByExhibitId[tok].length) {
    const ids = State.nodesByExhibitId[tok].slice();
    return { kind: 'exhibits', label: State.nodes[ids[0]].name, ids, sample: State.nodes[ids[0]] };
  }
  // legacy name / visitorDestination match (kept only for backward compatibility)
  const ids = Object.values(State.nodes).filter(n => n.name === tok || n.visitorDestination === tok).map(n => n.id);
  if (ids.length) return { kind: 'exhibits', label: tok, ids, sample: State.nodes[ids[0]] };
  return null;
}

/* ---------------- transfer persistence (localStorage) ---------------- */
const LS_PLAN = 'griffin.wayfinding.plan.v1';

function saveImportedPlan(stopIds, startId, access) {
  try {
    localStorage.setItem(LS_PLAN, JSON.stringify({ stops: stopIds, start: startId, access: !!access, ts: Date.now() }));
  } catch (e) { /* private mode / storage disabled: transfer still works this session */ }
}
function loadImportedPlan() {
  try {
    const raw = localStorage.getItem(LS_PLAN);
    if (!raw) return null;
    const o = JSON.parse(raw);
    if (o && Array.isArray(o.stops) && o.stops.length) return o;
  } catch (e) {}
  return null;
}

/* Greedy nearest-first ordering of plan stops, reusing the existing Dijkstra
   routing engine (no new routing logic). Starts from the visitor's origin and
   always visits the closest remaining stop next. Unreachable stops keep their
   given order at the end. */
function orderPlanNearestFirst(stops, startId, accessible) {
  if (!stops || stops.length <= 1) return (stops || []).slice();
  const remaining = stops.slice();
  const ordered = [];
  let curIds = [startId];
  while (remaining.length) {
    let bestI = -1, best = null;
    for (let i = 0; i < remaining.length; i++) {
      const r = buildRoute({ ids: curIds }, remaining[i], accessible);
      if (r && (best === null || r.dist < best.dist)) { best = r; bestI = i; }
    }
    if (bestI < 0) { remaining.forEach(s => ordered.push(s)); break; }
    ordered.push(remaining[bestI]);
    curIds = [best.path[best.path.length - 1]];
    remaining.splice(bestI, 1);
  }
  return ordered;
}

/* Resolve, validate against the graph, and de-duplicate a list of stop tokens
   (node ids preferred; names/visitorDestination also accepted). Invalid tokens
   are silently ignored. */
function resolveStops(tokens) {
  const seen = new Set();
  const out = [];
  tokens.forEach(tok => {
    const e = resolvePlanToken(tok);
    if (e && e.ids && e.ids.length) {
      const key = e.ids.slice().sort().join('|');
      if (!seen.has(key)) { seen.add(key); out.push(e); }
    }
  });
  return out;
}

/* Parse URL parameters and set up state. Returns a routing hint for boot():
   'directions' | 'plan' | 'home'. Supports the new mode-based scheme and the
   original aliases (plan/origin/access/done) for backward compatibility. */
function readParams() {
  const p = new URLSearchParams(location.search);
  const list = v => (v ? v.split(',').map(s => s.trim()).filter(Boolean) : []);

  // --- accessibility: new avoidStairs=true|1 ; legacy access=1 ---
  const av = (p.get('avoidStairs') || '').toLowerCase();
  const wantAccess = (av === 'true' || av === '1' || p.get('access') === '1');
  if (wantAccess) setAccessible(true);

  // --- origin/start: new start ; legacy origin ; default n84 ---
  const startRaw = p.get('start') || p.get('origin');
  if (startRaw && State.nodes[startRaw]) State.origin = startRaw;
  if (!State.origin || !State.nodes[State.origin]) State.origin = State.nodes['n84'] ? 'n84' : State.order[0];
  State.lastNodeId = State.origin;

  const mode = (p.get('mode') || '').toLowerCase();
  const destRaw = p.get('destination');

  // ---------- DIRECTIONS transfer ----------
  if (mode === 'directions' || (!mode && destRaw)) {
    const dest = destRaw ? resolvePlanToken(destRaw) : null;
    if (dest) { State._pendingDest = dest; return 'directions'; }
    State._transferError = 'That destination link looks incomplete. Showing the home screen instead.';
    return 'home';
  }

  // ---------- PLAN transfer ----------
  const stopTokens = list(p.get('stops')).length ? list(p.get('stops')) : list(p.get('plan'));
  if (mode === 'plan' || stopTokens.length) {
    const stops = resolveStops(stopTokens);
    if (stops.length) {
      const ordered = orderPlanNearestFirst(stops, State.origin, State.accessible);
      State.plan = ordered;
      list(p.get('done')).forEach(d => State.done.add(d));
      saveImportedPlan(ordered.map(s => (s.ids && s.ids[0]) || s.label), State.origin, State.accessible);
      return 'plan';
    }
    State._transferError = 'That plan link didn’t contain any stops we recognise. Showing the home screen instead.';
    return 'home';
  }

  // ---------- No transfer params ----------
  // Restore a previously imported plan if we have one; otherwise fall back to the
  // original demo itinerary. Either way we land on the home screen.
  const saved = loadImportedPlan();
  if (saved) {
    if (saved.access) setAccessible(true);
    if (saved.start && State.nodes[saved.start]) { State.origin = saved.start; State.lastNodeId = saved.start; }
    const stops = resolveStops(saved.stops);
    if (stops.length) State.plan = stops;
  }
  if (!State.plan.length) {
    ['Science Storms', 'U-505 Submarine', 'Wright Flyer'].forEach(nm => {
      const e = resolvePlanToken(nm); if (e) State.plan.push(e);
    });
  }
  return 'home';
}

/* Start a directions route imported from the kiosk. Unlike the interactive
   startNavigation(), a failed auto-route never alerts — it quietly lands the
   visitor on the home screen so they can navigate normally. */
function startTransferDirections(destSel) {
  const route = buildRoute({ ids: [State.origin] }, destSel, State.accessible);
  if (!route) return false;
  State.navContext = 'find';
  State.navDest = destSel; State.route = route;
  State.segments = splitSegments(route.path); State.segIndex = 0;
  renderNav(); show('screen-nav');
  return true;
}

async function boot() {
  wire();
  try {
    const res = await fetch('graph.json', { cache: 'no-store' });
    if (!res.ok) throw new Error('HTTP ' + res.status);
    normalizeGraph(await res.json());
    const route = readParams();

    if (route === 'directions' && State._pendingDest) {
      if (startTransferDirections(State._pendingDest)) return;
      // Route couldn't be built (e.g. step-free with no accessible path): fall home.
      show('screen-home');
      return;
    }
    if (route === 'plan') {
      renderPlan(); show('screen-plan');
      return;
    }
    show('screen-home');
  } catch (err) {
    console.error(err);
    const be = document.getElementById('boot-error'); if (be) be.classList.remove('hidden');
    show('screen-error');
  }
}
document.addEventListener('DOMContentLoaded', boot);
