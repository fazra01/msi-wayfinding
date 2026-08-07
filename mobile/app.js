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
  hasVisitedDestination: false,
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
  { id: 'exits', label: 'Exits & parking', match: e => e.kind === 'exit' || e.kind === 'parking' },
];
function searchEntries(target = 'dest') {
  const entries = [];

  function nodesByName(name) {
    return Object.values(State.nodes)
      .filter(n => String(n.name || '').trim() === name)
      .map(n => n.id);
  }

  function nodesByDestination(name) {
    return Object.values(State.nodes)
      .filter(n => String(n.visitorDestination || '').trim() === name)
      .map(n => n.id);
  }

  function addEntry(kind, label, ids) {
    if (!ids || !ids.length) return;

    entries.push({
      kind,
      label,
      ids,
      sample: State.nodes[ids[0]]
    });
  }


  /* ================= EXHIBITS ================= */

  const exhibits = {};

  Object.values(State.nodes).forEach(n => {
    if (/exhibit/.test(n.type)) {
      (exhibits[n.name] = exhibits[n.name] || []).push(n.id);
    }
  });

  Object.keys(exhibits)
    .sort()
    .forEach(name => {
      addEntry('exhibits', name, exhibits[name]);
    });


/* ================= AMENITIES ================= */

if (target === 'start' || target === 'recover') {

  /* Allowed starting points */
  addEntry(
    'amenities',
    'Museum Kitchen',
    nodesByName('Museum Kitchen')
  );

  addEntry(
    'amenities',
    'Outside Seating',
  nodesByName('Outside Seating')
  );

  addEntry(
    'amenities',
    "Stan's Donut",
    nodesByName("Stan's Donut")
  );

  addEntry(
    'amenities',
    'Museum Store',
    nodesByName('Museum Store')
  );

  addEntry(
    'amenities',
    'Vending',
    nodesByName('Vending')
  );

  addEntry(
    'amenities',
    'Tickets',
    nodesByName('Tickets')
  );

  addEntry(
    'amenities',
    'Guest Services',
    nodesByName('Guest Services')
  );

} else {

  /* Destination amenities */
  addEntry(
    'amenities',
    'Museum Kitchen',
    nodesByName('Museum Kitchen')
  );

  addEntry(
    'amenities',
    "Stan's Donut",
    nodesByName("Stan's Donut")
  );

  addEntry(
    'amenities',
    'Museum Store',
    nodesByName('Museum Store')
  );

  addEntry(
    'amenities',
    'Outside Seating',
    nodesByName('Outside Seating')
  );

  addEntry(
    'amenities',
    'Restrooms',
    nodesByDestination('Restrooms')
  );

  addEntry(
    'amenities',
    'Family Restrooms',
    nodesByDestination('Family Restrooms')
  );

  addEntry(
    'amenities',
    'Vending',
    nodesByName('Vending')
  );

  addEntry(
    'amenities',
    'Tickets',
    nodesByName('Tickets')
  );

  addEntry(
    'amenities',
    'Guest Services',
    nodesByName('Guest Services')
  );
}
  /* ================= PARKING ================= */

  addEntry(
    'parking',
    'Parking A, B, C',
    nodesByName('Exit to Parking (A, B, C)')
  );

  addEntry(
    'parking',
    'Parking D, E, F',
    nodesByName('Exit to Parking (D, E, F)')
  );
  /* Parking help — destination only */
  if (target === 'dest') {
    const guestServicesIds = nodesByName('Guest Services');

    if (guestServicesIds.length) {
      entries.push({
        kind: 'parking',
        label: "I don't remember where I parked",
        routeLabel: 'Guest Services',
        ids: guestServicesIds,
        sample: State.nodes[guestServicesIds[0]],
        parkingHelp: true
      });
    }
  }

  /* ================= EXIT ================= */

  addEntry(
    'exit',
    'Exit',
    nodesByDestination('Exit')
  );


  return entries;
}
/* ---------------- screen router ---------------- */
function show(id) {
  document.querySelectorAll('.screen').forEach(s => s.classList.remove('is-active'));
  const scr = document.getElementById(id);
  scr.classList.add('is-active');
  scr.scrollTop = 0;
}
function renderFindStart() {
  const button = $('#find-last');
  const title = $('#find-last-title');
  const description = $('#find-last-name');

  const hasRealLastDestination = Boolean(
    State.hasVisitedDestination &&
    State.lastNodeId &&
    State.nodes[State.lastNodeId]
  );

  const startId = hasRealLastDestination
    ? State.lastNodeId
    : State.origin;

  const startNode = startId
    ? State.nodes[startId]
    : null;

  button.disabled = !startNode;

  if (hasRealLastDestination) {
    title.textContent = 'Start from Last Destination';
    description.textContent = `Last visited: ${startNode.label}`;
  } else {
    title.textContent = 'Start from Kiosk Location';

    description.textContent = startNode
      ? `Starting point: ${startNode.label}`
      : 'Kiosk location unavailable';
  }
}
/* ---------------- MY PLAN ---------------- */
let planReorderMode = false;
let planSortable = null;


function planStopToken(stop) {
  return (
    stop.ids &&
    stop.ids.length
      ? stop.ids[0]
      : stop.label
  );
}


function savePlanOrder() {

  saveImportedPlan(
    State.plan.map(planStopToken),
    State.origin,
    State.accessible
  );
}


function enablePlanSorting() {

  const list =
    $('#plan-stops');

  if (planSortable) {
    planSortable.destroy();
    planSortable = null;
  }

  if (!planReorderMode) {
    return;
  }


  planSortable =
    new Sortable(list, {

      animation: 220,

      /* Important for touch screens */
      delay: 220,
      delayOnTouchOnly: true,
      touchStartThreshold: 4,

      /* Only upcoming stops can move */
      draggable: '.stop:not(.done)',

      ghostClass: 'stop-ghost',
      chosenClass: 'stop-chosen',
      dragClass: 'stop-dragging',

      /*
        Prevent an upcoming stop from being dragged
        through a completed stop.
      */
      onMove: function(evt) {

        if (
          evt.related &&
          evt.related.classList.contains('done')
        ) {
          return false;
        }

        return true;
      },


      onEnd: function(evt) {

        if (
          evt.oldIndex == null ||
          evt.newIndex == null ||
          evt.oldIndex === evt.newIndex
        ) {
          return;
        }


        const moved =
          State.plan.splice(
            evt.oldIndex,
            1
          )[0];


        State.plan.splice(
          evt.newIndex,
          0,
          moved
        );


        savePlanOrder();

        /*
          Re-render so the numbers update:
          1, 2, 3, 4...
        */
        renderPlan();
      }
    });
}
function planList() { return State.plan; }
function doneCount() { return State.plan.filter(p => State.done.has(p.label)).length; }

function renderPlan() {

  const list = planList();

  const total = list.length;
  const dc = doneCount();

  const pct =
    total
      ? Math.round((dc / total) * 100)
      : 0;


  $('#plan-progress-fill').style.width =
    pct + '%';


  $('#plan-progress-meta').innerHTML =
    `<span>${dc} of ${total} exhibits</span>` +
    `<span>${pct}% complete</span>`;


  const reorderButton =
    $('#plan-reorder');

  const reorderHint =
    $('#plan-reorder-hint');


  reorderButton.textContent =
    planReorderMode
      ? 'Done'
      : 'Reorder stops';


  reorderButton.classList.toggle(
    'is-active',
    planReorderMode
  );


  reorderHint.classList.toggle(
    'hidden',
    !planReorderMode
  );


  const ul =
    $('#plan-stops');

  ul.classList.toggle(
    'is-reordering',
    planReorderMode
  );

  ul.innerHTML = '';


  list.forEach((p, i) => {

    const isDone =
      State.done.has(p.label);


    const li =
      el(
        'li',
        'stop' +
          (isDone ? ' done' : '')
      );


    li.appendChild(
      el(
        'span',
        'stop-dot',
        isDone
          ? '✓'
          : String(i + 1)
      )
    );


    const body =
      el('div', 'stop-body');


    body.appendChild(
      el(
        'div',
        'stop-name',
        p.label
      )
    );


    li.appendChild(body);


    /*
      Grip appears only while reorder mode is on
      and only for stops that are not completed.
    */
    if (
      planReorderMode &&
      !isDone
    ) {

      li.appendChild(
        el(
          'span',
          'stop-drag-handle',
          '⋮⋮'
        )
      );
    }


    ul.appendChild(li);
  });


  const hasProgress =
    dc > 0 &&
    dc < total;


  $('#plan-continue').classList.toggle(
    'hidden',
    !hasProgress ||
    planReorderMode
  );


  $('#plan-start').classList.toggle(
    'hidden',
    planReorderMode
  );


  $('#plan-start').textContent =
    dc === 0
      ? 'Start visit'
      : 'Restart visit';


  enablePlanSorting();
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
    State.hasVisitedDestination = true;
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
  State.origin = last;
  State.lastNodeId = last;
  State.hasVisitedDestination = true;
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

/* ============================================================
   LANDMARK-BASED MOBILE DIRECTIONS
   Mirrors the kiosk direction logic.
   ============================================================ */

const MOBILE_LANDMARK_MAX_DISTANCE = 150;
const MOBILE_LANDMARK_SIDE_MIN_DISTANCE = 40;
const MOBILE_LANDMARK_MAX_PER_FLOOR = 3;


/* Is this a recognizable exhibit? */
function isMobileRouteLandmark(n) {
  if (!n) return false;

  return (
    /exhibit/i.test(String(n.type || '')) ||
    String(n.visitorCategory || '').toLowerCase() === 'exhibits'
  );
}


/* Find nearest point on a section of the orange route */
function mobileLandmarkProjection(p, a, b) {

  const dx = b.x - a.x;
  const dy = b.y - a.y;

  const len2 = dx * dx + dy * dy;

  if (!len2) {
    return {
      t: 0,
      dist: Math.hypot(
        p.x - a.x,
        p.y - a.y
      ),
      side: ''
    };
  }

  let t =
    ((p.x - a.x) * dx +
     (p.y - a.y) * dy) / len2;

  t = Math.max(0, Math.min(1, t));

  const x = a.x + dx * t;
  const y = a.y + dy * t;

  const dist =
    Math.hypot(
      p.x - x,
      p.y - y
    );

  /*
    SVG coordinates increase downward.
    Negative = left of walking direction.
    Positive = right.
  */
  const cross =
    dx * (p.y - a.y) -
    dy * (p.x - a.x);

  let side = '';

  if (dist >= MOBILE_LANDMARK_SIDE_MIN_DISTANCE) {
    side = cross < 0 ? 'left' : 'right';
  }

  return {
    t,
    dist,
    side
  };
}


/* Find up to 3 exhibit landmarks close to this floor's route */
function mobileRouteLandmarks(seg, isLast) {

  const pts =
    seg.nodes
      .map(id => State.nodes[id])
      .filter(Boolean);

  if (pts.length < 2) return [];

  const floorId = pts[0].floorId;

  /* Every node actually used by the orange route */
  const routeSet =
    new Set(seg.nodes);


  /* Build graph-neighbor lookup */
  const neighbors = {};

  State.edges.forEach(edge => {

    if (!neighbors[edge.from]) {
      neighbors[edge.from] = new Set();
    }

    if (!neighbors[edge.to]) {
      neighbors[edge.to] = new Set();
    }

    neighbors[edge.from].add(edge.to);
    neighbors[edge.to].add(edge.from);
  });


  /* Distance travelled along the route */
  const cumulative = [0];

  for (let i = 1; i < pts.length; i++) {

    cumulative[i] =
      cumulative[i - 1] +
      Math.hypot(
        pts[i].x - pts[i - 1].x,
        pts[i].y - pts[i - 1].y
      );
  }

  const totalLength =
    cumulative[cumulative.length - 1];

  const edgeBuffer =
    Math.min(
      70,
      totalLength * 0.12
    );


  const startNode = pts[0];

  const finalNode =
    State.route &&
    State.route.path &&
    State.route.path.length
      ? State.nodes[
          State.route.path[
            State.route.path.length - 1
          ]
        ]
      : null;


  const startName =
    String(
      startNode.name ||
      startNode.visitorDestination ||
      startNode.label ||
      ''
    )
      .trim()
      .toLowerCase();


  const destinationName =
    finalNode
      ? String(
          finalNode.name ||
          finalNode.visitorDestination ||
          finalNode.label ||
          ''
        )
          .trim()
          .toLowerCase()
      : '';


  const byName = {};


  Object.values(State.nodes).forEach(n => {

    if (!isMobileRouteLandmark(n)) return;

    if (n.floorId !== floorId) return;


    const name =
      String(
        n.name ||
        n.visitorDestination ||
        n.label ||
        ''
      ).trim();

    if (!name) return;


    const key =
      name.toLowerCase();

    if (key === startName) return;
    if (destinationName && key === destinationName) return;


    /* ======================================================
       RULE 1:
       Exhibit node is ACTUALLY on the orange route.
       This is always trustworthy.
       ====================================================== */

    if (routeSet.has(n.id)) {

      const routeIndex =
        seg.nodes.indexOf(n.id);

      const candidate = {
        kind: 'exhibit',
        name,
        dist: 0,
        along: cumulative[routeIndex],
        side: '',
        priority: 0
      };

      if (
        candidate.along >= edgeBuffer &&
        (!isLast ||
         candidate.along <= totalLength - edgeBuffer)
      ) {
        byName[key] = candidate;
      }

      return;
    }


    /* ======================================================
       RULE 2:
       Exhibit is BESIDE an actual route segment.

       It must:
       - be close to the segment
       - connect directly to that corridor in graph.json
       - project onto the MIDDLE of the segment
         rather than merely being near a corner/intersection
       ====================================================== */

    let best = null;


    for (let i = 0; i < pts.length - 1; i++) {

      const a = pts[i];
      const b = pts[i + 1];

      const projection =
        mobileLandmarkProjection(
          n,
          a,
          b
        );


      /*
        IMPORTANT:
        The exhibit must branch directly from one of the
        two nodes making up this exact route segment.
      */
      const connectedToSegment =
        (neighbors[n.id] &&
          (
            neighbors[n.id].has(a.id) ||
            neighbors[n.id].has(b.id)
          ));


      if (!connectedToSegment) {
        continue;
      }


/*
  If the landmark is beside the END of a route segment,
  allow it only when it genuinely branches off to the side
  of the direction the visitor is walking.

  This allows things like Idea Factory beside the route,
  while rejecting exhibits that are merely ahead/behind
  near an intersection.
*/
if (
  projection.t < 0.18 ||
  projection.t > 0.82
) {

  const anchorIndex =
    projection.t < 0.5
      ? i
      : i + 1;

  const anchor =
    pts[anchorIndex];

  const previous =
    pts[Math.max(0, anchorIndex - 1)];

  const next =
    pts[Math.min(
      pts.length - 1,
      anchorIndex + 1
    )];


  /* Local walking direction through this route node */
  const routeDX =
    next.x - previous.x;

  const routeDY =
    next.y - previous.y;


  /* Direction from route node toward the exhibit */
  const landmarkDX =
    n.x - anchor.x;

  const landmarkDY =
    n.y - anchor.y;


  const routeLength =
    Math.hypot(
      routeDX,
      routeDY
    );

  const landmarkLength =
    Math.hypot(
      landmarkDX,
      landmarkDY
    );


  if (
    routeLength > 0 &&
    landmarkLength > 0
  ) {

    /*
      0 = perfectly beside you
      1 = directly ahead/behind you
    */
    const alignment =
      Math.abs(
        (
          routeDX * landmarkDX +
          routeDY * landmarkDY
        ) /
        (
          routeLength *
          landmarkLength
        )
      );


    /*
      Only accept endpoint landmarks that are
      substantially to the SIDE of the route.
    */
    if (alignment > 0.45) {
      continue;
    }
  }
}


      /* Much stricter than the old 150px rule */
      if (projection.dist > 90) {
        continue;
      }


      const segmentLength =
        Math.hypot(
          b.x - a.x,
          b.y - a.y
        );


      const along =
        cumulative[i] +
        segmentLength * projection.t;


      if (
        !best ||
        projection.dist < best.dist
      ) {

        best = {
          kind: 'exhibit',
          name,
          dist: projection.dist,
          along,
          side: projection.side,
          priority: 1
        };
      }
    }


    if (!best) return;

    if (best.along < edgeBuffer) return;

    if (
      isLast &&
      best.along > totalLength - edgeBuffer
    ) {
      return;
    }


    /*
      Prefer an exhibit actually ON the route over
      a merely nearby side landmark.
    */
    if (
      !byName[key] ||
      best.priority < byName[key].priority ||
      (
        best.priority === byName[key].priority &&
        best.dist < byName[key].dist
      )
    ) {
      byName[key] = best;
    }

  });


  let candidates =
    Object.values(byName);


  /*
    Prioritize:
    1. exhibits actually on the route
    2. then legitimate side landmarks
    */
  candidates.sort((a, b) => {

    if (a.priority !== b.priority) {
      return a.priority - b.priority;
    }

    return a.dist - b.dist;
  });


  candidates =
    candidates.slice(
      0,
      MOBILE_LANDMARK_MAX_PER_FLOOR
    );


  /* Finally display them in walking order */
  candidates.sort(
    (a, b) => a.along - b.along
  );


  return candidates;
}


/* Staircases the orange route ACTUALLY passes through */
function mobileRouteStairCallouts(seg) {

  const pts =
    seg.nodes
      .map(id => State.nodes[id])
      .filter(Boolean);

  if (pts.length < 3) return [];


  const cumulative = [0];

  for (let i = 1; i < pts.length; i++) {

    cumulative[i] =
      cumulative[i - 1] +
      Math.hypot(
        pts[i].x - pts[i - 1].x,
        pts[i].y - pts[i - 1].y
      );
  }


  const stairs = [];


  /*
    Ignore first and last nodes.

    This prevents:
    - repeating the stairs you just came from
    - repeating the stairs used as the actual floor connector
  */
  for (let i = 1; i < pts.length - 1; i++) {

    const n = pts[i];

    if (n.type !== 'stairs') continue;


    const name =
      n.name && n.name.trim()
        ? n.name.trim()
        : 'Stairs';


    stairs.push({
      kind: 'stairs',
      name,
      along: cumulative[i]
    });
  }


  return stairs;
}


/* Build the actual written directions */
function renderDirections(seg, isLast) {

  const box =
    $('#nav-directions');

  box.innerHTML = '';


  const landmarks =
    mobileRouteLandmarks(
      seg,
      isLast
    );


  const stairs =
    mobileRouteStairCallouts(seg);


  /*
    Combine landmarks and stairs so everything appears
    in the actual order the visitor encounters it.
  */
  const events = [
    ...landmarks,
    ...stairs
  ];


  events.sort(
    (a, b) => a.along - b.along
  );


  const steps = [];


  events.forEach(event => {

    /* Staircase */
    if (event.kind === 'stairs') {

      steps.push(
        `Pass the ${event.name}.`
      );

      return;
    }


    /* Exhibit */
    let text =
      `Pass ${event.name}`;

    if (event.side) {
      text +=
        ` on your ${event.side}`;
    }

    text += '.';

    steps.push(text);
  });


  /* FINAL FLOOR */
  if (isLast) {

    const end =
      State.nodes[
        seg.nodes[
          seg.nodes.length - 1
        ]
      ];

    steps.push(
      `Arrive at ${end.label}.`
    );
  }


  /* FLOOR CHANGE */
  else if (seg.transfer) {

    const transferNode =
      State.nodes[
        seg.nodes[
          seg.nodes.length - 1
        ]
      ];


    const connectorName =
      transferNode &&
      transferNode.name &&
      transferNode.name.trim()
        ? transferNode.name.trim()
        : seg.transfer.label;


    const direction =
      String(
        seg.transfer.dir || ''
      ).toLowerCase();


    steps.push(
      `Take the ${connectorName} ${direction} to ${seg.transfer.toName}.`
    );
  }


  /* Render numbered cards */
  steps.forEach((text, i) => {

    const row =
      el(
        'div',
        'direction'
      );


    row.appendChild(
      el(
        'span',
        'step-n',
        String(i + 1)
      )
    );


    row.appendChild(
      el(
        'span',
        'step-text',
        text
      )
    );


    box.appendChild(row);
  });
}

//* ---------------- SEARCH UI ---------------- */

let _searchTarget = null;
let _searchCategory = null;
let _startSel = null;
let _startConfirmTimer = null;
function confirmStartingPoint(entry) {

  _startSel = entry;

  $('#start-confirm-name').textContent =
    entry.label;

  show('screen-start-confirmed');

  clearTimeout(_startConfirmTimer);

  _startConfirmTimer = setTimeout(() => {
    openCategory('dest');
  }, 2600);
}

/* ============================================================
   CATEGORY SCREEN
   ============================================================ */

function openCategory(target) {
  _searchTarget = target;
  _searchCategory = null;

  const title = $('#category-title');
  const sub = $('#category-sub');

  if (target === 'dest') {
    title.textContent = 'Where do you want to go?';

    sub.textContent = _startSel
      ? 'Starting from ' + _startSel.label
      : 'Choose a destination category.';
  }

  else if (target === 'recover') {
    title.textContent = 'Where are you now?';
    sub.textContent = 'Choose something you can see near you.';
  }

  else {
    title.textContent = "What's your starting point?";
    sub.textContent = 'Choose something you can see near you.';
  }

  show('screen-category');
}


/* ============================================================
   CATEGORY → SEARCH
   ============================================================ */

const CATEGORY_COPY = {

  exhibits: {
    label: 'Exhibits',
    startTitle: 'Which exhibit are you near?',
    destTitle: 'Which exhibit do you want to visit?',
    placeholder: 'Search exhibits...'
  },

  amenities: {
    label: 'Amenities',
    startTitle: 'Which amenity are you near?',
    destTitle: 'Which amenity do you need?',
    placeholder: 'Search amenities...'
  },

  exit: {
    label: 'Exits',
    startTitle: 'Which exit are you near?',
    destTitle: 'Which exit do you want?',
    placeholder: 'Search exits...'
  },

  parking: {
    label: 'Parking',
    startTitle: 'Which parking area are you near?',
    destTitle: 'Where did you park?',
    placeholder: 'Type your parking letter...'
  }
};


function chooseCategory(category) {
  _searchCategory = category;


  /* EXIT:
     There is only one Exit option, so skip the search page. */
  if (category === 'exit') {

    const exitEntry =
      availableSearchEntries()
        .find(entry => entry.kind === 'exit');

    if (!exitEntry) return;

    chooseSearch(exitEntry);
    return;
  }


  /* PARKING:
     Use the dedicated big-card screen. */
  if (category === 'parking') {

    renderParkingChoices();
    show('screen-parking');

    return;
  }


  /* EXHIBITS + AMENITIES:
     Continue to the normal search screen. */
  const copy = CATEGORY_COPY[category];

  const isDestination =
    _searchTarget === 'dest';

  $('#search-category-kicker').textContent =
    copy.label;

  $('#search-title').textContent =
    isDestination
      ? copy.destTitle
      : copy.startTitle;


  const searchSub = $('#search-sub');

  if (category === 'exhibits') {

    searchSub.classList.remove('hidden');

    searchSub.textContent =
      isDestination
        ? 'Start typing the name of the exhibit.'
        : 'Start typing the name you can see.';

  } else {

    /* Amenities does not need helper text */
    searchSub.classList.add('hidden');
  }


  const searchInput = $('#search-input');

  /* Only Exhibits needs a search bar */
  if (category === 'exhibits') {
    searchInput.classList.remove('hidden');
    searchInput.placeholder = copy.placeholder;
    searchInput.value = '';
  } else {
    searchInput.classList.add('hidden');
    searchInput.value = '';
  }

  renderResults();

  show('screen-search');

  /* Only open keyboard for Exhibits */
  if (category === 'exhibits') {
    setTimeout(() => {
      searchInput.focus();
    }, 250);
  }
}

function renderParkingChoices() {

  const wrap = $('#parking-choices');

  wrap.innerHTML = '';


  const isDestination =
    _searchTarget === 'dest';


  $('#parking-title').textContent =
    isDestination
      ? 'Where did you park?'
      : 'Which parking area are you near?';


  $('#parking-sub').textContent =
    isDestination
      ? 'Choose the color and letter you remember.'
      : 'Choose the color and letter you can see.';


  /* availableSearchEntries already respects:
     - starting vs destination
     - selected starting point removal
     - parking help being destination-only
  */
  const parkingItems =
    availableSearchEntries();


  parkingItems.forEach(entry => {

    const button =
      el('button', 'parking-choice-card');


    /* I DON'T REMEMBER */
    if (entry.parkingHelp) {

      const kicker =
        el(
          'span',
          'parking-choice-kicker',
          'Need help?'
        );

      const title =
        el(
          'span',
          'parking-choice-title parking-help-title',
          "I DON'T REMEMBER WHERE I PARKED"
        );

      const description =
        el(
          'span',
          'parking-choice-desc',
          'Take me to Guest Services.'
        );

      button.appendChild(kicker);
      button.appendChild(title);
      button.appendChild(description);

    }


    /* PARKING A B C / D E F */
    else {

      const title =
        el(
          'span',
          'parking-choice-title',
          'PARKING'
        );

      const badges =
        el(
          'div',
          'parking-choice-badges'
        );


      const letters =
        entry.label === 'Parking A, B, C'
          ? ['A', 'B', 'C']
          : ['D', 'E', 'F'];


      letters.forEach(letter => {

        badges.appendChild(
          el(
            'span',
            'parking-letter parking-' +
              letter.toLowerCase(),
            letter
          )
        );

      });


      button.appendChild(title);
      button.appendChild(badges);
    }


    button.onclick = () => {
      chooseSearch(entry);
    };


    wrap.appendChild(button);
  });
}

/* ============================================================
   SMART / FUZZY SEARCH
   ============================================================ */

function normalizeSearchText(value) {
  return String(value || '')
    .toLowerCase()
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .replace(/&/g, ' and ')
    .replace(/[^a-z0-9]+/g, ' ')
    .trim()
    .replace(/\s+/g, ' ');
}


function compactSearchText(value) {
  return normalizeSearchText(value)
    .replace(/\s+/g, '');
}


function levenshtein(a, b) {
  a = normalizeSearchText(a);
  b = normalizeSearchText(b);

  const matrix =
    Array.from(
      { length: b.length + 1 },
      () => Array(a.length + 1).fill(0)
    );

  for (let i = 0; i <= b.length; i++) {
    matrix[i][0] = i;
  }

  for (let j = 0; j <= a.length; j++) {
    matrix[0][j] = j;
  }

  for (let i = 1; i <= b.length; i++) {
    for (let j = 1; j <= a.length; j++) {

      const cost =
        b[i - 1] === a[j - 1]
          ? 0
          : 1;

      matrix[i][j] = Math.min(
        matrix[i - 1][j] + 1,
        matrix[i][j - 1] + 1,
        matrix[i - 1][j - 1] + cost
      );
    }
  }

  return matrix[b.length][a.length];
}


function fuzzySimilarity(a, b) {
  const aa = normalizeSearchText(a);
  const bb = normalizeSearchText(b);

  const longest =
    Math.max(aa.length, bb.length);

  if (!longest) return 1;

  return 1 -
    levenshtein(aa, bb) / longest;
}


/* Helpful museum-specific language */
const SEARCH_ALIASES = {

  'museum store': [
    'gift shop',
    'gift store',
    'shop',
    'store',
    'souvenir'
  ],

  'museum kitchen': [
    'kitchen',
    'food',
    'restaurant',
    'cafeteria'
  ],

  "stan's donut": [
    'stans',
    'stan',
    'donut',
    'donuts',
    'food'
  ],

  'guest services': [
    'guest service',
    'information',
    'information desk',
    'info desk',
    'help desk'
  ],

  'tickets': [
    'ticket',
    'ticket desk',
    'admission'
  ],

  'vending': [
    'vending machine',
    'snacks',
    'drinks'
  ],

  'restrooms': [
    'restroom',
    'bathroom',
    'bathrooms',
    'toilet',
    'toilets',
    'washroom'
  ],

  'family restrooms': [
    'family restroom',
    'family bathroom',
    'family toilet',
    'baby changing'
  ],

  'exit': [
    'exit',
    'way out',
    'leave',
    'leave museum'
  ],

  'parking a b c': [
    'abc',
    'a b c',
    'parking a',
    'parking b',
    'parking c',
    'orange parking',
    'purple parking',
    'green parking'
  ],

  'parking d e f': [
    'def',
    'd e f',
    'parking d',
    'parking e',
    'parking f',
    'blue parking',
    'yellow parking',
    'brown parking'
  ],

  "i don't remember where i parked": [
    'dont remember',
    'forgot',
    'forgot parking',
    'parking help',
    'dont know where i parked'
  ]
};


function searchTermsForEntry(entry) {
  const key =
    normalizeSearchText(entry.label);

  const terms = [
    entry.label
  ];

  const aliases =
    SEARCH_ALIASES[key] || [];

  aliases.forEach(alias =>
    terms.push(alias)
  );

  return terms;
}


function scoreSearchEntry(entry, query) {
  const q =
    normalizeSearchText(query);

  const qc =
    compactSearchText(query);

  if (!q) return 0;

  let best = 0;

  searchTermsForEntry(entry)
    .forEach(term => {

      const t =
        normalizeSearchText(term);

      const tc =
        compactSearchText(term);

      if (t === q) {
        best = Math.max(best, 120);
      }

      else if (t.startsWith(q)) {
        best = Math.max(best, 110);
      }

      else if (t.includes(q)) {
        best = Math.max(best, 100);
      }

      else if (
        qc &&
        tc.includes(qc)
      ) {
        best = Math.max(best, 95);
      }


      /* Typo matching only once user types enough letters */
      if (q.length >= 3) {

        const similarity =
          fuzzySimilarity(q, t);

        if (similarity >= 0.58) {
          best = Math.max(
            best,
            similarity * 88
          );
        }


        /* Handle multi-word misspellings:
           "musuem kichen" → Museum Kitchen */
        const queryWords =
          q.split(' ');

        const termWords =
          t.split(' ');

        let total = 0;

        queryWords.forEach(queryWord => {

          let wordBest = 0;

          termWords.forEach(termWord => {
            wordBest = Math.max(
              wordBest,
              fuzzySimilarity(
                queryWord,
                termWord
              )
            );
          });

          total += wordBest;
        });

        const average =
          total / queryWords.length;

        if (average >= 0.62) {
          best = Math.max(
            best,
            average * 82
          );
        }
      }
    });

  return best;
}


/* ============================================================
   FILTER RESULTS
   ============================================================ */

function categoryMatches(entry) {

  if (_searchCategory === 'exhibits') {
    return entry.kind === 'exhibits';
  }

  if (_searchCategory === 'amenities') {
    return entry.kind === 'amenities';
  }

  if (_searchCategory === 'exit') {
    return entry.kind === 'exit';
  }

  if (_searchCategory === 'parking') {
    return entry.kind === 'parking';
  }

  return false;
}


function availableSearchEntries() {

  let items =
    searchEntries(_searchTarget)
      .filter(categoryMatches);


  /* Destination cannot equal starting point */
  if (
    _searchTarget === 'dest' &&
    _startSel
  ) {

    const startLabel =
      normalizeSearchText(
        _startSel.label
      );

    items = items.filter(entry => {

      const actualDestination =
        normalizeSearchText(
          entry.routeLabel ||
          entry.label
        );

      return actualDestination !==
        startLabel;
    });
  }

  return items;
}


/* ============================================================
   RESULT CARD
   ============================================================ */

function makeSearchResult(entry) {

  const btn = el(
    'button',
    'result' +
      (entry.kind === 'parking'
        ? ' parking-result'
        : '') +
      (entry.parkingHelp
        ? ' parking-help-result'
        : '')
  );

  const body = el('div');


  /* PARKING HELP */
  if (entry.parkingHelp) {

    body.appendChild(
      el(
        'div',
        'result-name',
        "I don't remember where I parked"
      )
    );

    body.appendChild(
      el(
        'div',
        'result-meta',
        'Take me to Guest Services for help.'
      )
    );

  }


  /* PARKING LETTERS */
  else if (
    entry.label === 'Parking A, B, C' ||
    entry.label === 'Parking D, E, F'
  ) {

    const heading =
      el('div', 'parking-heading');

    heading.appendChild(
      el(
        'div',
        'result-name',
        'Parking'
      )
    );

    const badges =
      el('div', 'parking-badges');

    const letters =
      entry.label === 'Parking A, B, C'
        ? ['A', 'B', 'C']
        : ['D', 'E', 'F'];

    letters.forEach(letter => {

      badges.appendChild(
        el(
          'span',
          'parking-letter parking-' +
            letter.toLowerCase(),
          letter
        )
      );

    });

    heading.appendChild(badges);
    body.appendChild(heading);

  }


  /* NORMAL RESULT */
  else {

    body.appendChild(
      el(
        'div',
        'result-name',
        entry.label
      )
    );
  }


  btn.appendChild(body);

  btn.onclick = () =>
    chooseSearch(entry);

  return btn;
}


/* ============================================================
   RENDER SEARCH
   ============================================================ */

function renderResults() {

  const box =
    $('#search-results');

  box.classList.toggle(
    'amenities-grid',
    _searchCategory === 'amenities'
  );

  const query =
    $('#search-input').value.trim();

  box.innerHTML = '';

  const available =
    availableSearchEntries();


  /* Exhibits require typing.
    Amenities, exits and parking show their full list immediately. */
  if (!query) {

    if (_searchCategory === 'exhibits') {

      box.appendChild(
        el(
          'div',
          'search-prompt',
          'Start typing to see matches.'
        )
      );

      return;
    }

    /* Small categories: show every available option */
    available.forEach(entry => {
      box.appendChild(
        makeSearchResult(entry)
      );
    });

    return;
  }


  const matches =
    available
      .map(entry => ({
        entry,
        score:
          scoreSearchEntry(
            entry,
            query
          )
      }))
      .filter(item =>
        item.score >= 55
      )
      .sort((a, b) =>
        b.score - a.score
      )
      .slice(0, 5);


  if (!matches.length) {

    box.appendChild(
      el(
        'div',
        'empty',
        'No close matches. Try another spelling.'
      )
    );

    return;
  }


  matches.forEach(item => {
    box.appendChild(
      makeSearchResult(item.entry)
    );
  });
}


/* ============================================================
   CHOOSE RESULT
   ============================================================ */

function chooseSearch(entry) {

  /* Starting point selected */
  if (_searchTarget === 'start') {

    confirmStartingPoint(entry);

    return;
  }


  /* Destination selected */
  if (_searchTarget === 'dest') {

    State.navContext = 'find';

    const destination =
      entry.routeLabel
        ? {
            ...entry,
            label: entry.routeLabel
          }
        : entry;

    const route =
      buildRoute(
        _startSel,
        destination,
        State.accessible
      );

    if (!route) {

      alert(
        'No route found between those two. Try turning accessible routing off, or choose a different destination.'
      );

      return;
    }

    State.origin =
      route.path[0];

    State.navDest =
      destination;

    State.route =
      route;

    State.segments =
      splitSegments(route.path);

    State.segIndex = 0;

    renderNav();
    show('screen-nav');

    return;
  }


  /* Updating position while navigating */
  if (_searchTarget === 'recover') {
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
  $('#go-find').onclick = () => {
  renderFindStart();
  show('screen-find-start');
  };
  document.querySelectorAll('[data-access-toggle]').forEach(t => t.onclick = () => setAccessible(!State.accessible));

  $('#plan-back').onclick = () => {

  planReorderMode = false;

  renderPlan();

  show('screen-home');
};
  $('#plan-reorder').onclick = () => {

  planReorderMode =
    !planReorderMode;

  renderPlan();
};
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
  const startId =
    State.hasVisitedDestination && State.lastNodeId
      ? State.lastNodeId
      : State.origin;

  const startNode = State.nodes[startId];

  if (!startNode) return;

  const startEntry = {
    kind: 'node',
    label: startNode.label,
    ids: [startId],
    sample: startNode
  };

  confirmStartingPoint(startEntry);
  };
    $('#find-new').onclick = () => {
    openCategory('start');
  };

  $('#search-back').onclick = () => {
  show('screen-category');
};

$('#parking-back').onclick = () => {
  show('screen-category');
};

$('#category-back').onclick = () => {
  if (_searchTarget === 'recover') {
    show('screen-nav');
    return;
  }

  show('screen-find-start');
};


document
  .querySelectorAll('[data-search-category]')
  .forEach(button => {

    button.onclick = () => {
      chooseCategory(
        button.getAttribute(
          'data-search-category'
        )
      );
    };

  });
  $('#search-input').oninput = renderResults;

  $('#nav-back').onclick = () => navBack();
  $('#nav-advance').onclick = () => continueNav();
  $('#nav-recover').onclick = () => {
  openCategory('recover');
  };
  $('#nav-exit').onclick = () => show('screen-home');

  $('#arrival-continue').onclick = () => goToStop(State._nextIndex != null ? State._nextIndex : firstUnvisited(), false);
  $('#arrival-else').onclick = () => {
    renderFindStart();
    show('screen-find-start');
  };  
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
  if (saved.start && State.nodes[saved.start]) {State.origin = saved.start;}
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
