#!/usr/bin/env node
'use strict';
/*
  migrate-exhibit-ids.js  —  one-time data migration

  Adds a stable `exhibitId` field to every exhibit node in graph.json, so the
  kiosk↔graph↔mobile association no longer depends on display-name matching.

  WHY A MIGRATION USES NAMES (once): the current graph nodes have no exhibitId
  yet, so we must seed them. We do that here, offline, with a REVIEWABLE mapping
  (exhibit id → the node name(s) it currently appears under). After this runs,
  nothing at runtime ever compares names again — association is purely by id.

  Usage:
    node tools/migrate-exhibit-ids.js <input graph.json> <output graph.json>

  The mapping below is the single source of truth for the migration. Each entry:
    { id: '<stable exhibitId>', names: [ '<current graph node name>', ... ] }
  `names` lists every graph node name (any punctuation/spelling variant, or the
  several entrances of a multi-node exhibit) that belongs to this exhibit. Names
  are matched case-insensitively and ignoring punctuation/whitespace, so e.g.
  "Yesterday's Main Street" (curly apostrophe) still matches "Yesterday's Main
  Street" (straight apostrophe). Add a name here to attach a node to an exhibit;
  never rely on names at runtime.
*/

const fs = require('fs');

// exhibitId → graph node names that represent it (incl. variants & extra entrances)
const MAP = [
  { id: 'spiderman',        names: ['Marvel’s Spider-Man: Beyond Amazing — The Exhibition', 'Spider-Man Gallery 1', 'Spider-Man Gallery 2'] },
  { id: 'annefrank',        names: ['Anne Frank The Exhibition', 'Anne Frank'] },
  { id: 'poweringfuture',   names: ['Powering the Future'] },
  { id: 'paultazewell',     names: ['Crafting Character: The Costumes of Paul Tazewell', 'Griffin Studio (Crafting Character)'] },
  { id: 'spacecenter',      names: ['Henry Crown Space Center', 'Henry Crown Center'] },
  { id: 'sciencestorms',    names: ['Science Storms'] },                    // two entrances: main + balcony
  { id: 'u505',             names: ['U-505 Submarine'] },
  { id: 'bicycle',          names: ['Art of the Bicycle', 'The Art of the Bicycle'] },
  { id: 'fairycastle',      names: ["Colleen Moore's Fairy Castle"] },
  { id: 'earthrevealed',    names: ['Earth Revealed'] },
  { id: 'extremeice',       names: ['Extreme Ice'] },
  { id: 'farmtech',         names: ['Farm Tech'] },
  { id: 'simulators',       names: ['Flight and Motion Simulators'] },
  { id: 'numbers',          names: ['Numbers in Nature: A Mirror Maze', "Number's in Nature"] },
  { id: 'zephyr',           names: ['Pioneer Zephyr'] },
  { id: 'ships',            names: ['Ships Gallery'] },
  { id: 'steelmakers',      names: ['Steelmakers'] },
  { id: 'jollyball',        names: ['Swiss Jollyball', 'Swiss Jolly Ball'] },
  { id: 'takeflight',       names: ['Take Flight', '727 Take Flight'] },
  { id: 'blueparadox',      names: ['The Blue Paradox', 'The Blue Paradox Entrance'] },
  { id: 'trainstory',       names: ['The Great Train Story'] },
  { id: 'ideafactory',      names: ['The Idea Factory', 'Idea Factory'] },
  { id: 'transportgallery', names: ['Transportation Gallery'] },
  { id: 'vrtransporter',    names: ['VR Transporter'] },                    // no graph node yet (see report)
  { id: 'whispering',       names: ['Whispering Gallery'] },
  { id: 'you',              names: ['YOU! The Experience'] },
  { id: 'mainstreet',       names: ["Yesterday’s Main Street", "Yesterday's Main Street"] },
];

const norm = s => String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, '');

function migrate(inPath, outPath) {
  const g = JSON.parse(fs.readFileSync(inPath, 'utf8'));
  const exhibitNodes = g.nodes.filter(n => /exhibit/.test(String(n.type || '')));

  // normalized node-name → [node,...]
  const byNorm = {};
  exhibitNodes.forEach(n => { (byNorm[norm(n.name)] = byNorm[norm(n.name)] || []).push(n); });

  const assigned = new Set();
  const report = { matched: [], multi: [], unmatchedExhibits: [], unmatchedNodes: [] };

  MAP.forEach(entry => {
    const hit = [];
    entry.names.forEach(nm => (byNorm[norm(nm)] || []).forEach(n => { if (!hit.includes(n)) hit.push(n); }));
    if (!hit.length) { report.unmatchedExhibits.push(entry.id); return; }
    hit.forEach(n => { n.exhibitId = entry.id; assigned.add(n.id); });
    const rec = { id: entry.id, nodes: hit.map(n => n.id) };
    report.matched.push(rec);
    if (hit.length > 1) report.multi.push(rec);
  });

  exhibitNodes.forEach(n => { if (!assigned.has(n.id)) report.unmatchedNodes.push({ id: n.id, name: n.name }); });

  fs.writeFileSync(outPath, JSON.stringify(g, null, 2));
  return report;
}

// ---- run ----
const [, , inPath, outPath] = process.argv;
if (!inPath || !outPath) { console.error('usage: node migrate-exhibit-ids.js <in.json> <out.json>'); process.exit(2); }
const r = migrate(inPath, outPath);
console.log('exhibits matched : ' + r.matched.length + '/' + MAP.length);
console.log('multi-node exhibits:');
r.multi.forEach(m => console.log('   ' + m.id + ' → ' + m.nodes.join(', ')));
console.log('exhibits with NO graph node (stay non-routable until a node is added):');
console.log('   ' + (r.unmatchedExhibits.join(', ') || '(none)'));
console.log('graph exhibit-nodes with no kiosk exhibit (left untouched):');
console.log('   ' + r.unmatchedNodes.map(n => n.id + ':' + n.name).join(', '));
