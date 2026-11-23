// Ad-hoc: print the lowered nodes of one diagram, flagging orphans.
//   node tests/nodes.mjs <claims-file> <diagram-name>
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { viewerDir as dir } from "./data.mjs";
const ctx = vm.createContext({ console, performance });
for (const f of ["lower.js", "graph.js", "read.js"])
  vm.runInContext(fs.readFileSync(path.join(dir, f), "utf8"), ctx, { filename: f });
const run = e => vm.runInContext(e, ctx);

const entries = JSON.parse(fs.readFileSync(path.resolve(process.argv[2]), "utf8"));
run(`GRAPHS = lowerAll(${JSON.stringify(entries)})`);
const key = JSON.parse(run("JSON.stringify(Object.keys(GRAPHS))"))
  .find(k => k.endsWith(process.argv[3]));
run(`G = GRAPHS[${JSON.stringify(key)}]`);
const ns = JSON.parse(run(`JSON.stringify(Object.entries(G.nodes).map(([id, n]) => ({
  id, kind: n.kind, label: (n.label || "").slice(0, 34),
  region: n.region ? n.region.kind : null, stored: !!n.stored, deps: n.deps || [] })))`));
const referenced = new Set();
for (const n of ns) for (const d of n.deps) referenced.add(d);
const only = process.argv[4];
for (const n of ns) {
  const orphan = referenced.has(n.id) ? "" : "  <-- ORPHAN";
  if (only && !(n.stored || orphan)) continue;
  console.log(`  ${n.id.padEnd(9)}${n.kind.padEnd(7)}${n.label.padEnd(36)}` +
    `region=${String(n.region).padEnd(7)} stored=${n.stored}${orphan}`);
}
