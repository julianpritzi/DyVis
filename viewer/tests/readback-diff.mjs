// Why a diagram does not read back: which runs the picture offers that the
// claim does not, and which the claim asks for that the picture does not.
// `reads back: no` is a yes/no answer to a question whose useful form is
// "which run disagrees"; this prints that.
//
//   node tests/readback-diff.mjs <diagram-name>
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { viewerDir as dir, claimsDir as claimDir, shortName } from "./data.mjs";
const want = process.argv[2];
if (!want) throw new Error("usage: readback-diff.mjs <diagram-name>");

const ctx = vm.createContext({ console, performance });
for (const f of ["lower.js", "graph.js", "read.js"])
  vm.runInContext(fs.readFileSync(path.join(dir, f), "utf8"), ctx, { filename: f });
const run = expr => vm.runInContext(expr, ctx);

for (const file of fs.readdirSync(claimDir).filter(f => f.endsWith(".json"))) {
  const entries = JSON.parse(fs.readFileSync(path.join(claimDir, file), "utf8"));
  const claimOf = Object.fromEntries(
    entries.map(e => [shortName(e.name), e.claim]));
  run(`GRAPHS = lowerAll(${JSON.stringify(entries)})`);
  for (const name of run("Object.keys(GRAPHS)")) {
    if (name !== want) continue;
    run(`G = GRAPHS[${JSON.stringify(name)}]; expanded.clear();`);
    run("for (const id of Object.keys(G.nodes)) if (revealed(id).length) expanded.add(id);");
    run(`__claim = ${JSON.stringify(claimOf[name] ?? null)}`);
    const pic = run("canon(readGraph(elements())).split('  |  ')");
    const cla = run("claimCanon(__claim, pretty).split('  |  ')");
    const only = (a, b) => a.filter(x => !b.includes(x));
    const pOnly = only(pic, cla), cOnly = only(cla, pic);
    console.log(`${name}\n  runs: picture ${pic.length}, claim ${cla.length}, shared ${pic.length - pOnly.length}`);
    const atoms = s => s.split(" & ");
    // A run present on neither side is usually one atom away from one that is,
    // and the nearest match is what says which atom.
    for (const p of pOnly) {
      let best = null, bestD = 1e9;
      for (const c of cOnly) {
        const d = only(atoms(p), atoms(c)).length + only(atoms(c), atoms(p)).length;
        if (d < bestD) { bestD = d; best = c; }
      }
      console.log(`\n  PICTURE ONLY (nearest claim run differs by ${bestD} atom(s)):`);
      if (best) {
        for (const a of only(atoms(p), atoms(best))) console.log(`    picture has: ${a}`);
        for (const a of only(atoms(best), atoms(p))) console.log(`    claim has:   ${a}`);
      } else console.log(`    ${p}`);
    }
    if (!pOnly.length) for (const c of cOnly) console.log(`\n  CLAIM ONLY:\n    ${c}`);
    process.exit(0);
  }
}
console.log(`no such diagram: ${want}`);
