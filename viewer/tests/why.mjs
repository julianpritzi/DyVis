// Scratch diagnostic: why does one diagram not read back as its claim?
//   node viewer/tests/why.mjs <substring-of-name>
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { viewerDir as dir, claimsDir, shortName } from "./data.mjs";
const want = process.argv[2] || "";

const ctx = vm.createContext({ console, performance });
for (const f of ["lower.js", "graph.js", "read.js"])
  vm.runInContext(fs.readFileSync(path.join(dir, f), "utf8"), ctx, { filename: f });
const run = e => vm.runInContext(e, ctx);

const short = a => a.replace(/^check\(/, "?").replace(/^occurs\(/, "@")
  .replace(/^not\(/, "NOT ").replace(/\)$/, "").slice(0, 64);

for (const file of fs.readdirSync(claimsDir).filter(f => f.endsWith(".json"))) {
  const entries = JSON.parse(fs.readFileSync(path.join(dir, "claims", file), "utf8"));
  const claimOf = Object.fromEntries(entries.map(e => [shortName(e.name), e.claim]));
  run(`GRAPHS = lowerAll(${JSON.stringify(entries)})`);
  for (const name of run("Object.keys(GRAPHS)")) {
    if (!name.includes(want)) continue;
    run(`G = GRAPHS[${JSON.stringify(name)}]; expanded.clear();`);
    run("for (const id of Object.keys(G.nodes)) if (revealed(id).length) expanded.add(id);");
    run(`__claim = ${JSON.stringify(claimOf[name] ?? null)}`);
    const pic = run("canon(readGraph(elements())).split('  |  ')").map(r => r.split(" & "));
    const cla = run("claimCanon(__claim, pretty).split('  |  ')").map(r => r.split(" & "));
    console.log(`\n===== ${name}`);
    console.log(`picture ${pic.length} runs, claim ${cla.length} runs`);

    const sub = (a, b) => a.every(x => b.includes(x));
    const omitted = new Map();
    let weaker = 0, stronger = 0, exact = 0, unrelated = 0;
    for (const p of pic) {
      const eq = cla.find(c => sub(p, c) && sub(c, p));
      if (eq) { exact++; continue; }
      const w = cla.find(c => sub(p, c));
      const s = cla.find(c => sub(c, p));
      if (w) {
        weaker++;
        for (const x of w.filter(x => !p.includes(x))) omitted.set(x, (omitted.get(x) || 0) + 1);
      } else if (s) {
        stronger++;
        console.log(`\n  [stronger] picture demands extra:`);
        for (const x of p.filter(x => !s.includes(x))) console.log(`      ${short(x)}`);
      } else {
        unrelated++;
      }
    }
    console.log(`\n  exact ${exact} | WEAKER ${weaker} | stronger ${stronger} | unrelated ${unrelated}`);
    console.log(`\n  atoms the picture DROPS from runs it allows (count x atom):`);
    for (const [a, n] of [...omitted].sort((x, y) => y[1] - x[1]))
      console.log(`    ${n} x  ${a}\n`);
    const missed = cla.filter(c => !pic.some(p => sub(p, c) && sub(c, p)));
    console.log(`  claim runs with no exact picture match: ${missed.length}`);
    // Sharp discriminator: is the whole disagreement about WHICH RUNS THE `∄`
    // MARKS SIT ON, or is the run structure itself different?
    const drop = rs => new Set(rs.map(r =>
      r.filter(a => !a.startsWith("not(")).sort().join(" & ")));
    const [pb, cb] = [drop(pic), drop(cla)];
    const same = pb.size === cb.size && [...pb].every(x => cb.has(x));
    console.log(`  ignoring every ∄ mark: picture ${pb.size} runs, claim ${cb.size} runs -- ` +
                (same ? "IDENTICAL (so the disagreement is only about where the marks go)"
                      : "STILL DIFFERENT (the run structure itself disagrees)"));
    if (!same) {
      for (const x of [...pb].filter(x => !cb.has(x)))
        console.log(`    only in picture: ${x.slice(0, 100)}`);
      for (const x of [...cb].filter(x => !pb.has(x)))
        console.log(`    only in claim:   ${x.slice(0, 100)}`);
    }
    for (const c of missed) {
      console.log(`    - ${c.length} atoms: ${short(c[c.length - 1])}`);
    }
  }
}
