// Approval tests for the diagrams.
//
// The artifact under test is the PICTURE, not some property of it: `elements()`
// is the last point at which the drawing is data, so that is what is recorded.
// A diff here means a diagram changed and wants looking at -- it does not mean
// anything is wrong. You decide, then accept it.
//
//   scripts/snapshot.sh                 compare, report
//   scripts/snapshot.sh --check         fail ONLY on approved diagrams
//                                              that changed -- usable as a gate
//                                              while the baseline is incomplete
//   scripts/snapshot.sh --accept        accept everything that differs
//   scripts/snapshot.sh --accept a b    accept only these
//
// `scripts/review.sh` accepts from the viewer instead, against the
// picture rather than the text. Both go through `accept` below.
//
// `lower.js` and `graph.js` are run verbatim, exactly as the browser runs them.

import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { pathToFileURL } from "node:url";
import { viewerDir as dir, claimsDir as claimDir, acceptedDir, currentDir, shortName } from "./data.mjs";

/** Stable display name for a node: its own text, never its generated id. */
function keys(els) {
  const of = d => d.kind === "group" ? "(box)"
    : d.kind === "end" ? "(end of trace)"
    : d.kind === "start" ? "(start of trace)"
    : d.kind === "again" ? "(begins again)"
    : d.kind === "join" ? "(empty event)"
    : (d.mark || "") + (d.knows === "yes" ? "\u21af " : "") +
      (d.name || `(${d.kind})`) +
      (d.kind === "loop" ? "  \u21ba" : "");
  const seen = new Map(), out = {};
  for (const e of els) {
    if (e.data.source) continue;
    const base = of(e.data);
    const n = (seen.get(base) || 0) + 1;
    seen.set(base, n);
    out[e.data.id] = n > 1 ? `${base} #${n}` : base;
  }
  return out;
}

function render(els) {
  if (!els.length) return "  (nothing drawn)\n";
  const k = keys(els);
  const kids = {};
  for (const e of els) if (!e.data.source) (kids[e.data.parent || ""] ||= []).push(e);

  let out = "";
  const walk = (parent, indent) => {
    for (const e of kids[parent] || []) {
      const d = e.data;
      out += `${indent}${k[d.id]}`;
      if (d.neg === "yes") out += "   [forbidden]";
      if (d.hidden) out += `   +${d.hidden} folded`;
      out += "\n";
      for (const c of d.checks || []) {
        if (!c.alt) { out += `${indent}  \u2022 ${c.p}\n`; continue; }
        c.alt.forEach((g, i) => {
          out += `${indent}  [${i ? "or" : "either"}]\n`;
          for (const x of g) out += `${indent}    \u2022 ${x.p}\n`;
        });
      }
      walk(d.id, indent + "  ");
    }
  };
  walk("", "  ");

  const edges = els.filter(e => e.data.source);
  if (edges.length) {
    out += "  --\n";
    for (const e of edges) {
      const d = e.data;
      out += `  ${k[d.source]} -> ${k[d.target]}`;
      if (d.never) out += `   ${d.never}`;
      // Two separate facts, both gated. `walk ⟦n⟧` names WHICH walk this step
      // is on, by the absence that declares it -- it is not a ban on this step,
      // which is what the bare number before it means. And the hue is not that
      // name either: absences that never meet share a colour, so two walks can
      // be drawn alike. Left out, parallel copies of one step recorded as
      // identical lines, and a recolouring did not register as a change at all.
      if (d.walk) out += `   walk ${d.walk} ${d.hue}`;
      if (d.weak === "yes") out += "   (weak)";
      out += "\n";
    }
  }
  return out;
}

/** Faults visible only once the drawing is laid out live in `graph.js`, beside
    the notation they are about, so the viewer banners the same ones. */

export function computeSnapshots() {
  const ctx = vm.createContext({ console, performance });
  for (const f of ["lower.js", "graph.js", "read.js"])
    vm.runInContext(fs.readFileSync(path.join(dir, f), "utf8"), ctx, { filename: f });
  const run = expr => vm.runInContext(expr, ctx);

  // Every claim file the build produced. Each campaign writes its own; the
  // reference theorems land in `reference.json`.
  const claimFiles = (fs.existsSync(claimDir) ? fs.readdirSync(claimDir) : [])
    .filter(f => f.endsWith(".json")).sort().map(f => path.join(claimDir, f));
  if (!claimFiles.length) throw new Error("no claim files -- run `lake build` first, or set DYVIS_DATA");

  const out = {};
  for (const file of claimFiles) {
    const entries = JSON.parse(fs.readFileSync(file, "utf8"));
    const claimOf = Object.fromEntries(entries.map(e => [shortName(e.name), e.claim]));
    const emittersOf = Object.fromEntries(
      entries.map(e => [shortName(e.name), e.emitters || {}]));
    run(`GRAPHS = lowerAll(${JSON.stringify(entries)})`);
    for (const name of run("Object.keys(GRAPHS)")) {
      run(`G = GRAPHS[${JSON.stringify(name)}]; expanded.clear();`);
      const foldedEls = run("elements()");
      const folded = render(foldedEls);
      // Only the unfolded view is asked to account for every absence: folding
      // hides shapes on purpose, and the `+N` says so.
      const foldedFaults = run("auditElements(elements(), [])");
      run("for (const id of Object.keys(G.nodes)) if (revealed(id).length) expanded.add(id);");
      const unfoldedEls = run("elements()");
      const unfolded = render(unfoldedEls);
      const status = run("G.failed ? 'failed: ' + G.failed : G.unsupported ? 'unsupported' : 'ok'");
      const faults = [...run("(G.mismatch || [])"),
                      ...foldedFaults,
                      ...run("auditElements(elements())")];
      // Does the picture READ BACK as its claim? Recorded rather than enforced:
      // where it does not yet, that is the state to see change.
      run(`__claim = ${JSON.stringify(claimOf[name] ?? null)}`);
      const reads = run(`(function () {
        if (!__claim || G.failed) return "not drawn";
        try {
          return canon(readGraph(elements())) === claimCanon(__claim, pretty)
            ? "yes" : "no";
        } catch (e) { return "error: " + e.message; }
      })()`);
      // Which code the diagram will send a reader to. Declaration names only:
      // a line number here would churn every baseline on an unrelated edit,
      // and it is the NAMES that say whether the model still reaches the same
      // emitters -- a driver dropping out of the config shows up as a diff.
      const em = emittersOf[name] || {};
      const sites = Object.keys(em).sort().map(c =>
        `  ${c}\n${em[c].map(s => `    ${s.decl}  (${s.file})`).sort().join("\n")}`).join("\n");
      out[name] = `status: ${status}\nreads back as its claim: ${reads}` +
        (run("G.size > 400") ? `\nlarge: ${run("G.size")} claim nodes after distribution` : "") +
        (faults.length ? `\ndoes not match the theorem:\n  ${[...new Set(faults)].join("\n  ")}` : "") +
        (sites ? `\n\n[emitted by]\n${sites}` : "") +
        `\n\n[folded]\n${folded}\n[unfolded]\n${unfolded}`;
    }
  }
  return out;
}

export function readAccepted() {
  fs.mkdirSync(acceptedDir, { recursive: true });
  return Object.fromEntries(fs.readdirSync(acceptedDir)
    .filter(f => f.endsWith(".txt"))
    .map(f => [f.slice(0, -4), fs.readFileSync(path.join(acceptedDir, f), "utf8")]));
}

/** `same` | `changed` | `new` per diagram, plus any whose theorem has gone. */
export function review(current, accepted = readAccepted()) {
  const state = {};
  for (const n of Object.keys(current))
    state[n] = !(n in accepted) ? "new" : current[n] === accepted[n] ? "same" : "changed";
  return { state, gone: Object.keys(accepted).filter(n => !(n in current)) };
}

export function accept(name, current) {
  if (!(name in current)) throw new Error(`no such diagram: ${name}`);
  fs.mkdirSync(acceptedDir, { recursive: true });
  fs.writeFileSync(path.join(acceptedDir, `${name}.txt`), current[name]);
}

export function writeCurrent(current) {
  fs.rmSync(currentDir, { recursive: true, force: true });
  fs.mkdirSync(currentDir, { recursive: true });
  for (const [name, body] of Object.entries(current))
    fs.writeFileSync(path.join(currentDir, `${name}.txt`), body);
}

function main() {
  let current;
  try { current = computeSnapshots(); }
  catch (e) { console.error(e.message); process.exit(2); }
  writeCurrent(current);

  const { state, gone } = review(current);
  const of = s => Object.keys(state).filter(n => state[n] === s);
  const changed = of("changed"), added = of("new");

  const args = process.argv.slice(2);
  const only = args.filter(a => !a.startsWith("--"));
  if (args.includes("--accept")) {
    const take = only.length ? only : [...changed, ...added];
    for (const n of take) {
      try { accept(n, current); } catch (e) { console.error(e.message); process.exit(2); }
      console.log(`accepted  ${n}`);
    }
    if (!only.length)
      for (const n of gone) {
        fs.rmSync(path.join(acceptedDir, `${n}.txt`));
        console.log(`removed   ${n}`);
      }
    if (!take.length && !gone.length) console.log("nothing to accept");
    return;
  }

  const list = xs => xs.length ? "  " + xs.join("\n  ") : "";
  console.log(`  same     ${of("same").length}`);
  console.log(`  CHANGED  ${changed.length}\n${list(changed)}`);
  console.log(`  NEW      ${added.length}\n${list(added)}`);
  console.log(`  GONE     ${gone.length}\n${list(gone)}`);

  // A diagram nobody has approved yet cannot regress, so `--check` ignores it.
  // That keeps the gate meaningful before the baseline is complete.
  if (args.includes("--check")) {
    if (changed.length || gone.length) {
      console.log("\nAPPROVED DIAGRAMS CHANGED -- look before accepting.");
      process.exit(1);
    }
    console.log("\nno approved diagram changed.");
    return;
  }

  if (changed.length || added.length || gone.length) {
    console.log(`\nnew output in ${path.relative(process.cwd(), currentDir)}/`);
    console.log("review the pictures and accept as you go:  scripts/review.sh");
    process.exit(1);
  }
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) main();
