// Reading a diagram BACK into a claim, by the rule a person is told to use.
//
// This is the check that matters. The audit in `lower.js` shows nothing went
// missing and nothing appeared from nowhere, but a picture that loses nothing
// can still be read wrongly -- three arrows meaning "one required, two
// alternatives" pass it happily. Reading the drawing back and comparing says
// the picture MEANS the claim.
//
// It is only worth anything if written from the notation rather than from
// `lower.js`. Mirroring the lowering would share every misconception and the
// round trip would succeed on a picture that misleads every reader. So the rule
// is restated here, and nothing else:
//
//   an arrow means the source happened earlier than the target
//   several arrows into one node are ALTERNATIVES
//   a box means all of its contents -- but a content an arrow LEAVES is a step
//     on the way somewhere, so it is read where the arrow lands and not again
//     on its own. Otherwise a fan-in inside a box reads as a conjunction of the
//     very alternatives it offers
//   a named box is a grouping and nothing more. Unfolded -- which is the view a
//     reader works in -- rubbing it out changes no meaning; the names are the
//     Lean subexpression names, kept for legibility
//   `∄ n` on an edge means shape n does not occur in that stretch
//   conditions on a node constrain that event; a divided cell is a choice
//   the bar is the end of the run; the branches reaching it are the
//     alternatives the theorem allows
//
// and, for the colours, which is what makes the local reading of `∄ n` sound --
// the claim behind it is about the WHOLE run, and the walk is what confines it
// to a stretch:
//
//   a colour is a WALK. Picking a run means picking an arrow into the bar: a
//     source AND a colour
//   a coloured walk keeps its colour: only arrows of that colour continue it
//   a grey arrow is under no rule. It may stay grey, or adopt a colour -- but
//     only one that STARTS there. A colour offered on the arrow already taken
//     was declined, and cannot be joined further in
//   so with `bar <- A` offering red and grey, and `A <- X` offering red, grey
//     and blue: red/red, grey/grey and grey/blue are runs; red/blue, red/grey
//     and grey/red are not
//   the NUMBERS on an edge say what is forbidden on THAT step; the COLOUR says
//     which walk you are on. A walk is a path identity and nothing else -- it
//     is not an absence. The two coincide here only because a whole-path `∄` is
//     so far the only thing that DECLARES a walk, which is also why walks are
//     named after one

function readGraph(els) {
  const node = {}, into = {};
  for (const e of els)
    if (!e.data.source) node[e.data.id] = e.data;
    else if (e.data.loop !== "yes") (into[e.data.target] ||= []).push(e.data);

  const kids = {};
  for (const e of els)
    if (!e.data.source && e.data.parent) (kids[e.data.parent] ||= []).push(e.data.id);

  const forbidden = {};
  for (const id of Object.keys(node))
    if ((node[id].tag || "").trim()) forbidden[node[id].tag.trim()] = id;

  // Nodes an arrow leaves. Reading one of these as a content of its box as well
  // would require it alongside the alternatives it competes with.
  // A loop arrow is not a departure: it is not a step, so the node it
  // leaves is still read where it stands.
  const departs = new Set(els.filter(e => e.data.source && e.data.loop !== "yes")
                             .map(e => e.data.source));

  const and = xs => xs.length === 0 ? null
    : xs.length === 1 ? xs[0] : { kind: "and", parts: xs };
  const or = xs => xs.length === 1 ? xs[0] : { kind: "or", parts: xs };

  // The conditions written on a node. A divided cell is a choice between them.
  // `? ` marks a hole the extractor could not classify; the text after it is
  // still the theorem's.
  const cond = x => ({ kind: "check", p: x.p.replace(/^\? /, "") });
  const conds = d => (d.checks || []).map(c => c.alt
    ? or(c.alt.map(g => and(g.map(cond))))
    : cond(c));

  // Which WALK an arrow belongs to, or `null` for a grey one under no rule.
  const walkOf = e => e.walk || null;
  // Every walk offered on one step, so that "a colour that starts here" can be
  // told from one that was offered a step earlier and declined.
  const offeredOn = (s, t) =>
    new Set((into[t] || []).filter(e => e.source === s).map(walkOf));

  // What one node says: itself, what it contains, what its conditions say, and
  // whatever reaches it -- alternatives if there is more than one.
  //
  // `walk` is the colour being followed, `offered` what the step already taken
  // put on the table. A coloured walk continues only on its own colour; a grey
  // one may stay grey or take up a colour that STARTS here. Without this a
  // reader is free to pair any arrival with any departure, and can walk out of
  // a run that forbids `sent` into one where `sent` happened.
  const read = (id, seen, walk, offered, inShape) => {
    if (seen.has(id)) return null;
    seen = new Set([...seen, id]);
    const d = node[id], parts = [];
    if (d.kind === "event") parts.push({ kind: "occurs", ev: d.name });
    if (d.kind === "loop") parts.push({ kind: "check", p: d.name });
    parts.push(...conds(d));
    parts.push(...(kids[id] || []).filter(k => !departs.has(k))
                 .map(k => read(k, seen, walk, offered, inShape)).filter(Boolean));
    const from = (into[id] || []).filter(e => {
      if (!node[e.source]) return false;
      const c = walkOf(e);
      if (walk !== null) return c === walk;
      return c === null || !offered.has(c);
    });
    const reached = from.map(e => {
      const b = read(e.source, seen, walkOf(e), offeredOn(e.source, id), inShape);
      const marks = (e.never || "").match(/\u27E6\d+\u27E7/g) || [];
      const shape = m => read(forbidden[m], seen, null, new Set(), true);
      // A forbidden shape is a sub-graph, not a run: its arrows are not steps a
      // reader takes, and a number on one of them is not scoped against
      // anything. So the accounting below is only done on the page proper.
      if (inShape)
        return and([b, ...marks.map(m => ({ kind: "not", c: shape(m) }))].filter(Boolean));
      // A number bans ITS OWN STEP -- that is the whole of what the notation
      // says it does. A `∄` over the run is that number on EVERY step of the
      // walk, which is a fact about the run and so cannot be decided here: a
      // run is a disjunct, and only `dnf` has those. The step and the bans on
      // it are recorded as atoms and resolved by `scopeRun`.
      const step = `${e.source}->${e.target}`;
      return and([b, { kind: "atom", s: `@step:${step}` },
                  ...marks.map(m => ({ kind: "atom", s: `@ban:${step}:${shapeText(shape(m))}` }))]
                 .filter(Boolean));
    }).filter(Boolean);
    if (reached.length) parts.push(or(reached));
    return and(parts.filter(Boolean));
  };

  // The bar is where every allowed run ends, so its incoming edges are the
  // alternatives the theorem permits: nothing has been declined yet, so every
  // colour offered there starts there.
  const root = Object.keys(node).find(id => node[id].kind === "end");
  if (!root) return null;
  return read(root, new Set(), null, new Set(), false);
}

// Comparison is up to what the picture cannot carry, and up to what carries no
// meaning: identifiers are shortened for display, index names are not drawn,
// and a NAME is transparent -- `denote (named n c)` is `denote c`, and once
// unfolded the name is not even on the path a reader follows.
//
// Both sides are put in DISJUNCTIVE NORMAL FORM, which absorbs three differences
// that are not disagreements. `∧`/`∨` are commutative and associative. An
// unbounded `∄` is repeated on every edge it governs -- that repetition is what
// makes a box readable on its own -- and `∧` is idempotent, so the copies
// collapse. And the picture is already distributed where the claim is not,
// since a branch of the drawing is one complete run.
//
// That idempotent collapse used to happen BEFORE anyone asked how many edges
// the mark was on, so a `∄` carried to the bar and one that stopped at a merge
// produced the same atom. `scopeRun` is what asks, and it has to run per
// disjunct, which is why the steps and bans travel this far as raw atoms.
function dnf(c) {
  if (!c) return [[]];
  if (c.kind === "named") return dnf(c.c);
  if (c.kind === "atom") return [[c.s]];
  if (c.kind === "or") return c.parts.flatMap(dnf);
  if (c.kind === "and")
    return c.parts.reduce((acc, p) => {
      const d = dnf(p);
      return acc.flatMap(a => d.map(b => [...a, ...b]));
    }, [[]]);
  if (c.kind === "not") return [[`not(${shapeText(c.c)})`]];
  // An absence the claim states between two points, and the picture draws on
  // the one arrow spanning them. NOT the same atom as a whole-run `∄`: that is
  // the distinction this whole pass exists to keep.
  if (c.kind === "notOn") return [[`notOn(${shapeText(c.c)})`]];
  if (c.kind === "check") return [[`check(${c.p})`]];
  return [[`occurs(${c.ev})`]];
}

// The same idempotence `canon` applies to a run, applied INSIDE a forbidden
// shape. A whole `¬` is one atom, so duplication within it is invisible to the
// run-level dedupe -- and `distribute` duplicates whatever the branches share,
// so the picture's shape carried four copies of a block the claim states once.
function shapeText(c) {
  return [...new Set(dnf(c).map(a => [...new Set(a)].sort().join("&")))]
    .sort().join("|");
}

// One run's atoms, with its numbers resolved against the steps it actually
// took. THE RULE THE PAGE STATES: a number bans its own step and nothing else,
// and a `∄` over the whole run is that number on EVERY step of the walk. A mark
// on some of them is a bounded absence and reads as one -- which is how a
// whole-run `∄` that stopped at a merge is told from one that reached the bar.
function scopeRun(atoms) {
  const steps = new Set(), banned = new Map(), rest = [];
  for (const a of atoms) {
    if (a.startsWith("@step:")) { steps.add(a.slice(6)); continue; }
    if (a.startsWith("@ban:")) {
      const i = a.indexOf(":", 5);
      const shape = a.slice(i + 1);
      if (!banned.has(shape)) banned.set(shape, new Set());
      banned.get(shape).add(a.slice(5, i));
      continue;
    }
    rest.push(a);
  }
  for (const [shape, on] of banned)
    rest.push([...steps].every(s => on.has(s)) ? `not(${shape})` : `notOn(${shape})`);
  return rest;
}

function canon(c) {
  // Idempotence on both connectives: an atom twice in a run says no more than
  // once, and a run offered twice is one alternative. The picture draws each
  // once, and two disjuncts that differ only inside a name collapse here.
  //
  // Deliberately NOT absorption. `a ∨ (a ∧ b)` is `a`, so absorbing would be
  // sound -- and it would also make the comparison blind to the colours, since a
  // page with none of them reads as runs that are strictly stronger than the
  // real ones and would be absorbed away. The picture has to earn equality on
  // the nose.
  return [...new Set(dnf(c).map(a => [...new Set(scopeRun(a))].sort().join(" & ")))]
    .sort().join("  |  ");
}

// The same reading, taken from the claim rather than from the picture.
const unimpOf = c => c.kind === "imp"
  ? { kind: "and", a: c.a, b: unimpOf(c.b) }
  : { kind: "not", c };

// `∀x⃗, a x⃗ → c` with `c` free of `x⃗`, exactly as `lower.js` reads it.
// `denote_all_imp_const` in `Claim.lean`; `closed` is decided in `Extract.lean`.
function unforallOf(c) {
  if (!c || c.kind !== "all" || !c.closed) return null;
  let x = c;
  while (x && x.kind === "all") x = x.c;
  if (!x || x.kind !== "imp") return null;
  const ants = [];
  while (x.kind === "imp") { ants.push(x.a); x = x.b; }
  return { kind: "or", a: { kind: "not", c: ants.reduce((a, b) => ({ kind: "and", a, b })) },
           b: x };
}

// What a node forbids, or null if the notation does not read it as an absence.
// A `∀` only BECOMES one under the rewrites below, so an outer `¬` has to ask
// here rather than look at its raw child: otherwise the two never meet and the
// `¬¬` the picture cancels survives in the reading as an atom of its own. Seen
// through a name, since `denote (named n c)` is `denote c`.
function forbiddenBy(c) {
  if (!c) return null;
  if (c.kind === "not") return c.c || null;
  if (c.kind === "named") {
    const i = forbiddenBy(c.c);
    return i ? { ...c, c: i } : null;
  }
  if (c.kind !== "all" || !c.c || unforallOf(c)) return null;
  if (c.c.kind === "imp") return unimpOf(c.c);
  // A `∀` of an absence is that absence one witness wider, so a statement's
  // binders collapse from the inside out.
  if (c.c.kind === "all" || c.c.kind === "not") return forbiddenBy(c.c);
  return null;
}

function claimCanon(c, pretty) {
  const go = n => {
    const flat = unforallOf(n);
    if (flat) return go(flat);
    switch (n.kind) {
      case "and": case "or":
        return { kind: n.kind, parts: [go(n.a), go(n.b)].filter(Boolean) };
      case "not": {
        // `¬¬` is nothing; the picture drops it, so the reading must too.
        const i = forbiddenBy(n.c);
        return i ? go(i) : { kind: "not", c: go(n.c) };
      }
      case "named": return { kind: "named", n: pretty(n.n), c: go(n.c) };
      case "ex": return go(n.c);
      // The same two rewrites the picture is drawn through, so the comparison is
      // between the claim and the drawing rather than between two spellings of
      // the claim. Both are proved in `Claim.lean`.
      case "all": return n.c && n.c.kind === "imp"
        ? { kind: "not", c: go(unimpOf(n.c)) }
        : n.c && n.c.kind === "not" ? { kind: "not", c: go(n.c.c) } : go(n.c);
      case "imp": return { kind: "or", parts: [{ kind: "not", c: go(n.a) },
                                               { kind: "and", parts: [go(n.a), go(n.b)] }] };
      case "check": case "opaque": return { kind: "check", p: pretty(n.p) };
      // A turn of a recursive predicate is recovered as an ATOM naming the
      // predicate at this turn's arguments -- the same treatment `opaque`
      // gets. What the drawing added is the turn itself, not a reading of the
      // repetition, and the check must not claim otherwise.
      case "again": return { kind: "check", p: pretty(n.n) };
      // Must match the box text `lower.js` writes, or the reading of a picture
      // that is right disagrees with the claim it came from.
      case "knows": return { kind: "occurs", ev: `AttackerKnows ${pretty(n.ev)}` };
      // Stated between two positions, so it bans the stretch between them and
      // not the run -- `notOn`, which is a different atom from a whole-run `∄`.
      case "absentBetween":
        return { kind: "notOn", c: { kind: "occurs", ev: pretty(n.ev) } };
      default: return { kind: "occurs", ev: pretty(n.ev) };
    }
  };
  // `asNamed` from `lower.js`: an inductive predicate is a name here too.
  return canon(go(asNamed(c)));
}
