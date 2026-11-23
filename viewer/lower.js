// Claim tree -> diagram graph.
//
// This is the UNTRUSTED half of the pipeline: the Lean side certifies that a
// theorem's conclusion IS its claim tree, and everything here is presentation.
// So the rule is that each step below is mechanical and local -- no step may
// decide that two different claims deserve the same picture.
//
// Lowering returns a FRAGMENT rather than a node, because three things travel
// upwards until something can host them:
//   entries -- the nodes an incoming arrow should point at (several = a choice)
//   checks  -- conditions, which ride on the event that binds their witness
//   nevers  -- forbidden shapes, which belong on an edge and not on a node
//
// The one piece of real analysis is happens-before. An `occursAt ev i` BINDS the
// index `i`; a sibling whose region is `before i` is therefore constrained to
// the stretch under that event, and becomes its child rather than its sibling.
// That is what turns a conjunction into a chain, and it is read off the indices
// rather than guessed from the order the conjuncts were written in.

// `accepted` alone does not say which event it is, so the type name stays. The
// module path does not: only the head identifier is trimmed, never arguments.
const pretty = s => (s || "").replace(/^[A-Za-z_][A-Za-z0-9_.']*/, m => {
  const p = m.split(".");
  return p.length > 2 ? p.slice(-2).join(".") : m;
});

// Identifiers a label or condition mentions, used to find which event binds a
// witness. Deliberately crude: it only ever decides WHERE a check is drawn.
// Only locals are collected -- constructor and namespace names are capitalised
// and would match across unrelated events. A field projection still names its
// witness, so `rrset.rdata` yields `rrset` too.
const idents = s => {
  const out = new Set();
  for (const m of (s || "").match(/[A-Za-z_][A-Za-z0-9_.']*/g) || []) {
    const head = m.split(".")[0];
    if (/^[a-z_]/.test(head)) out.add(head);
    if (/^[a-z_]/.test(m)) out.add(m);
  }
  return out;
};

// What a leaf's box says. Attacker knowledge names its predicate: the byte
// string alone reads as an event about `payload` rather than a fact about who
// holds it.
const evText = c =>
  c.kind === "knows" ? `AttackerKnows ${pretty(c.ev)}` : pretty(c.ev);

// Does a claim say anything about the trace itself?
const claimHasEvent = c =>
  ["occurs", "occursAt", "stored", "storedAt", "absentBetween", "opaque", "again",
   "knows"].includes(c.kind) ||
  ["a", "b", "c"].some(k => c[k] && c[k].kind && claimHasEvent(c[k]));

// An INDUCTIVE predicate arrives as `cases` rather than `named`. The two draw
// alike -- a dashed box is a name from the source either way -- and differ in
// what ties the box to its name: delta-reduction for `named`, and for this a
// theorem `Extract.lean` generated and the kernel checked. That is a fact about
// the claim, carried by its `tie` field and reported at the trace site; the
// picture has nothing to add to it, so the kinds are levelled here and once.
const asNamed = c => {
  if (!c || !c.kind) return c;
  const out = c.kind === "cases" ? { ...c, kind: "named" } : { ...c };
  for (const k of ["a", "b", "c"]) if (c[k] && c[k].kind) out[k] = asNamed(c[k]);
  return out;
};

// `¬(a → b → c)` is `a ∧ b ∧ ¬c`: what a run would have to look like to break
// the obligation. `denote_not_imp` in `Claim.lean`.
const unimp = c => c.kind === "imp"
  ? { kind: "and", a: c.a, b: unimp(c.b) }
  : { kind: "not", c };

// `∀x⃗, a x⃗ → c` whose conclusion does not mention `x⃗` is "nothing satisfies
// `a`, or `c`" -- a choice between two shapes the notation already has, rather
// than an absence with another absence inside it. Which is what it becomes
// otherwise: `denote_all_imp` gives `∄x⃗, a ∧ ¬c`, and a conclusion that is
// itself an `∃` -- a registration, a key lookup -- puts a second `¬` in there.
// `denote_all_imp_const` in `Claim.lean`. The side condition is decided in
// `Extract.lean`, where the binders are variables rather than printed names.
function unforall(c) {
  if (!c || c.kind !== "all" || !c.closed) return null;
  const binders = [];
  let x = c;
  while (x && x.kind === "all") { binders.push(x.binder); x = x.c; }
  if (!x || x.kind !== "imp") return null;
  const ants = [];
  while (x.kind === "imp") { ants.push(x.a); x = x.b; }
  const conj = ants.reduce((a, b) => ({ kind: "and", a, b }));
  const ex = binders.reduceRight((inner, binder) => ({ kind: "ex", binder, c: inner }), conj);
  return { kind: "or", a: { kind: "not", c: ex }, b: x };
}

// `∀x, a → b` is "there is no `x` with `a` and not `b`", and a forbidden shape
// is what the notation already has for that -- so an obligation over every
// publication is drawn in the same vocabulary as everything else, rather than
// as a hole. `denote_all_imp` in `Claim.lean`, with `denote_all_not` to collapse
// the binders outside it: a statement quantifies one at a time, so once the
// innermost is a `∄` the rest are each a `∀` of a negation, which is the same
// `∄` one witness wider. A `∀` of anything else has no reading here and is left
// for the audit to refuse.
function deforall(c) {
  if (!c || !c.kind) return c;
  const flat = unforall(c);
  if (flat) return deforall(flat);
  const out = {};
  for (const k of Object.keys(c))
    out[k] = ["a", "b", "c"].includes(k) ? deforall(c[k]) : c[k];
  if (out.kind !== "all" || !out.c) return unnot(out);
  if (out.c.kind === "imp")
    return unnot({ kind: "not", c: { kind: "ex", binder: out.binder, c: unimp(out.c) } });
  if (out.c.kind === "not")
    return unnot({ kind: "not", c: { kind: "ex", binder: out.binder, c: out.c.c } });
  return out;
}

// `¬¬` is nothing. A theorem's premise is drawn negated in the branch where it
// fails, so a premise that is ITSELF an absence arrives doubly negated -- and
// drawn literally that is a forbidden shape whose body is another one, which
// has nothing to show. `denote_not_not` in `Claim.lean`, transparent through a
// name because `denote (named n c)` is `denote c`.
function unnot(c) {
  if (!c || c.kind !== "not" || !c.c) return c;
  const inner = c.c;
  if (inner.kind === "not") return inner.c;
  if (inner.kind === "named" && inner.c && inner.c.kind === "not")
    return { ...inner, c: inner.c.c };
  return c;
}

function distribute(c) {
  // A choice between CONDITIONS is drawn as a divided cell on the event they
  // qualify, so multiplying it out buys nothing and costs a copy of everything
  // around it. Only a choice between runs needs branches of its own.
  const splits = x => x.kind === "or" && claimHasEvent(x);
  switch (c.kind) {
    case "or": return splits(c) ? { kind: "or", a: distribute(c.a), b: distribute(c.b) } : c;
    case "and": {
      const a = distribute(c.a), b = distribute(c.b);
      if (splits(a))
        return distribute({ kind: "or", a: { kind: "and", a: a.a, b },
                                        b: { kind: "and", a: a.b, b } });
      if (splits(b))
        return distribute({ kind: "or", a: { kind: "and", a, b: b.a },
                                        b: { kind: "and", a, b: b.b } });
      return { kind: "and", a, b };
    }
    // A witness is not a step, so a choice under one cannot be drawn where it
    // stands: one copy of the witness per alternative instead. Sound because
    // `∃ x, (A ∨ B)` is `(∃ x, A) ∨ (∃ x, B)`. Without it an `∨` under a
    // witness never reaches an `∧` to distribute against, and DANE buries its
    // choices under seven of them.
    case "ex": {
      const inner = distribute(c.c);
      if (splits(inner))
        return distribute({ kind: "or", a: { ...c, c: inner.a }, b: { ...c, c: inner.b } });
      return { ...c, c: inner };
    }
    // A NAME keeps its choice. Splitting one is sound as a proposition --
    // `denote (named n c)` is `denote c` -- but each copy goes on wearing the
    // name while holding a fraction of what the name means, and two boxes then
    // read as the same Lean expression while saying different things. The
    // reason to split, that an alternative inside a box reads as a requirement,
    // is a reason about the SOLID box: a name draws a bar for its alternatives
    // to converge on, which says "this is needed, and for it you may take any
    // one of these back".
    case "named": return { ...c, c: distribute(c.c) };
    default: return c;
  }
}

const claimSize = c =>
  1 + ["a", "b", "c"].reduce((n, k) => n + (c[k] && c[k].kind ? claimSize(c[k]) : 0), 0);

// Raised when alternatives end up as siblings of a conjunct, where a solid box
// would read them as requirements. The answer is to multiply the claim out, but
// that is worth avoiding while the alternatives can simply converge.
const AMBIGUOUS = Symbol("ambiguous");

function lowerTheorem(entry) {
  try {
    return build(entry, false);
  } catch (e) {
    if (e !== AMBIGUOUS) throw e;
    return build(entry, true);
  }
}

function build(entry, dnf) {
  let nodes = {};
  let n = 0;
  const created = [];
  const fresh = base => { const id = `${base}${n++}`; created.push(id); return id; };
  let unsupported = false;

  // Which node binds each index name, so `before i` can find its parent. The
  // theorem has ONE `i`, but distribution draws one copy of that event per
  // alternative, so this must be read within a branch and not across branches.
  const binder = {};
  // Witnesses currently in scope: a check may only ride on an event that binds
  // one of these, otherwise every check would stick to the nearest event.
  const bound = new Set();

  // One box per named absence, however many alternatives cite it. Distribution
  // copies a shared premise into every disjunct, and drawing six identical
  // forbidden shapes says there are six rules where there is one.
  const sharedAbsence = {};

  // The end of the trace. Everything drawn happens before it, so it is the
  // anchor rather than any particular event -- which is what lets a branch in
  // which NOTHING happens still be a path on the page.
  const bar = fresh("end");
  nodes[bar] = { kind: "end", label: "", deps: [] };

  const frag = (entries = [], checks = [], nevers = []) => ({ entries, checks, nevers });

  // Nodes that stand for a CHOICE. Converging arrows mean alternatives, so
  // whether several things may point at one event depends on this.
  const alternatives = new Set();

  // Happens-before among siblings: whoever is confined to `before i` goes under
  // whoever binds `i`.
  function chain(entries, box) {
    const out = [], byParent = new Map();
    for (const id of entries) {
      const r = nodes[id].region;
      const parent = r && r.kind === "before" ? binder[r.i] : null;
      if (parent && parent !== id && entries.includes(parent)) {
        if (!byParent.has(parent)) byParent.set(parent, []);
        byParent.get(parent).push(id);
      } else out.push(id);
    }
    for (const [parent, kids] of byParent) {
      const conj = kids.filter(k => !alternatives.has(k));
      const alts = kids.filter(k => alternatives.has(k));
      // A requirement and a choice arriving at the same event cannot be told
      // apart -- every arrow looks alike, and boxing the requirements does not
      // help, since the box is then just one more arrow among the choices. The
      // claim is multiplied out instead, as it already is for two triggers.
      if (conj.length && alts.length) {
        if (!dnf) throw AMBIGUOUS;
        unsupported = true;
      }
      // Several REQUIREMENTS converging on one event would read as a choice,
      // so they are boxed together and the box is what points at the event.
      if (conj.length > 1) {
        const g = fresh("group");
        nodes[g] = { kind: "group", deps: conj, owner: box };
        for (const k of conj) nodes[k].owner = g;
        nodes[g].region = commonRegion(conj);
        nodes[parent].deps.push(g, ...alts);
        for (const k of alts) nodes[k].owner = box;
      } else {
        nodes[parent].deps.push(...kids);
        for (const k of kids) nodes[k].owner = box;
      }
    }
    return out;
  }

  // A check rides on the event that binds its witness -- but only if exactly
  // one candidate does. Two candidates and it is genuinely about the pair, so
  // it gets a box of its own rather than being arbitrarily attached to one.
  //
  // Matched on the statement's own variables, which the extractor records, not
  // on a scan of the printed text: that mistook `rrset.rdata` for something
  // other than `rrset`, and `= true` for a name.
  function placeChecks(f, box) {
    const hostOf = c => {
      const cs = new Set(c.vars);
      const hostsBy = pred => f.entries.filter(id => {
        const ls = new Set(nodes[id].vars || []);
        return [...cs].some(t => ls.has(t) && pred(t));
      });
      // A witness the statement introduced is the sharper clue, so a check is
      // matched on parameters only when no witness of its own is in play.
      // Without the fallback a condition on the trigger's own arguments -- all
      // of DANE's R2 -- floats free of the event it is about.
      let hosts = hostsBy(t => bound.has(t));
      if (!hosts.length) hosts = hostsBy(t => !bound.has(t));
      // Several candidates: most shared names wins, and on a tie the event the
      // statement is triggered by. An alternative SET spans its compartments'
      // names, so it almost always touches more than one event.
      if (hosts.length > 1) {
        const score = id => {
          const ls = new Set(nodes[id].vars || []);
          const shared = [...cs].filter(t => ls.has(t)).length;
          return 2 * shared + (nodes[id].binds ? 1 : 0);
        };
        const best = Math.max(...hosts.map(score));
        const top = hosts.filter(id => score(id) === best);
        hosts = top.length === 1 ? top : hosts;
      }
      return hosts.length === 1 ? hosts[0] : null;
    };

    // A placed check NAMES its host's witnesses, so the leftovers are retried
    // against what it introduced. Some witnesses reach the run only through a
    // condition -- `dnskey'` is named by `contains (serialize dnskey') …`, never
    // by `rrsetSigned signer' rrsig' rrset'` itself -- and a check about one of
    // those has nothing to match until that condition has been placed. One pass
    // cannot do it: the two arrive in the wrong order.
    let left = f.checks, moved = true;
    while (moved && left.length) {
      const again = [];
      for (const c of left) {
        const host = hostOf(c);
        if (host === null) { again.push(c); continue; }
        nodes[host].checks = [...(nodes[host].checks || []), c];
        nodes[host].vars = [...new Set([...(nodes[host].vars || []), ...(c.vars || [])])];
      }
      moved = again.length < left.length;
      left = again;
    }
    if (left.length) {
      const id = fresh("chk");
      nodes[id] = { kind: "checks", checks: left, deps: [], owner: box };
      f.entries.push(id);
    }
    f.checks = [];
  }

  // A collapsed box hands its contents to whoever held the box.
  function reown(box, owner) {
    for (const x of Object.values(nodes)) if (x.owner === box) x.owner = owner;
  }

  // `A ∧ B ∧ C` parses as `A ∧ (B ∧ C)`, but that nesting is punctuation, not
  // structure: the reader is owed one box with three things in it.
  function flatten(c, kind) {
    return c.kind === kind ? [...flatten(c.a, kind), ...flatten(c.b, kind)] : [c];
  }

  // Absence marks travel up until something can carry them. A mark that already
  // names the edge it sits on keeps travelling -- only an UNANCHORED one needs
  // a box of its own, because a `∄` has to sit on some edge.
  function seal(f, owner) {
    const floating = f.nevers.filter(nv => !nv.after);
    if (!floating.length) return f.entries;
    if (!f.entries.length) {
      const dot = fresh("start");
      // At the TOP level nothing happens in this branch at all: start of trace
      // straight to the end, so the marks name that one edge and are done.
      //
      // Inside a box the same branch is not the whole run -- it leaves the box
      // and the run carries on -- and the `∄` is over the whole trace, so a
      // reader entering here commits from the start to never introducing the
      // shape. That is a WALK, and anchoring it was what stopped it being one:
      // `neverMarks` skips an anchored mark outright, so it never travelled to
      // the bar and the steps after the merge went unbanned. Left floating and
      // hung on the dot, which has no deps, `contexts` reads it as the branch
      // that DECLARES the walk, and the shared arrows downstream are split per
      // walk -- the arrows, not the name, which stays whole.
      nodes[dot] = { kind: "start", label: "", deps: [], owner,
                     ...(owner ? { never: floating } : {}) };
      f.nevers = f.nevers.filter(nv => nv.after)
                         .concat(owner ? [] : floating.map(nv => ({ ...nv, after: dot })));
      return [dot];
    }
    const id = fresh("group");
    nodes[id] = { kind: "group", deps: f.entries, owner, never: floating };
    for (const e of f.entries) nodes[e].owner = id;
    f.nevers = f.nevers.filter(nv => nv.after);
    return [id];
  }

  // A container sits where its contents sit, but only if they agree. Mixing a
  // `before i` with something stated over the whole run would otherwise place
  // the whole box before an event that need not follow it.
  const commonRegion = ids => {
    const key = r => r && r.kind === "before" ? `b${r.i}` : "w";
    if (!ids.length) return undefined;
    const first = nodes[ids[0]].region;
    return ids.every(i => key(nodes[i].region) === key(first)) && key(first) !== "w"
      ? first : undefined;
  };

  // The conditions of one alternative, gathered without drawing anything. A
  // shape this cannot read is refused rather than flattened, since flattening
  // would silently merge two alternatives into one list of requirements.
  function cellOf(c, out) {
    switch (c.kind) {
      case "check": out.push({ p: pretty(c.p), vars: c.vars || [] }); break;
      case "and": cellOf(c.a, out); cellOf(c.b, out); break;
      // The witness is named by the conditions that mention it.
      case "ex": bound.add(c.binder); cellOf(c.c, out); break;
      case "named": cellOf(c.c, out); break;
      default: unsupported = true;
    }
    return out;
  }

  function lower(c, owner, neg) {
    switch (c.kind) {
      case "or": {
        const parts = flatten(c, "or");
        // A disjunction of pure CONDITIONS is not a choice of runs: it is one
        // event qualifying two ways. Drawn as alternative condition sets on
        // that event, so no branch is owed. Each alternative is kept whole --
        // flattened into one list, `rtype = DNSKEY` and `rtype = DS` would sit
        // side by side and read as a contradiction.
        if (parts.every(p => !claimHasEvent(p))) {
          const cells = parts.map(p => cellOf(p, []));
          const vars = [...new Set(cells.flat().flatMap(x => x.vars || []))];
          return frag([], [{ alt: cells, vars }]);
        }
        // Each alternative is sealed on its own: a `∄` in one branch says
        // nothing about the others. Marks that already name their edge keep
        // rising, since the edge they name is drawn further up.
        const entries = [], nevers = [];
        for (const part of parts) {
          // An index bound inside one alternative names that alternative's own
          // copy of the event, so resolve before the next branch rebinds it.
          const outer = { ...binder };
          const from = created.length;
          const f = lower(part, owner, neg);
          // A branch that is nothing but conditions still has to become a node:
          // dropping its checks here would silently delete a whole alternative
          // and leave a diagram that looks complete.
          placeChecks(f, owner);
          entries.push(...seal(f, owner));
          nevers.push(...f.nevers);
          resolveAbsence(created.slice(from));
          for (const k of Object.keys(binder)) delete binder[k];
          Object.assign(binder, outer);
        }
        for (const e of entries) alternatives.add(e);
        return frag(entries, [], nevers);
      }

      case "ex":
        // A witness is not a step; it is named by the events that mention it.
        bound.add(c.binder);
        return lower(c.c, owner, neg);

      case "named": {
        const shareKey = JSON.stringify(c);
        if (sharedAbsence[shareKey])
          return frag([], [], [{ def: sharedAbsence[shareKey] }]);
        const id = fresh("def");
        nodes[id] = { kind: "def", label: pretty(c.n), deps: [], owner,
                      pred: c.of || "" };
        const f = lower(c.c, id, neg);
        placeChecks(f, id);
        nodes[id].deps = chain(f.entries, id);
        for (const e of nodes[id].deps) nodes[e].owner = id;
        // Whether this name's contents are a CHOICE or a conjunction. Only the
        // lowering knows: the renderer sees a `def` with several deps and has
        // been guessing both ways -- `entriesOf` reads it as branching while
        // containment and `read.js` read it as "all of these".
        if (nodes[id].deps.length > 1 && nodes[id].deps.every(d => alternatives.has(d)))
          nodes[id].choice = true;
        // Several REQUIREMENTS inside one name. An unfolded name is dissolved,
        // so each would draw an arrow of its own -- and converging arrows mean
        // alternatives everywhere else on the page. They are boxed together
        // first, which is the same rule `chain` applies at an event, and the
        // box is then the one thing the arrow leaves. `chain` does not reach
        // this: a check with nowhere to ride becomes a leaf of the name AFTER
        // the entries have been chained.
        else if (nodes[id].deps.length > 1) {
          const g = fresh("group");
          nodes[g] = { kind: "group", deps: nodes[id].deps, owner: id,
                       region: commonRegion(nodes[id].deps) };
          for (const k of nodes[id].deps) nodes[k].owner = g;
          nodes[id].deps = [g];
        }
        nodes[id].region = commonRegion(nodes[id].deps);
        // A name whose whole meaning is an absence IS the forbidden shape --
        // otherwise the box comes out empty and the `∄` floats off onto
        // whatever edge the ban machinery happens to pick. A BOUNDED absence
        // already names the edge it rides, so it is left where it is.
        const free = nv => nv.lo === undefined && !nv.after;
        if (!nodes[id].deps.length && f.nevers.length && f.nevers.every(free)) {
          nodes[id].deps = f.nevers.map(nv => nv.def);
          for (const e of nodes[id].deps) nodes[e].owner = id;
          // A forbidden shape hangs off no branch, so it belongs to no box.
          delete nodes[id].owner;
          nodes[id].saysAbsence = true;
          sharedAbsence[shareKey] = id;
          return frag([], [], [{ def: id }]);
        }
        // Absence inside a named predicate is part of what the name means.
        if (f.nevers.length) nodes[id].never = f.nevers;
        return frag([id]);
      }

      case "and": {
        const id = fresh("group");
        const parts = flatten(c, "and").map(p => lower(p, id, neg));
        const f = frag(parts.flatMap(p => p.entries),
                       parts.flatMap(p => p.checks),
                       parts.flatMap(p => p.nevers));
        placeChecks(f, id);
        let entries = chain(f.entries, id);

        // Alternatives that did not converge are still siblings of the
        // conjuncts. They can only be read as alternatives if they all point at
        // one event; with two candidates there is no honest choice, so give up
        // here and let the caller multiply the claim out instead.
        const stray = entries.filter(e => alternatives.has(e));
        if (stray.length) {
          const anchors = entries.filter(e => !alternatives.has(e) && nodes[e].binds);
          if (anchors.length !== 1) throw AMBIGUOUS;
          const a = anchors[0];
          for (const s of stray) {
            const r = nodes[s].region;
            // Stated over the whole run, so it is not ordered against the
            // anchor -- but it is still one of the ways to reach it.
            if (r && r.kind === "whole") (nodes[a].also ||= []).push(s);
            else nodes[a].deps.push(s);
            nodes[s].owner = nodes[a].owner;
          }
          entries = entries.filter(e => !alternatives.has(e));
        }

        // A box holding one thing adds nothing the arrow does not already say;
        // any absence mark it was carrying goes further up instead.
        if (entries.length === 1) {
          reown(id, owner);
          nodes[entries[0]].owner = owner;
          return frag(entries, [], f.nevers);
        }
        // Nor a box over members that are differently PLACED. A box has one
        // outgoing arrow and can only claim what its weakest member claims, so
        // boxing a member the statement bounds together with one it does not
        // throws the bound away. Handed up unboxed, the enclosing level places
        // each on its own -- and re-boxes whatever still belongs together.
        //
        // A CHECKS node is not a member with a different bound: it is a value
        // condition, with no region because it has no position, so it has no
        // bound to throw away. Counting it here dissolved the box around a
        // conjunction whenever a check could not find a host, and the members
        // then reached the event as separate arrows -- which is the notation
        // for a choice, so the picture offered runs the theorem does not.
        const positional = entries.filter(e => nodes[e].kind !== "checks");
        const placed = positional.filter(e => (nodes[e].region || {}).kind === "before");
        if (placed.length && placed.length < positional.length) {
          reown(id, owner);
          for (const e of entries) nodes[e].owner = owner;
          return frag(entries, [], f.nevers);
        }
        nodes[id] = { kind: "group", deps: entries, owner };
        for (const e of entries) nodes[e].owner = id;
        nodes[id].region = commonRegion(entries);
        if (f.nevers.length) nodes[id].never = f.nevers;
        return frag([id]);
      }

      case "occurs":
      case "occursAt":
      case "stored":
      case "storedAt":
      case "knows": {
        const id = fresh("ev");
        const isState = c.kind === "stored" || c.kind === "storedAt";
        nodes[id] = { kind: "event", label: evText(c), deps: [], owner,
                      vars: c.vars || [], region: c.region, ctor: c.ctor };
        // A state ENTRY, not a logged event: the same kind of fact, but written
        // by `storeGlobalState` rather than by the protocol, and a reader
        // asking what emits it needs to know which.
        if (isState) nodes[id].stored = true;
        // Attacker knowledge is not emitted by ANYONE -- no action logs it, it
        // is closed under the deduction rules. It scopes and connects like an
        // event, which is why it is drawn as one, so the mark is what stops a
        // reader hunting for the action that produced it.
        if (c.kind === "knows") nodes[id].knows = true;
        if (c.region && c.region.weak) nodes[id].weak = true;
        // Binding an index makes this event something others can be placed
        // relative to, and so the only thing alternatives may converge on.
        if (c.kind === "occursAt" || c.kind === "storedAt") {
          binder[c.i] = id; nodes[id].binds = true;
        }
        return frag([id]);
      }

      case "check":
        return frag([], [{ p: pretty(c.p), vars: c.vars || [] }]);

      // One turn on of a recursive predicate. Which box it re-enters is
      // resolved when the graph is drawn: `owner` is still being assigned here,
      // so the chain is not walkable yet.
      case "again": {
        const id = fresh("loop");
        nodes[id] = { kind: "loop", label: pretty(c.n), deps: [], owner,
                      pred: c.of || "" };
        return frag([id]);
      }

      case "absentBetween": {
        // Absence belongs to a stretch, not to a point: the forbidden event is
        // drawn unconnected, and the mark goes on the edge bounding it.
        const id = fresh("never");
        nodes[id] = { kind: "event", label: pretty(c.ev), deps: [], ctor: c.ctor };
        return frag([], [], [{ def: id, lo: c.lo, hi: c.hi }]);
      }

      case "not": {
        // The negated shape is drawn, but never connected: nothing in it
        // happened. Whether that leaves an empty run is `seal`'s business.
        const f = lower(c.c, null, true);
        placeChecks(f, null);
        // An absence inside this one is part of what it forbids, the same way
        // one inside a name is part of what the name means. Dropped here, the
        // same predicate came out drawn or not according to whether a name or a
        // multi-member box happened to lie between the two.
        if (f.nevers.length && f.entries.length === 1) {
          const host = nodes[f.entries[0]];
          host.never = [...(host.never || []), ...f.nevers];
          f.nevers = [];
        }
        for (const id of f.entries) delete nodes[id].owner;
        // A shape with nothing in it asserts nothing, and reads as though the
        // absence were satisfied. A `¬` nested below this one is how that
        // happens: the inner one becomes a mark of its own and hands no entry
        // back, leaving the outer box empty. `denote_not_not` reaches the case
        // where the two are adjacent; anything deeper has no reading here and
        // must not be drawn as though it had.
        if (!f.entries.length ||
            f.entries.some(id => ["def", "group"].includes(nodes[id].kind) &&
                                 !nodes[id].deps.length))
          unsupported = true;
        return frag([], [], f.entries.map(id => ({ def: id })));
      }

      default: {
        unsupported = true;
        const id = fresh("hole");
        nodes[id] = { kind: "checks", checks: [{ p: `? ${pretty(c.p || c.kind)}`, vars: [] }],
                      deps: [], owner };
        return frag([id]);
      }
    }
  }

  // `Extract.lean` has already expanded implications, hoisted witnesses and
  // bounded whole-run claims by the trigger; only the fallback split is left.
  const claim = deforall(entry.claim);
  const normal = dnf ? distribute(claim) : claim;
  // Distribution can multiply out. That makes a diagram BIG, which a reader can
  // see for himself -- it does not make it incomplete or wrong, so it is
  // reported as a measurement rather than as a defect.
  const size = claimSize(normal);
  const top = lower(normal, null, false);
  placeChecks(top, null);

  // Everything hangs off the end of the trace, so there is no distinction left
  // between "before the trigger" and "somewhere in the run".
  nodes[bar].deps = chain(seal(top, null), null);
  if (top.nevers.length) nodes[bar].never = top.nevers;
  // Anything not inside an alternative, which `or` has already dealt with.
  resolveAbsence(created);
  // A box has ONE outgoing arrow, so it must claim only what its weakest member
  // does: any step-bounded member makes the whole box step-bounded.
  for (let again = true; again; ) {
    again = false;
    for (const node of Object.values(nodes))
      if (!node.weak && (node.kind === "group" || node.kind === "def") &&
          (node.deps || []).some(d => nodes[d] && nodes[d].weak)) {
        node.weak = true;
        again = true;
      }
  }

  // Resolve bounded absence onto the edge it constrains. `after` names the
  // lower end, so the mark lands on exactly one edge rather than spreading down
  // the whole path. Runs per alternative: `binder` must hold THAT branch's
  // events, or a mark lands on a copy belonging to a sibling.
  function resolveAbsence(ids) {
    for (const id of ids) {
      const node = nodes[id];
      if (!node || !node.never) continue;
      const out = [];
      for (const nv of node.never) {
        if (nv.lo === undefined) { out.push(nv); continue; }
        const hi = binder[nv.hi], lo = binder[nv.lo];
        if (hi && lo && nodes[hi]) {
          // The absence names the stretch from `lo` to `hi`, so it is the claim
          // itself -- not the premise list -- that orders the two events.
          // Nothing else in the statement does, so the edge is drawn here or
          // nowhere.
          if (!nodes[hi].deps.includes(lo)) {
            for (const other of Object.values(nodes))
              if (other !== nodes[hi] && other.deps)
                other.deps = other.deps.filter(d => d !== lo);
            nodes[hi].deps.push(lo);
            nodes[lo].owner = nodes[hi].owner;
          }
          nodes[hi].never = [...(nodes[hi].never || []), { def: nv.def, after: lo }];
        } else unsupported = true;
      }
      node.never = out;
      if (!out.length) delete node.never;
    }
  }

  // A named box that exists only to hold an absence mark it has handed on would
  // otherwise be drawn as an empty dashed box.
  for (const [id, node] of Object.entries(nodes))
    if (node.kind === "def" && !node.deps.length && !node.never) delete nodes[id];
  for (const node of Object.values(nodes))
    node.deps = (node.deps || []).filter(d => nodes[d]);

  // The same forbidden shape reached by two different routes was drawn twice and
  // numbered twice, so a reader had to compare two boxes character by character
  // to find out they said the same thing. Only NAMED absences were shared; this
  // shares the rest, by what the shape actually is.
  {
    const sig = id => {
      const n = nodes[id];
      return JSON.stringify([n.kind, n.label || "", n.checks || [], n.region || null,
                             (n.deps || []).map(sig)]);
    };
    const canonical = {}, alias = {};
    for (const node of Object.values(nodes))
      for (const nv of node.never || []) {
        const k = sig(nv.def);
        if (canonical[k] === undefined) canonical[k] = nv.def;
        else if (canonical[k] !== nv.def) alias[nv.def] = canonical[k];
      }
    if (Object.keys(alias).length) {
      const dead = new Set();
      const drop = id => { if (dead.has(id)) return; dead.add(id);
                           (nodes[id].deps || []).forEach(drop); };
      for (const id of Object.keys(alias)) drop(id);
      for (const node of Object.values(nodes))
        for (const nv of node.never || []) if (alias[nv.def]) nv.def = alias[nv.def];
      // A shape one route reaches through a box the other does not still has to
      // keep its own dots, so only what nothing else points at is removed.
      for (const [id, node] of Object.entries(nodes))
        if (!dead.has(id)) for (const d of node.deps || []) dead.delete(d);
      for (const id of dead) delete nodes[id];
      for (const node of Object.values(nodes))
        node.deps = (node.deps || []).filter(d => nodes[d]);
    }
  }

  // A named box holding a CHOICE needs somewhere for its alternatives to
  // converge. Usually they converge on whatever the box points at. Two cases
  // have no such point: a conjunct, where one arrow leaves for the whole box,
  // and a forbidden shape parked below the bar, which nothing points at at all.
  // The bar is that missing point: "this is needed, and for it you may take any
  // one of these back".
  //
  // Done here rather than in `case "named"`, where the enclosing box is known
  // by id but its node does not exist yet.
  const consumed = new Set();
  for (const node of Object.values(nodes)) for (const d of node.deps || []) consumed.add(d);
  const joinAfter = {};
  for (const [id, node] of Object.entries(nodes)) {
    if (!node.choice || node.deps.length < 2) continue;
    const owner = node.owner && nodes[node.owner];
    if (consumed.has(id) && !(owner && owner.kind === "group")) continue;
    const j = fresh("join");
    // Inside the box, so the layout reserves room for it. The box is a grouping
    // and nothing more, so which side of its border this sits on says nothing.
    nodes[j] = { kind: "join", label: "", deps: node.deps, owner: id, under: id };
    for (const e of node.deps) nodes[e].owner = id;
    node.deps = [j];
    joinAfter[id] = j;
  }
  // Model order is what the layout falls back on, so the bar is listed straight
  // after its box to keep it directly below rather than adrift in the row.
  if (Object.keys(joinAfter).length) {
    const ordered = {};
    for (const [id, node] of Object.entries(nodes)) {
      if (node.kind === "join" && Object.values(joinAfter).includes(id)) continue;
      ordered[id] = node;
      if (joinAfter[id]) ordered[joinAfter[id]] = nodes[joinAfter[id]];
    }
    nodes = ordered;
  }

  // An absence with no lower bound governs the whole run, so it is drawn on
  // every edge of its branch. Where that branch merges with a sibling before
  // the end of the trace, the mark used to land on the sibling's edges too --
  // the page then read "sent happened ... sent never happened". The shared EDGE
  // is now split instead: one copy per absence context, so the mark travels
  // only on the copy that belongs to its own branch. See `elements()`.

  return { root: bar, nodes, unsupported, size };
}

// What the claim says, and what the graph shows, as bags of text.
//
// `unsupported` is a self-report of KNOWN ignorance -- an unhandled shape. It
// cannot fire for a bug, since a bug is the case where the code believes it
// succeeded. Every silent defect so far was of that kind: an
// alternative dropped, a forbidden shape declared but never cited, the
// exception itself drawn as an event. So the graph is compared back against the
// claim it came from. This does not prove the picture MEANS the claim -- only
// an inverse reading would -- but nothing may go missing or appear from nowhere.
function contents(claim) {
  const ev = new Set(), ck = new Set();
  const walk = c => {
    if (["occurs", "occursAt", "stored", "storedAt", "absentBetween",
         "knows"].includes(c.kind))
      ev.add(evText(c));
    if (c.kind === "check" || c.kind === "opaque") ck.add(pretty(c.p));
    for (const k of ["a", "b", "c"]) if (c[k] && c[k].kind) walk(c[k]);
  };
  walk(claim);
  return { ev, ck };
}

function drawn(g) {
  const ev = new Set(), ck = new Set();
  // `? ` marks a hole the extractor could not classify; the text after it is
  // still the theorem's.
  const bare = s => s.replace(/^\? /, "");
  for (const n of Object.values(g.nodes)) {
    if (n.kind === "event") ev.add(n.label);
    for (const c of n.checks || [])
      if (c.alt) for (const grp of c.alt) for (const x of grp) ck.add(bare(x.p));
      else ck.add(bare(c.p));
  }
  return { ev, ck };
}

function audit(claim, g) {
  const said = contents(claim), shown = drawn(g), bad = [];
  const miss = (a, b, what) => [...a].filter(x => !b.has(x))
    .forEach(x => bad.push(`${what}: ${x}`));
  miss(said.ev, shown.ev, "event in the theorem but not drawn");
  miss(said.ck, shown.ck, "condition in the theorem but not drawn");
  miss(shown.ev, said.ev, "event drawn but not in the theorem");
  miss(shown.ck, said.ck, "condition drawn but not in the theorem");

  // A forbidden shape nobody cites is invisible: the branch it belongs to reads
  // as unconstrained. This is how half of `¬(a ∨ b)` once went missing.
  const cited = new Set();
  for (const n of Object.values(g.nodes))
    for (const nv of n.never || []) cited.add(nv.def);
  for (const n of Object.values(g.nodes))
    for (const nv of n.never || [])
      if (!g.nodes[nv.def]) bad.push(`forbidden shape missing: ${nv.def}`);
  return bad;
}

function lowerAll(entries) {
  const out = {};
  for (const raw of entries) {
    const e = { ...raw, claim: asNamed(raw.claim) };
    const short = e.name.replace(/^DYVis\.Theorem\./, "");
    try {
      const g = lowerTheorem(e);
      const bad = audit(e.claim, g);
      if (bad.length) { g.unsupported = true; g.mismatch = bad; }
      out[short] = g;
    } catch (err) {
      // Draw NOTHING rather than the exception: a node here would be read as
      // part of the theorem. The empty run is the one graph that asserts
      // nothing, and the banner says why it is empty.
      out[short] = { root: "bar", nodes: { bar: { kind: "end", deps: [] } },
                     unsupported: true, failed: String(err.description || err) };
    }
  }
  return out;
}
