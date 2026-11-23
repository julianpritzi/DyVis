// The notation: a lowered graph plus a fold state, turned into the exact set of
// nodes and edges to be drawn. Everything here is a decision about MEANING --
// which `∄` rides which edge, what a box contains, which shapes are forbidden.
// `viewer.html` adds only styling and layout on top, so this is the last point
// at which the picture can be inspected as data. `tests/snapshot.mjs` reads it.
//
// Moved out of `viewer.html` unchanged. Nothing here touches the DOM or
// cytoscape; it reads `G` and `expanded` and nothing else.

// Edges point earlier -> later. Every node has `deps`, the nodes revealed by
// expanding it. `owner` says which box a node is drawn inside.
//   event  -- a logged event.
//   checks -- constraints with no event of their own to sit on; always a leaf.
//   group  -- an unnamed conjunction; always open, everything in it required.
//   def    -- a named predicate from the source; same containment, but foldable.
//
// Checks that DO have a binding event ride on that event instead. A container
// never carries checks itself, so its contents are always nodes.
//
// Argument names carry value identity along a PATH: the same name is the same
// value. Disjuncts are separate paths and never co-occur, so a name may be
// reused across them; two witnesses that meet on one path must be told apart.
let GRAPHS = {};
let G = { root: null, nodes: {} };
const expanded = new Set();

// A group carries no name of its own, so there is nothing to fold it down to.
// The end-of-trace bar is likewise always open: it is the anchor everything
// hangs from, so folding it would blank the diagram. A convergence bar is a
// point, not a thing that happened, so it has nothing to hide either.
const isOpen = id => G.nodes[id].kind === "group" || G.nodes[id].kind === "end"
                     || G.nodes[id].kind === "join"
                     || expanded.has(id);
// `also` is stated over the whole trace, not over `tr.prefix i`; drawn as an
// ordinary edge because the diagram only ever reads backwards from the trigger.
const revealed = id => [...G.nodes[id].deps, ...(G.nodes[id].also || [])];

// A forbidden shape is declared like any other, and is drawn only once some
// visible edge names it. It is never anyone's `dep`, so it stays unconnected:
// nothing in it happened.
function visibleFrom(seeds) {
  const vis = new Set(seeds);
  for (let changed = true; changed;) {
    changed = false;
    for (const id of [...vis])
      if (isOpen(id))
        for (const d of revealed(id))
          if (!vis.has(d)) { vis.add(d); changed = true; }
  }
  return vis;
}

// Which nodes draw their own inbound edges. A `∄` can only be shown on an edge
// that exists, so deciding what is drawn and what is revealed must use the
// SAME rule -- they drifted apart once, and the mark went missing in silence.
const drawsEdges = id => G.nodes[id].kind === "end" || G.nodes[id].kind === "join" ||
                         (G.nodes[id].kind === "event" && expanded.has(id));

// Where a bounded absence can come to REST: a point in the run, which an event
// and the end of the trace are. Not the same question as whether that point
// draws its edges, though the two look alike -- and running them together put
// the mark on the wrong stretch of trace. Unfolding a `def` shows what is
// INSIDE it, so its arrow abbreviates a region and a mark passes through to
// that arrow; unfolding an event shows what came BEFORE it, which is no
// business of the step leaving it. So an event rests a mark whether folded or
// not, and where that leaves the stretch off the page nothing is drawn: the
// `+N` already says there is more here to look at.
// A bar is an empty event: nothing is inside it to unfold, so a mark rests there
// exactly as it does on a real one.
const restsAt = id => ["event", "end", "join"].includes(G.nodes[id].kind);

// Where each bounded absence lands: on the edge LEAVING its lower end. That end
// may have no edge of its own -- a branch in which nothing happens is a lone dot
// inside a box, and the box is what points onwards -- so the mark is recorded
// against every level between the two, and the drawn source picks the one that
// applies. Unfolded that is the dot itself, so the mark stays on its own branch
// instead of spreading to the box's other alternatives; folded it is the box.
//
// Both `referenced` and `elements` read the placement from here, so what is
// revealed and what is drawn cannot drift apart.
function placements() {
  const goesTo = {};
  for (const [id, n] of Object.entries(G.nodes))
    for (const d of n.deps || []) goesTo[d] ||= id;
  const out = [];
  for (const n of Object.values(G.nodes))
    for (const nv of n.never || [])
      if (nv.after) {
        const seen = new Set();
        let from = nv.after, to = goesTo[from];
        const levels = [from];
        while (to && !restsAt(to) && !seen.has(to)) {
          seen.add(to);
          levels.push(to);
          from = to;
          to = goesTo[to];
        }
        if (to) for (const lvl of levels) out.push({ from: lvl, to, def: nv.def, origin: nv.after });
      }
  return out;
}

// The same forbidden shape may be declared in more than one place -- two boxes
// holding one `∄`. What is forbidden is one thing and wears one number; the
// WALK is one per declaration, because a reader on the run a sibling declared
// is not pinned to the branch that declares it here. So a mark is carried as
// `site + def` and reduced to `def` wherever it is the number that is wanted.
const TOK = "\u0001";
const tokOf = (site, def) => `${site}${TOK}${def}`;
const defOf = t => t.slice(t.indexOf(TOK) + 1);
// By DEF first, so a context's order is the one it had when marks were plain
// def ids and no baseline moves under a graph with one declarer per shape.
const sortToks = ts => [...ts].sort((a, b) => {
  const x = defOf(a), y = defOf(b);
  return x < y ? -1 : x > y ? 1 : a < b ? -1 : a > b ? 1 : 0;
});
function declarers() {
  const out = {};
  for (const [id, n] of Object.entries(G.nodes))
    for (const nv of n.never || [])
      if (!nv.after) (out[nv.def] ||= []).push(id);
  return out;
}

// Which `never`s a given visible set actually puts on an edge.
function referenced(base) {
  const marks = neverMarks(), refs = new Set();
  for (const p of placements())
    if (base.has(p.from) && base.has(p.to)) refs.add(p.def);
  for (const id of base) {
    if (drawsEdges(id))
      for (const d of G.nodes[id].deps) {
        if (!base.has(d)) continue;
        for (const t of marks[d] || []) refs.add(defOf(t));
      }
    // A dot cites its ban as much as an arrow does, and a dot is drawn on
    // anything closed. Without this the shape it names would be off the page.
    if (!isOpen(id) && G.nodes[id].kind !== "start")
      for (const t of marks[id] || []) refs.add(defOf(t));
  }
  return refs;
}

function visible() {
  // A forbidden shape can itself cite a forbidden shape, and that citation is
  // only found once the outer one is on the page, so this runs to a fixed point.
  let vis = visibleFrom([G.root]);
  for (;;) {
    const next = visibleFrom([G.root, ...referenced(vis)]);
    if (next.size === vis.size) return next;
    vis = next;
  }
}

// Everything drawn as forbidden: the roots of each `never` and their contents.
function negated() {
  const neg = new Set();
  const walk = id => {
    if (neg.has(id)) return;
    neg.add(id);
    for (const d of revealed(id)) walk(d);
  };
  for (const n of Object.values(G.nodes))
    for (const nv of n.never || []) walk(nv.def);
  return neg;
}

// Nodes revealed by expanding `id`. Groups are transparent because they open
// with their parent; a def is not, because it stays folded on its own.
function frontier(id) {
  const out = [];
  const walk = ds => ds.forEach(d =>
    G.nodes[d].kind === "group" ? walk(revealed(d)) : out.push(d));
  walk(revealed(id));
  return out;
}

// Which box each visible node is drawn inside.
function parents(vis) {
  const parentOf = {};
  for (const id of vis) {
    const o = G.nodes[id].owner;
    if (o && vis.has(o)) parentOf[id] = o;
  }
  return parentOf;
}

// The part of the graph a reveal from `id` currently covers: `id` itself plus
// everything unfolded below it. A `never` declared on `id` governs this whole
// stretch of trace, not just the segment it is written on.
function revealClosure(id, vis) {
  const seen = new Set([id]), stack = [id];
  while (stack.length) {
    const x = stack.pop();
    if (!isOpen(x)) continue;
    for (const d of revealed(x))
      if (vis.has(d) && !seen.has(d)) { seen.add(d); stack.push(d); }
  }
  return seen;
}

// Every node in the branch an unbounded `never` governs: the declaration, what
// it reveals, and everything between it and the trigger. Fold state is ignored,
// so a claim made inside a box still shows on the edge leaving it.
//
// Going back, a CONJUNCTION met on the way is met in FULL, so the ban reaches
// its other members too: they are steps of the same run. Left out, the steps
// inside a sibling conjunct came out unmarked, and since the branch as a whole
// could then only be entered on the colour, they were ink no reading could
// walk on -- and the ban they were under went unsaid on the very edges it
// governs, which is the one thing locality is for.
function neverMarks() {
  const back = {};
  for (const [id, n] of Object.entries(G.nodes))
    for (const d of revealed(id)) (back[d] ||= []).push(id);

  const marks = {};
  const conj = x => G.nodes[x] && (G.nodes[x].kind === "group" ||
                                   (G.nodes[x].kind === "def" && !G.nodes[x].choice));
  // Earlier in the run than the declaration, so under the same ban.
  const forward = (start, event) => {
    const seen = new Set(), stack = [start];
    while (stack.length) {
      const x = stack.pop();
      if (seen.has(x)) continue;
      seen.add(x);
      (marks[x] ||= new Set()).add(event);
      for (const y of revealed(x)) stack.push(y);
    }
  };
  // Later, up to the trigger.
  const backward = (start, event) => {
    const seen = new Set(), stack = [[start, true]];
    while (stack.length) {
      const [x, pure] = stack.pop();
      if (seen.has(`${x}|${pure}`)) continue;
      seen.add(`${x}|${pure}`);
      (marks[x] ||= new Set()).add(event);
      // Sideways only while no CHOICE has been crossed. Past a convergence bar
      // the run that declares the ban is ONE alternative among several, and the
      // conjuncts beside the choice are met by the others just as well -- so
      // marking them asserts the ban on runs that never had it. That is not
      // hypothetical: on the DANE trust-base theorem two bans declared in
      // sibling alternatives each reached 44 of the 72 nodes, and the picture
      // came to demand absences the theorem does not.
      if (pure && conj(x)) for (const y of revealed(x)) forward(y, event);
      const next = pure && G.nodes[x].kind !== "join";
      for (const y of back[x] || []) stack.push([y, next]);
    }
  };
  for (const [id, n] of Object.entries(G.nodes))
    for (const nv of n.never || [])
      if (!nv.after) { forward(id, tokOf(id, nv.def)); backward(id, tokOf(id, nv.def)); }
  return marks;
}

// A condition, or a set of alternative conditions. Only used to SIZE the node;
// the drawn form is in `viewer.html`.
//
// The alternatives are drawn as COLUMNS, so they have to be measured as
// columns. Run together on one line -- as they were -- the node came out as
// wide as every condition laid end to end and one line tall, which is neither
// dimension the label actually needs: far too wide, and too short to hold what
// is drawn in it.
const checkText = c => {
  if (!c.alt) return c.p;
  const cols = c.alt.map(g => g.map(x => x.p));
  const w = cols.map(col => Math.max(...col.map(s => s.length)));
  const rows = Math.max(...cols.map(col => col.length));
  const body = Array.from({ length: rows }, (_, r) =>
    cols.map((col, i) => (col[r] || "").padEnd(w[i])).join("   ").trimEnd());
  // The hairline drawn round a divided cell is not in this label, so the room
  // it needs has to be: a column each side for the border and its padding, and
  // a line for the top and bottom of it.
  return ["", ...body.map(s => ` ${s} `), ""].join("\n");
};

// One colour per forbidden shape. Muted, and never the colour of an ordinary
// arrow, so an unconstrained step stays visibly unconstrained.
const PALETTE = ["#a4443c", "#2f6fb5", "#2e7d52", "#8a5cb8", "#b8862a", "#1f8b8b"];

// An event's arguments are the same in every branch that mentions it, so on a
// big diagram they are most of the ink and none of the difference. Only what is
// DRAWN is shortened: `name` stays whole, so `read.js` still compares the full
// text, and a box label -- sometimes the only thing telling two branches apart
// -- is never touched.
let briefLabels = false;
const brief = s =>
  !s ? s : s.startsWith("{") ? "{…}" : s.replace(/^(\S+)\s+[\s\S]+$/, "$1 …");

// Edges name a forbidden shape by NUMBER rather than restating it. Two edges
// carrying the same number are then visibly one constraint, not two, and an
// edge can carry several without becoming unreadable. Numbered over the whole
// graph, so folding a box cannot renumber anything.
function tags() {
  const allIds = Object.keys(G.nodes), out = {};
  [...new Set(allIds.flatMap(id => (G.nodes[id].never || []).map(nv => nv.def)))]
    .sort((a, b) => allIds.indexOf(a) - allIds.indexOf(b))
    .forEach((id, i) => { out[id] = `\u27E6${i + 1}\u27E7`; });
  return out;
}

// Every absence the graph holds, whether or not it reached the page.
const declaredAbsences = () => Object.values(tags());

// Share the palette out between walks that never meet, so a page with six of
// them on disjoint paths stays two-coloured.
function dealHues(painted) {
  const meeting = {};
  for (const { data } of painted)
    (meeting[`${data.source}->${data.target}`] ||= new Set()).add(data.walk);
  const clash = {};
  for (const met of Object.values(meeting))
    for (const a of met) {
      clash[a] ||= new Set();
      for (const b of met) if (a !== b) clash[a].add(b);
    }
  // By the numbers a walk is made of, so the palette is dealt out in reading
  // order rather than in whatever order the edges happened to be emitted. Ties
  // by NAME: two walks banning one shape have the same numbers, and emission
  // order is not a fact about the picture.
  const nums = w => (w.match(/\d+/g) || []).map(Number);
  const slot = {};
  for (const w of Object.keys(clash).sort((a, b) => {
         const x = nums(a), y = nums(b);
         for (let i = 0; i < Math.max(x.length, y.length); i++)
           if ((x[i] ?? -1) !== (y[i] ?? -1)) return (x[i] ?? -1) - (y[i] ?? -1);
         return a < b ? -1 : a > b ? 1 : 0;
       })) {
    const taken = new Set([...clash[w]].map(x => slot[x]).filter(x => x !== undefined));
    let i = 0;
    while (taken.has(i)) i++;
    slot[w] = i;
  }
  return slot;
}

// The deal every view uses, taken once from the fully unfolded graph. Null
// while that pass is itself running, which then deals for itself.
let dealingHues = false;
function hueSlots() {
  if (G.__hueSlots) return G.__hueSlots;
  if (dealingHues) return null;
  dealingHues = true;
  const save = new Set(expanded);
  expanded.clear();
  for (const id of Object.keys(G.nodes)) if (revealed(id).length) expanded.add(id);
  const painted = elements().filter(e => e.data.source && e.data.walk);
  expanded.clear();
  for (const x of save) expanded.add(x);
  dealingHues = false;
  return G.__hueSlots = dealHues(painted);
}

function elements() {
  if (!G.root) return [];
  const vis = visible(), parentOf = parents(vis);
  // Reassigned once, by the walk collapse below.
  let els = [];
  // Declaration order, not discovery order: ELK keeps siblings in input order,
  // so anything else lets nodes swap sides when the graph changes.
  const order = Object.keys(G.nodes).filter(id => vis.has(id));

  // A `never` is a claim about a STRETCH of trace, so it rides on edges. With a
  // lower bound it annotates that one edge. Without one it governs the whole
  // branch, and once unfolded a dot marks where it reaches back past. What is
  // forbidden is spelled out once, in an unconnected box the labels name.
  const neverOn = {}, banAt = {}, banFrom = {}, marks = neverMarks(), dots = [], neg = negated();

  // Edges name a forbidden shape by NUMBER rather than restating it. Two edges
  // carrying the same number are then visibly one constraint, not two, and an
  // edge can carry several without becoming unreadable. Numbered over the whole
  // graph, so folding a box cannot renumber anything.
  const tag = tags();
  // An arrow wears only the NUMBER of what it forbids; the `∄` is said once,
  // on the shape itself, where there is room to say what it is.
  const marker = defs => defs.map(x => tag[x] || "?").join(" ");
  // What is FORBIDDEN on a step: numbers, one per shape however many places
  // declare it. Takes marks or plain defs, `defOf` being the identity on a def.
  const banMarker = xs => [...new Set(xs.map(x => tag[defOf(x)] || "?"))].join(" ");
  // WHICH WALK a step is on. One name per declaration, so two boxes holding the
  // same `∄` are two walks -- a reader on one of them is free here, and pinned
  // on the other. Lettered only where a shape has more than one declarer, so
  // every diagram in which it has one keeps the name it had.
  const LETTERS = "abcdefghijklmnopqrstuvwxyz";
  const walkTag = {};
  for (const [def, sites] of Object.entries(declarers()))
    sites.forEach((s, i) => {
      walkTag[tokOf(s, def)] = sites.length === 1 ? (tag[def] || "?")
        : `\u27E6${(tag[def] || "").replace(/\D/g, "")}${LETTERS[i] || i}\u27E7`;
    });
  const walkMarker = ts => ts.map(t => walkTag[t] || "?").join(" ");
  // A walk name back to the number it bans, for the copies the fill and the
  // dots make: those wear the walk's colour, and what they FORBID is the shape.
  const shapeOf = w => w.replace(/(\u27E6\d+)[a-z]+(\u27E7)/, "$1$2");
  // Colours are assigned once every marked arrow is known, since two absences
  // only need telling apart where they ride the same arrow. See `paint` below.
  let painted = [];

  // One edge can forbid SEVERAL shapes -- `¬(a ∨ b)` forbids both -- so they
  // accumulate. Keeping only the last silently dropped half the claim.
  for (const p of placements())
    if (vis.has(p.from)) (neverOn[`${p.from}->${p.to}`] ||= []).push(p.def);
  // The same, without the visibility test: a FOLDED box has to know what bans
  // the alternatives it speaks for are under, and those are by definition not
  // drawn. For anything visible the two agree.
  for (const p of placements())
    (banAt[`${p.from}->${p.to}`] ||= []).push(p.def);
  // Only where the ban ORIGINATES. A node that merely passes one on gets it
  // from the alternative that owns it, which is what lets the two be told apart.
  for (const p of placements())
    if (p.from === p.origin) (banFrom[`${p.from}->${p.to}`] ||= []).push(p.def);
  // An unbounded absence governs a whole run, so its mark rides up to wherever
  // that run rejoins its siblings -- and one arrow cannot say "never, on the way
  // here" for one branch and stay silent for another. So the ARROW is split
  // rather than the graph: one copy per absence context arriving at the source,
  // the marked copy carrying the run that forbids and the plain one the runs
  // that do not. Following a path backwards, an arrow's own mark is the whole
  // rule -- nothing has to be remembered from further down.
  const ctxCache = {};
  // A context holds ONE declarer per forbidden shape. Two of them ban the same
  // thing, so a run under both is the run under either read twice -- not a
  // third walk banning more, which is what a larger context means everywhere
  // else. Without this the both-declared branch took a colour of its own and
  // the two single ones lost the run they share.
  const oneEach = c => {
    const byDef = new Map();
    for (const t of sortToks(c)) {
      const d = defOf(t);
      if (!byDef.has(d)) byDef.set(d, []);
      byDef.get(d).push(t);
    }
    return [...byDef.values()].reduce(
      (acc, ts) => acc.flatMap(a => ts.map(t => [...a, t])), [[]]);
  };
  const norm = list => {
    const out = new Map();
    for (const c of list)
      for (const s of oneEach(c)) out.set(s.join("|"), s);
    return [...out.values()];
  };
  const contexts = d => {
    if (ctxCache[d]) return ctxCache[d];
    const own = marks[d] || new Set();
    if (!own.size) return ctxCache[d] = [[]];
    // Fold state is ignored, as it is for the marks themselves: a step is under
    // the same rules whether or not what leads to it is currently shown.
    const from = G.nodes[d].deps || [];
    // Nothing arrives here, so this IS the branch that declares the absence.
    if (!from.length) return ctxCache[d] = norm([sortToks(own)]);
    // Guard against a cycle while the answer is being computed.
    ctxCache[d] = norm([sortToks(own)]);
    const seen = new Map();
    // A GROUP's members are a CONJUNCTION: every run through it meets all of
    // them, so a path arrives carrying the union of what each member brings.
    // Taking them one at a time -- which is right where converging arrows are
    // alternatives -- also offers an arrival under only ONE member's absences,
    // and that arrow then permits a run the theorem forbids.
    const arrivals = G.nodes[d].kind === "group"
      ? from.reduce((acc, s) => {
          const cs = contexts(s), out = new Map();
          for (const a of acc)
            for (const c of cs) {
              const u = [...new Set([...a, ...c])].sort();
              out.set(u.join("|"), u);
            }
          return [...out.values()];
        }, [[]])
      : from.flatMap(s => contexts(s));
    for (const c of arrivals)
      // What travels with a path is the context it ARRIVED in, not everything
      // the source is touched by. Intersecting with the source's whole mark set
      // merges two runs into one arrow that then reads as a conjunction -- and
      // `¬(a ∨ b)` is a real conjunction, so the two must stay distinguishable.
      seen.set(sortToks(c.filter(m => own.has(m))).join("|"),
               sortToks(c.filter(m => own.has(m))));
    return ctxCache[d] = norm([...seen.values()]);
  };

  // One dot per POINT, carrying EVERY absence in force there. A dot each said
  // "under x, or under y" where the claim is "under x and under y" -- two
  // arrows into one node with different labels is the notation for a choice.
  //
  // Where the ban is in force is `marks`, not what the DECLARATION reveals: a
  // conjunct beside the one that declares it is just as much under it, and
  // reading only forward from the declaration left those leaves with no dot --
  // the event drawn as though nothing were forbidden before it while the
  // arrow leaving its box said otherwise.
  //
  // Nor does it depend on whether the DECLARING box is open. The ban governs
  // the run either way, so the declarations are read from the whole graph and
  // not from what is on the page: folding the box a ban is declared in used to
  // take the mark off every conjunct beside it, and the same event was under a
  // ban or not according to what the reader had happened to click.
  const dotDefs = new Map();
  for (const id of Object.keys(G.nodes))
    for (const nv of G.nodes[id].never || [])
      if (!nv.after)
        for (const x of order)
          // Never onto a dot. A branch in which nothing happens is ALREADY a
          // lone dot, and its own outgoing arrow carries what is banned there;
          // giving it one of its own draws a dot pointing at a dot.
          if (!isOpen(x) && G.nodes[x].kind !== "start" &&
              (marks[x] || new Set()).has(tokOf(id, nv.def))) {
            if (!dotDefs.has(x)) dotDefs.set(x, new Set());
            dotDefs.get(x).add(tokOf(id, nv.def));
          }
  for (const [target, defs] of dotDefs) {
    // The dot stands for everything folded away before `target`, and that may be
    // several ALTERNATIVES, each under its own bans. So its arrow is split the
    // way a real step's is -- one per context -- rather than drawn once per
    // absence with the UNION stamped on every copy, which says each walk
    // forbids whatever any of them forbids. On `accepted_one_or_other_unoffered`
    // that turned "no offer listed one or the other" into "neither": strictly
    // stronger, refusing runs the theorem allows. Only folded, because unfolded
    // the alternatives have arrows of their own and never meet here.
    //
    // A context that is a CONJUNCTION keeps all of its members, which is what
    // `accepted_neither_offered` needs: one run, under both.
    //
    // Including the context that carries NOTHING. A folded box may hold an
    // alternative under no ban at all -- `UnofferedOrRevoked`'s `revoked`
    // branch -- and dropping its group left the box with no plain arrow, so the
    // run that enters it that way had no way in and the box could not be
    // walked on the colour that run wears. The audit says so in as many words:
    // "box entered on red, but this member has no red arrow".
    const groups = new Map();
    for (const c of contexts(target)) {
      const mine = sortToks(c.filter(m => defs.has(m)));
      groups.set(mine.join("|"), mine);
    }
    dots.push({ dot: `${target}__start__`, target,
                groups: groups.size ? [...groups.values()] : [[...defs]] });
  }

  for (const id of order) {
    const n = G.nodes[id];
    const hidden = isOpen(id) ? 0 : frontier(id).length;
    // Which box a turn of a recursive predicate re-enters. Resolved here rather
    // than while lowering, where `owner` is still being assigned.
    if (n.kind === "loop") {
      let box = n.owner;
      while (box && G.nodes[box] && G.nodes[box].pred !== n.pred) box = G.nodes[box].owner;
      n.loopTo = (box && G.nodes[box] && G.nodes[box].pred === n.pred) ? box : "";
    }
    // The shape says `∄` once, with room to say what it is; the edges that cite
    // it wear only its number. A name that SAYS an absence wears the number
    // alone: the `∄` belongs to what is inside it, not to the name.
    const mark = !tag[id] || parentOf[id] ? ""
      : n.saysAbsence ? `${tag[id]} `
      : neg.has(id) ? `${tag[id]} \u2204 ` : "";
    if (n.kind === "group")
      // A group has no label of its own, so its number has to be drawn as the
      // box's title or the edges citing it point at nothing findable.
      els.push({ data: { id, kind: "group", neg: neg.has(id) ? "yes" : "no",
                         tag: tag[id] || "", title: mark.trimEnd(),
                         parent: parentOf[id] } });
    else {
      const base = briefLabels && n.kind === "event" ? brief(n.label)
        // Both the loop node and the box it re-enters print their own
        // arguments, so the substitution between them is already on the page.
        : n.kind === "loop" ? `\u21ba ${n.label}`
        : n.label;
      // Attacker knowledge reads as an event -- same box, same arrows, same
      // scope -- but no action in the run emits it, so a reader tracing it back
      // to a protocol step is looking for something that does not exist. The
      // bolt is what stops that search. Like the loop's `↺` it goes on what is
      // DRAWN and not on `name`, which `read.js` compares.
      const shown = n.knows ? `\u21af ${base}` : base;
      els.push({ data: { id, kind: n.kind, name: n.label || "", shown: shown || "",
                         hidden, checks: n.checks || [],
                         open: isOpen(id) ? "yes" : "no",
                         // Not an event anyone logs; see above.
                         knows: n.knows ? "yes" : "no",
                         // `mark` is what is DRAWN -- only a top-level forbidden
                         // shape wears its number. `tag` is WHICH shape this is,
                         // drawn or not, so one that no edge cites can be
                         // detected instead of sitting there unexplained.
                         neg: neg.has(id) ? "yes" : "no", mark, tag: tag[id] || "",
                         // The box a convergence bar belongs under.
                         under: n.under || "",
                         // An unfolded box draws its name from here instead.
                         title: mark + (n.label || ""),
                         // Sizes the node; the checks are extra lines, so they
                         // have to be in here as well as in the drawn label.
                         label: [...(shown ? [mark + shown +
                                              (hidden ? `   +${hidden}` : "")] : []),
                                 ...(n.checks || []).map(c =>
                                   checkText(c).split("\n").map(s => `  ${s}`).join("\n"))]
                                .join("\n"),
                         ctor: n.ctor || "",
                         parent: parentOf[id] } });
    }
  }
  for (const d of dots) {
    // A dot inside a forbidden shape belongs to it, and so is laid out with it.
    els.push({ data: { id: d.dot, kind: "start", parent: parentOf[d.target],
                       neg: neg.has(d.target) ? "yes" : "no" } });
    for (const defs of d.groups) {
      const base = { id: `${d.dot}->${d.target}#${defs.join("|")}`,
                     source: d.dot, target: d.target };
      // An empty context is not a walk: the run entering here is under nothing,
      // so the arrow stays plain and takes no colour. Painted, it was given a
      // hue slot under the empty name and came out red on a step that forbids
      // nothing -- a commitment with no consequence, and the wrong one.
      if (!defs.length) { els.push({ data: base }); continue; }
      // A walk is IDENTIFIED by the whole CONTEXT, and its numbers are its
      // stable name -- an internal id is regenerated with the graph and means
      // nothing outside it. The colour is a separate fact and NOT this name:
      // hues are shared out below between walks that never meet, so two may be
      // drawn in one colour.
      const data = { ...base, walk: walkMarker(defs),
                     never: banMarker(defs), path: walkMarker(defs) };
      painted.push({ data });
      els.push({ data });
    }
  }
  // A container's own deps are drawn inside it, so only events draw inbound
  // edges -- containment is what connects a box to what it holds.
  //
  // An UNFOLDED name is dissolved: an arrow means "this happened earlier", and
  // a named predicate is not an event, so the arrow only stands for its
  // contents. Folded it is a fair abbreviation; unfolded the contents speak for
  // themselves -- one arrow from the box a conjunction is grouped into, one per
  // alternative for a disjunction.
  const sourcesOf = d => (G.nodes[d].kind === "def" && isOpen(d))
    ? revealed(d).filter(x => vis.has(x)).flatMap(sourcesOf) : [d];

  // What a source would stand for with everything under it open. A FOLDED box
  // speaks for all of its alternatives at once, and they need not be under the
  // same bans -- so its arrow has to be split the same way an unbounded absence
  // splits one, or the box asserts one alternative's `∄` over the run that
  // sits beside it and the picture refuses a run the theorem allows. Fold state
  // is ignored here, exactly as it is for the marks themselves.
  const alternativesOf = d => {
    const inner = G.nodes[d].kind === "def" ? revealed(d) : [];
    return inner.length ? inner.flatMap(alternativesOf) : [d];
  };

  // What the arrow from `s` to `id` stands for: one (path-context, step-ban)
  // pair per alternative behind `s`. Unfolded those alternatives have arrows of
  // their own, each under its own rules; folded they share one arrow, and it
  // has to be split the same way or the arrow asserts one alternative's `∄`
  // over the run beside it -- refusing a run the theorem allows.
  //
  // The two are PAIRED, not taken separately: multiplying the contexts by the
  // bans would offer combinations no alternative has. The descent goes through
  // `def` and `event`, whose branches are alternatives, and stops at a `group`,
  // whose branches are a conjunction that every run meets in full -- and at
  // anything drawing its own edges, from where the alternatives carry their own.
  const entryCache = {};
  const entriesOf = (s, id) => {
    const key = `${s}->${id}`;
    if (entryCache[key]) return entryCache[key];
    const branching = !drawsEdges(s) && ["def", "event"].includes(G.nodes[s].kind);
    const alts = branching ? (G.nodes[s].deps || []) : [];
    if (!alts.length) {
      const ban = [...(banAt[key] || [])].sort();
      return entryCache[key] = contexts(s).map(ctx => ({ ctx: sortToks(ctx), ban }));
    }
    entryCache[key] = [];                          // guard against a cycle
    const own = marks[s] || new Set(), mine = banFrom[key] || [], seen = new Map();
    for (const a of alts)
      for (const e of entriesOf(a, id)) {
        // Only what originates HERE: anything else belongs to the alternative
        // it came from, and is already on that one's pair.
        const ban = [...new Set([...e.ban, ...mine])].sort();
        const ctx = sortToks(e.ctx.filter(m => own.has(m)));
        seen.set(`${ctx.join("|")}@${ban.join("|")}`, { ctx, ban });
      }
    return entryCache[key] = [...seen.values()];
  };

  for (const id of order)
    if (drawsEdges(id)) {
      for (const d of G.nodes[id].deps)
        if (vis.has(d)) {
          for (const s of sourcesOf(d))
            // The context belongs to the DRAWN source. Taking the box's
            // contexts instead gave every alternative inside it a copy per
            // context, and the page then offered runs the theorem does not.
            for (const { ctx, ban } of entriesOf(s, id)) {
              const nvs = [...ban, ...ctx];
              const base = { source: s, target: id,
                             // Everything precedes the end of the run, so there
                             // is no ordering there to weaken.
                             weak: (id !== G.root && G.nodes[s].weak) ? "yes" : "no" };
              // An arrow under no rule stays plain. Colour tracks the absences
              // that govern a whole PATH, so a step-local one -- an absence
              // between two named points -- wears its number without taking a
              // colour: there is no path to follow it along.
              if (nvs.length) base.never = banMarker(nvs);
              if (!ctx.length) {
                els.push({ data: { id: `${s}->${id}#@${ban.join("|")}`, ...base } });
                continue;
              }
              base.path = walkMarker(ctx);
              // ONE arrow per context, wearing one colour. A walk is what a
              // reader commits to and carries forward, and what has to be
              // carried here is the whole set: on a run under both `∄X` and
              // `∄Y`, neither number on its own says which run you are on, and
              // the continuations open to you are not those of the run under
              // `∄Y` alone. Drawn once per MEMBER, a context of two put two
              // arrows on the step wearing the colours of the runs beside it --
              // so the colour no longer decided anything, and where a smaller
              // context shared the step one of the copies was pure redundancy.
              const data = { id: `${s}->${id}#${ctx.join("|")}@${ban.join("|")}`,
                             ...base, walk: walkMarker(ctx) };
              painted.push({ data });
              els.push({ data });
            }
        }
      for (const d of G.nodes[id].also || [])
        if (vis.has(d))
          for (const s of sourcesOf(d))
            els.push({ data: { id: `${s}~${id}`, source: s, target: id } });
    }

  // The loop of a recursive predicate, drawn through a DOT beside the box: one
  // arrow from the whole expression back to the dot, and one from the dot to
  // each turn it has. A box may recur in several of its arms -- `ChainAuthExec`
  // does, in two -- and the dot is what says those are the same repetition
  // rather than several unrelated jumps.
  //
  // The dot sits BESIDE the box rather than inside it. An edge from a box to
  // its own descendant is clipped at the box's outer boundary, so cytoscape
  // sends it up and over the whole diagram; between siblings it is an ordinary
  // arrow.
  //
  // NOT a step: a run does not pass along it, and a ban on an edge traversed n
  // times has no reading. So these carry `loop` and every consumer of the
  // reading rule skips them. `serves` names the turns each belongs to, which is
  // how the hover finds them -- the dot is not a node any run visits.
  {
    const turns = {};
    for (const id of order) {
      const n = G.nodes[id];
      if (n.kind === "loop" && n.loopTo && vis.has(n.loopTo)) (turns[n.loopTo] ||= []).push(id);
    }
    for (const [box, ids] of Object.entries(turns)) {
      const dot = `${box}__again__`;
      els.push({ data: { id: dot, kind: "again", parent: parentOf[box] || undefined,
                         neg: neg.has(box) ? "yes" : "no" } });
      els.push({ data: { id: `${box}->${dot}`, source: box, target: dot,
                         loop: "yes", head: "no", tgtEnd: "outside-to-node",
                         bow: 0, serves: ids.join(" ") } });
      for (const t of ids)
        els.push({ data: { id: `${dot}->${t}`, source: dot, target: t,
                           loop: "yes", head: "yes", srcEnd: "outside-to-node",
                           bow: 0, serves: t } });
    }
  }

  // A run that passes through a CONJUNCTION passes through everything in it, so
  // every step inside has to be walkable in every colour the box is entered on.
  // Where a member's own steps are plain -- nothing forbidden is at stake in
  // them -- the walk arrived at the box and then had nowhere to go, and the box
  // read as though that member were not in it.
  //
  // A COPY, not a repaint: the colour says which walk this step is on, the `∄`
  // says what is forbidden on it, and the copy keeps the original's marks. Only
  // members with NO arrow of that colour are given one -- copying a step that
  // can already be walked in it adds a second, more constrained version of a
  // run the page already offers.
  //
  // The copy also wears the walk's OWN number. A step reached on walk `c` is on
  // a run that passes through `c`'s declaration, so `c` governs it, and locality
  // says every stretch a ban governs is drawn under it. Left off, the arrow was
  // red and said nothing forbidden, which is the reader asking "under what?"
  // and the page having no answer.
  //
  // Onto ONE alternative of the member, not all of them. A member may itself
  // hold a choice, and then walk `c` meets it by exactly one branch: the one
  // whose own context is `c` restricted to the absences that member declares.
  // Copying onto the others put an arrow of `c`'s colour on a branch `c` does
  // not take -- and where that branch was a `∄` declaration, on the very dot
  // that declares a ban the run under `c` is not under.
  {
    const kidsOf = {};
    for (const e of els) if (!e.data.source && e.data.parent) (kidsOf[e.data.parent] ||= []).push(e.data.id);
    const sub = id => [id, ...(kidsOf[id] || []).flatMap(sub)];
    // Which alternative an edge belongs to. `path` is the context the edge was
    // drawn for and survives a copy, where `walk` is overwritten by it.
    const ctxOf = e => (e.data.path || "").split(" ").filter(Boolean).sort().join(" ");
    for (const box of Object.keys(kidsOf)) {
      // A box holding a CHOICE is met by one alternative at a time, so a ban
      // declared in one says nothing about the run beside it. Painting its
      // colour across the siblings offers walks under a `∄` no branch of them
      // is under, and leaves dead paint wherever no arrow of that colour comes
      // in. A choice box entered from outside is filled by the conjunction it
      // is a member of, which copies onto the right branch of each member.
      if (G.nodes[box] && G.nodes[box].choice) continue;
      const own = new Set(sub(box));
      // A colour that arrives from outside, and one that starts on a member:
      // either way the run goes on through the rest of the box, so the rest of
      // the box has to be walkable in it.
      const through = new Set(els.filter(e => e.data.source && e.data.walk &&
                                              (own.has(e.data.source) || own.has(e.data.target)))
                                 .map(e => e.data.walk));
      if (!through.size) continue;
      for (const m of kidsOf[box]) {
        const mine = new Set(sub(m));
        const inside = els.filter(e => e.data.source && mine.has(e.data.target));
        const declares = new Set(inside.flatMap(e => ctxOf(e).split(" ").filter(Boolean)));
        for (const c of through) {
          const owns = c.split(" ").filter(t => declares.has(t)).sort();
          // Declared HERE: the walk is this member's own commitment, so it is
          // met by the branch that makes it and by no other.
          //
          // Declared in a SIBLING: nothing here is pinned, and a branch of this
          // member is on the walk whenever it adds no ban the walk is not
          // already under -- including one declaring the SAME shape somewhere
          // else, which commits the reader to nothing new. Two boxes holding
          // one `∄` need this both ways round: on either walk the other box is
          // free, and the run on which both declare it is those two read once
          // each rather than a third walk banning the same thing twice.
          const shapes = new Set(c.split(" ").map(shapeOf));
          const alt = owns.length
            ? inside.filter(e => ctxOf(e) === owns.join(" "))
            : inside.filter(e => ctxOf(e).split(" ").filter(Boolean)
                                  .every(t => shapes.has(shapeOf(t))));
          // Nothing here takes this run, so there is nothing to make walkable.
          if (!alt.length) continue;
          // Per BRANCH: a member met on the walk by more than one of them is
          // free on each, and one of them already carrying the colour says
          // nothing about the others. Where there is one, this is the whole of
          // the old test -- copying a step that can already be walked in it
          // adds a second, more constrained version of a run already offered.
          const branches = new Map();
          for (const e of alt) {
            const k = ctxOf(e);
            if (!branches.has(k)) branches.set(k, []);
            branches.get(k).push(e);
          }
          for (const es of branches.values()) {
            if (es.some(e => e.data.walk === c)) continue;
            for (const e of es) {
              const nv = [...new Set([...(e.data.never || "").split(" "),
                                      ...c.split(" ").map(shapeOf)].filter(Boolean))]
                .sort((a, b) => Number(a.replace(/\D/g, "")) - Number(b.replace(/\D/g, "")));
              const data = { ...e.data, id: `${e.data.id}+${c}`, walk: c, never: nv.join(" ") };
              painted.push({ data });
              els.push({ data });
            }
          }
        }
      }
    }
  }

  // An event with nothing drawn above it is still ON the runs that pass through
  // it, and a whole-run `∄` governs the stretch BEFORE it as much as any other.
  // With no dot a reader is entitled to read "and anything at all may have
  // happened first", which is the one thing such a `∄` denies.
  //
  // Where the event has arrows of its own, the runs it is on are the walks
  // those arrows are on -- and only the WALK's numbers travel back past it, a
  // bounded `∄` between two drawn points saying nothing about what came before.
  // With no arrows at all -- a bare member of a conjunction, which the trigger
  // usually is -- the runs are the box's, since every run through it meets them
  // all.
  //
  // Omitted where no run carries a ban: the dot would then say only "something
  // or nothing came before", which is what a reader infers from its absence.
  // Colour alone does not earn one.
  //
  // After the fill, so that a walk a member only carries by way of a copy is
  // counted. Only for EVENTS: a container's contents carry the arrows, and a
  // dot into the box asserts something before the BOX, which is a different
  // claim and one the contents already make.
  {
    const inbound = new Set(), outOf = {};
    for (const e of els)
      if (e.data.source) {
        inbound.add(e.data.target);
        (outOf[e.data.source] ||= []).push(e.data);
      }
    for (const id of order) {
      const n = G.nodes[id], o = n.owner;
      if (n.kind !== "event" || inbound.has(id)) continue;
      const walks = new Set();
      if (outOf[id]) for (const e of outOf[id]) walks.add(e.walk || "");
      else
        // Nothing of its own to read, so the runs are the enclosing box's, and
        // what says which those are is the box's OWN arrows -- every run
        // through a CONJUNCTION meets all of it, so a member is on exactly the
        // runs the box leaves under. Climbing while the box has no arrows
        // either, since the members of a conjunction do not draw their own.
        // Stopping at a CHOICE, which is met one alternative at a time and
        // whose members are therefore on a subset of its runs, not all of them.
        for (let x = id; ; ) {
          const p = G.nodes[x].owner;
          if (!p || !vis.has(p) || G.nodes[p].choice) break;
          if (outOf[p]) { for (const e of outOf[p]) walks.add(e.walk || ""); break; }
          x = p;
        }
      if (![...walks].some(Boolean)) continue;
      const dot = `${id}__before__`;
      els.push({ data: { id: dot, kind: "start", parent: parentOf[id] || o,
                         neg: neg.has(id) ? "yes" : "no" } });
      for (const w of walks) {
        const base = { id: `${dot}->${id}#${w}`, source: dot, target: id };
        if (!w) { els.push({ data: base }); continue; }
        const data = { ...base, walk: w, never: w.split(" ").map(shapeOf).join(" "), path: w };
        painted.push({ data });
        els.push({ data });
      }
    }
  }

  // A walk is a CLASS OF RUNS, and two walks offered on exactly the same steps
  // under exactly the same bans tell no two runs apart: choosing between them a
  // reader walks the same nodes forbidding the same things either way.
  //
  // A residual net. The case this was written for -- a CONJUNCTION of absences
  // drawn as one walk per member, `accepted_neither_offered` -- cannot arise now
  // that a walk is named by its whole context, and nothing in the corpus makes
  // it fire. It stays because the property it checks is the one that makes a
  // colour worth drawing, and it does not rest on an argument about which
  // shapes reach here.
  //
  // The step is paired with the BANS: on the steps alone this would also merge
  // two walks that are ALTERNATIVES over the same stretch -- `∄X` on one copy
  // and `∄Y` on the other -- which reads "no X AND no Y" where the theorem says
  // "no X OR no Y", refusing runs it allows. `accepted_one_or_other_unoffered`
  // is that shape, and nothing else in the corpus has it.
  {
    const offeredOn = {};
    for (const e of els)
      if (e.data.source && e.data.walk)
        (offeredOn[e.data.walk] ||= new Set()).add(
          `${e.data.source}->${e.data.target}|${(e.data.never || "").split(" ").sort().join(" ")}`);
    const rep = {}, cls = {};
    for (const w of Object.keys(offeredOn).sort())
      cls[w] = (rep[[...offeredOn[w]].sort().join(",")] ??= w);
    const drop = new Set();
    for (const e of els)
      if (e.data.source && e.data.walk && cls[e.data.walk] !== e.data.walk) drop.add(e.data.id);
    if (drop.size) {
      els = els.filter(e => !drop.has(e.data.id));
      painted = painted.filter(x => !drop.has(x.data.id));
    }
  }

  // Two walks only need telling apart where they MEET: on one step, or on
  // parallel copies of it, which are otherwise identical. Walks that never meet
  // reuse a colour, so a page with six of them on disjoint paths stays
  // two-coloured.
  //
  // Dealt from the FULLY UNFOLDED graph and reused in every view. Folding
  // MERGES walks -- two a closed box makes indistinguishable are one -- which
  // changes which of them meet, and dealing per view then repainted a reader's
  // own colour on a click that reveals nothing about it.
  const slot = hueSlots() || dealHues(painted);
  for (const { data } of painted) data.hue = PALETTE[slot[data.walk] % PALETTE.length];

  // Two arrows agreeing on their step, on what they forbid and on the walk they
  // are on ARE one arrow -- nothing drawn tells them apart, so the second is a
  // reading the first already offers. A folded box speaks for several
  // alternatives at once, and where a walk may take more than one of them the
  // copies collapse onto the same step; unfolded the alternatives have arrows
  // of their own and differ.
  {
    const seen = new Set();
    els = els.filter(e => {
      if (!e.data.source) return true;
      const k = `${e.data.source}->${e.data.target}|${e.data.never || ""}` +
                `|${e.data.walk || ""}|${e.data.weak || ""}`;
      return seen.has(k) ? false : (seen.add(k), true);
    });
  }

  return els;
}

// The reading rule applied to the drawing, with the claim thrown away: pick an
// arrow into the bar and a colour, follow arrows of that colour back. This is
// `read.js`'s traversal, and what is wanted from it here is only WHICH steps a
// reader can reach and WHERE a grey walk is asked to take up a colour.
//
// Visited states are remembered globally rather than per path, so a step some
// path can reach is counted reached. That over-approximates on purpose: this
// feeds a fault report, and a fault is worth reporting only when no reading
// whatsoever justifies the ink.
function walks(els) {
  const node = {}, into = {}, kids = {};
  for (const e of els)
    if (!e.data.source) { node[e.data.id] = e.data; (kids[e.data.parent || ""] ||= []).push(e.data.id); }
    else if (e.data.loop !== "yes") (into[e.data.target] ||= []).push(e.data);
  // A loop arrow is not a departure: it is not a step, so the node it
  // leaves is still read where it stands.
  const departs = new Set(els.filter(e => e.data.source && e.data.loop !== "yes")
                             .map(e => e.data.source));
  const forbidden = {};
  for (const id of Object.keys(node))
    if ((node[id].tag || "").trim()) forbidden[node[id].tag.trim()] = id;
  // Every walk offered on one step, so that a colour STARTING here can be told
  // from one offered a step earlier and declined.
  const offeredOn = (s, t) =>
    new Set((into[t] || []).filter(e => e.source === s).map(e => e.walk || null));

  const used = new Set(), starts = [], seen = new Set();
  const root = Object.keys(node).find(id => node[id].kind === "end");
  const stack = root ? [[root, null, new Set()]] : [];
  while (stack.length) {
    const [id, walk, offered] = stack.pop();
    if (!node[id]) continue;
    const key = `${id}|${walk}|${[...offered].sort().join(",")}`;
    if (seen.has(key)) continue;
    seen.add(key);
    // A box is a grouping: its contents are read on the walk that reached it.
    // What departs carries its own arrow and is read from there instead.
    for (const k of kids[id] || []) if (!departs.has(k)) stack.push([k, walk, offered]);
    for (const e of into[id] || []) {
      const c = e.walk || null;
      if (walk !== null ? c !== walk : !(c === null || !offered.has(c))) continue;
      used.add(e.id);
      if (walk === null && c !== null) starts.push(e);
      stack.push([e.source, c, offeredOn(e.source, id)]);
      // A forbidden shape is a run of its own, read from scratch.
      for (const m of (e.never || "").match(/\u27E6\d+\u27E7/g) || [])
        if (forbidden[m]) stack.push([forbidden[m], null, new Set()]);
    }
  }
  return { used, starts };
}

/** Faults visible only once the drawing is laid out, which the claim-to-graph
    audit in `lower.js` cannot see: it runs before the notation is applied. A
    forbidden shape nobody cites is the case that bit -- the branch it belongs
    to then reads as unconstrained.

    `declared` is every absence the LOWERED graph holds, so that one which never
    reached the page at all is caught too. The citation check alone cannot see
    it: that only looks at shapes already drawn. Pass `[]` for a FOLDED view,
    which hides shapes on purpose and says so with its `+N`. */
function auditElements(els, declared = declaredAbsences()) {
  const bad = [];
  const ids = new Set(els.filter(e => !e.data.source).map(e => e.data.id));
  for (const e of els)
    if (e.data.source && (!ids.has(e.data.source) || !ids.has(e.data.target)))
      bad.push(`edge with no node: ${e.data.id}`);
  const cited = new Set();
  for (const e of els)
    if (e.data.never) for (const m of e.data.never.match(/\u27E6\d+\u27E7/g) || []) cited.add(m);
  const shown = els.filter(e => !e.data.source && (e.data.tag || "").trim())
                   .map(e => e.data.tag.trim());
  for (const m of shown)
    if (!cited.has(m)) bad.push(`forbidden shape ${m} drawn but no edge names it`);
  // Being in `els` is not the same as being findable: a shape carries `tag`
  // whether or not anything paints it, and a group used to carry one with no
  // label to paint it on. So check the number a reader can actually SEE.
  const worn = new Set(els.filter(e => !e.data.source)
    .flatMap(e => `${e.data.title || ""}\n${e.data.label || ""}`
                    .match(/\u27E6\d+\u27E7/g) || []));
  for (const m of cited)
    if (!worn.has(m)) bad.push(`edge cites ${m} but no shape on the page wears it`);
  for (const m of declared)
    if (!cited.has(m) && !shown.includes(m))
      bad.push(`absence ${m} is in the graph but reaches no edge and is not drawn`);

  const node = {}, into = {}, kids = {};
  for (const e of els)
    if (!e.data.source) { node[e.data.id] = e.data; (kids[e.data.parent || ""] ||= []).push(e.data.id); }
    else if (e.data.loop !== "yes") (into[e.data.target] ||= []).push(e.data);
  const nameOf = id => (node[id] && (node[id].name || node[id].kind)) || id;
  // Where to point a reader: a bar or a dot has no name of its own, so the
  // nearest box that has one is what locates it.
  const inside = id => {
    for (let x = node[id] && node[id].parent; x && node[x]; x = node[x].parent)
      if (node[x].name) return ` in ${node[x].name}`;
    return "";
  };

  // A CONJUNCTION is met in full: every run through it meets all of its
  // members, so a colour that enters must be followable through each of them --
  // a member with no arrow of that colour leaves the walk with nowhere to go.
  // A box is DISSOLVED when open, its arrows landing on its contents, so a
  // member's colours are those of everything inside it. A box holding a CHOICE
  // is exempt: one alternative at a time is met, and requiring the others to
  // carry its colour is what put dead paint on the page.
  //
  // Keyed on the COLOUR the reader sees, not on the `⟦n⟧` an arrow wears. They
  // coincide here only because these absences happen to govern whole runs: a
  // colour says which walk you are on, a number says what is forbidden on that
  // step. Reporting the number invites reading this as a missing absence.
  const sub = id => [id, ...(kids[id] || []).flatMap(sub)];
  const hues = m => new Set(sub(m).flatMap(x => (into[x] || []))
    .map(e => e.hue).filter(Boolean));
  for (const g of Object.keys(node)) {
    if (!["group", "def"].includes(node[g].kind)) continue;
    if (G.nodes[g] && G.nodes[g].choice) continue;
    const mem = (kids[g] || []).filter(m => hues(m).size || (into[m] || []).length);
    if (mem.length < 2) continue;
    for (const c of new Set(mem.flatMap(m => [...hues(m)])))
      for (const m of mem)
        if (!hues(m).has(c))
          bad.push(`box entered on ${c}, but ${nameOf(m)} has no ${c} arrow`);
  }

  // Ink no reading can reach. Picking a run means picking an arrow into the bar
  // and a colour, and from there a coloured walk continues only on its own
  // colour; an arrow no such walk arrives at is one the rule can never put a
  // reader on. That is a stray copy, or an entry arrow gone missing, and it
  // misleads either way -- what is drawn is not what can be read, and nothing
  // downstream notices, because a walk that cannot be entered contributes
  // nothing to the claim read back. GREY arrows are checked too: a step inside
  // a branch that can only be entered on a colour is just as unwalkable, and
  // grey is the easier of the two to overlook.
  const { used, starts } = walks(els);
  for (const e of els)
    // A LOOP is not a step, so no reading walks it and the rule below does not
    // apply. What would make it wrong is a loop pointing at no box, which is
    // checked where it is drawn.
    if (e.data.source && e.data.loop !== "yes" && !used.has(e.data.id))
      bad.push(`${e.data.hue || "grey"} arrow into ${nameOf(e.data.target)}` +
               `${inside(e.data.target)} is on no walk a reader can enter`);

  // A grey walk may take up a colour, but only one that is DOING something
  // here: a colour means a `∄` governing the path from this step on. Starting a
  // colour on a step under no such ban asks the reader to commit to a walk that
  // constrains nothing, and the alternatives it offers are then indistinguish-
  // able -- there is no way to tell which was the right one to take, because
  // there is no difference between them.
  for (const e of starts)
    if (!e.walk.split(" ").every(m => (e.path || "").split(" ").includes(m)))
      bad.push(`${e.hue} starts at ${nameOf(e.target)}${inside(e.target)} but forbids` +
               ` nothing there: a choice with no consequence`);

  // Two dashed boxes with the same name AND the same arguments are the same
  // Lean expression, so a reader is entitled to treat them as one. One holding
  // a fraction of what its name means breaks that, and nothing downstream
  // notices: a name is transparent to `denote`, so the picture still reads back
  // as its claim. Compared only between boxes that are both open -- a folded
  // one shows a `+N` in place of its contents, which is no disagreement -- and
  // ignoring start dots, which mark the absences in force on a branch and so
  // differ between branches by design.
  const sig = id => [node[id].kind, node[id].name || "",
                     (node[id].checks || []).map(c => c.p || JSON.stringify(c.alt)).join(";"),
                     ...(kids[id] || []).filter(k => node[k].kind !== "start").map(sig)].join("|");
  const byName = {};
  for (const id of Object.keys(node))
    if (node[id].kind === "def" && node[id].open === "yes" && node[id].name)
      (byName[node[id].name] ||= []).push(id);
  for (const [nm, ids] of Object.entries(byName))
    if (new Set(ids.map(sig)).size > 1)
      bad.push(`${ids.length} boxes named ${nm}, and they do not hold the same thing`);

  return [...new Set(bad)];
}
