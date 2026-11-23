# DYVis.Trace — trace diagrams

A trace builder for DY sanity-check scenarios that draws a Mermaid sequence
diagram while it runs.

## Why

A DY execution trace records **what** happened but not **who** did it —
`Network.ExecEntryT` carries a `msg` and no sender, because in a Dolev–Yao model
every message is public and anybody may have placed it. Reconstructing
attribution afterwards means guessing from message content: brittle, and itself a
pile of code a reviewer must audit before trusting the picture.

DYVis takes attribution from the one place it is not in doubt — the call site.

## How

A scenario is an ordinary `Traceful` run in which each step also names its actor.
Drivers, byte algebra and trace are untouched; `Scenario` only carries a drawing
alongside.

```lean
format_lanes [root, child, wire, resolver]
format_strip ["Protocols.DNS.Security.Standalone.", "Protocols.DNS.", "DY."]
let h    ← send! "child KSK (to parent)" bytes
let sigH ← step! root ["RRSIG over DS RRset"] "" (Zone.publishDelegation …)
let st   ← step! resolver [] "" (Resolver.descendStep … childNameH h dsRrsetH sigH)
```

`step! lane [names for what it sends] "prose" (driver …)` — all four required.
`[]` and `""` say "nothing to add" explicitly. Optional parts were tried and
removed: a bracketed list and a parenthesised call are both terms, so the parser
picked the wrong one and silently dropped the names.

A step's label is the definition it calls, read off the head constant by the
elaborator, so it cannot drift. Its *reads* are read off the argument **types**:
`send` returns an opaque `Handle`, the only route to the `Nat` a driver wants is
`.id`, and the macro inserts that itself while recording the delivery. There is
no list of inputs to forget and none to pad.

`Network.receiveMessage` reads with `getEntry`, which appends nothing, so a read
leaves no evidence in the trace and cannot be derived from it — the type is what
makes it derivable instead.

There is deliberately **no lift from `Traceful`**. An action that can append trace
entries has to go through `step!`, `send!` or `peek`, so every entry is displayed
or counted; a bare `← someDriver` does not compile. `Err` lifts freely, since
`someOrErr` and `Comparse.parse` never touch the trace. `peek` is for reads that
append nothing — and counts anything they do append rather than letting it vanish.

A driver returning a bare `Nat` is wrapped as a `Handle` automatically, so it
cannot be passed on unseen. Some of those are local state rather than messages
(`Resolver.configure`'s result); a handle whose index is not a network entry
simply draws no delivery, which is checked against the trace rather than
declared.

A step's label is the definition it calls, read off the head constant by the
`actionName%` elaborator — so it cannot drift from the call. The optional string
is prose for when the name alone does not distinguish two steps
(`generateKeyPair` for a KSK and for a ZSK); it renders as a `/- … -/` comment on
the line above the name, the way it would read at the call site.

Everything named `format_` is presentation only. It can reorder or abbreviate,
but it cannot change what ran or hide a participant — `format_lanes` is an
ordering hint, and a lane the run touches is appended whether it is listed or
not; `format_strip` drops substrings from names. Names are fully qualified and a
campaign's steps come from unrelated namespaces, so there is no common prefix to
strip automatically.

Every step is drawn as an activation bar on its own participant's lifeline,
covering the messages it read, the step, and everything it left on the trace. A
step is local to one participant, so the bracket is on that lane rather than
across the diagram. The entries are found by scanning the trace range the step
appended, so sends buried inside a driver — ones the caller never sees a handle
for — are covered too. A driver cannot send invisibly, and it cannot send
*outside its own bar*.

Entries are named by the `ScenarioView` decoders, built with `eventDecoder%`,
which reads the **constructor names off the inductive** rather than taking a
table of strings:

```lean
instance : ScenarioView where
  decoders := [eventDecoder% (DnsEvent SBytes)]
```

So a decoder cannot describe an event as something it is not, and a renamed
constructor renames itself in the diagram. Which *types* to decode does have to
be listed — `TraceEntryHas` projects at a known entry type and the entry sum
carries no generic tag — but omitting one is safe: its entries are counted as
`«n entries»`, never dropped. Displayed items plus counts account for the whole
range.

`send` and `step!` remember the name a message was given, keyed by its handle,
and they are the *only* places a name is written. `recv` takes a lane and a
handle and no text: it renders the name the sender registered. So a receive
cannot describe bytes as something other than what was sent — there is no
`recv resolver "ZSK" h` for a handle sent as `KSK`. The delivery arrow lands
where the recipient actually reads it, not where the sender guessed it would.

`send` takes no lane. Bytes staged outside a step are drawn `wire->>wire`,
because nobody was seen to send them: no driver ran, and `Network.ExecEntryT`
records no sender. Environment staging, attacker construction and out-of-band
provisioning are indistinguishable to the model, so the diagram does not pretend
to tell them apart — only that the bytes became public.

## What is declared, what is derived

Declared: the lane and the label text. Derived from the trace: whether the step
ran at all, which messages it sent, every entry it appended, and the **handle in
brackets** on every message arrow. The step's *name* is derived from the
elaborated call, and event names from the constructors. So a stale label can
mis-*name* a step but cannot invent one, and cannot hide one; a step whose action
fails is drawn as `— REJECTED`, which is how the runs that are meant to abort
still produce a diagram.

The bracketed id is what moves the trust boundary into this library. It is the
real trace handle, taken from the action rather than from the scenario, so a
delivery can be matched to its send on the id alone:

```
  root->>wire: [34] RRSIG signer=root
  ...
  wire->>resolver: [34] RRSIG signer=root      ← same bytes, whatever the text says
```

## Value identity

A reader cannot otherwise tell whether two terms carry the same bytes. `Bytes` has
`DecidableEq` and `Ord`, so that question is answered from the run rather than by
the author: **every** term drawn gets a number, and

> equal numbers mean equal bytes, different numbers mean different bytes.

Numbering is **post-order** — a term's parts are numbered before the term itself —
so a composite always outranks its parts. That is what makes data flow readable:
in `sign:30(rand:3, rand:25, concat:29[…])`, the low numbers came from somewhere
earlier and the contiguous block above the previous high-water mark is what this
step built.

A number is handed out at the moment a term is first printed **whole**, so every
number has exactly one expansion, earlier in the diagram, and later sightings
print the number alone: `name:20`, `concat:24`, `vk:16`. That is also what stops a
depth-cut term from claiming a number it never explains. To find what `:29` is,
search for `:29` and take the first hit.

Adjacent copies of one term collapse to `×n`. That is a statement about bytes,
not about text: a rendering carries its instance number, so `lit:3 ×32` says the
same literal thirty-two times over.

`format_name "root KSK" b` attaches a name to a byte value. The name is
commentary and renders as `‹root KSK›` to say so. Named values take no number —
the name is the identity. Names apply to the whole diagram regardless of where
they are declared, since the same bytes must not render differently before and
after. Two names for one value, or a name matching no drawn message, is a
scenario bug and is drawn as one.

## Message structure

A label like `"DS RRset for child"` asserts something the model does not support:
`WireFormat` has round-trip laws *within* a type and no disjointness law *across*
types. An earlier renderer that guessed types by trying `parseAs` in turn had
`RrsigMeta` and `DnskeyRdata` at the same serialized width, and every RRSIG
rendered as a DNSKEY until the attempts were hand-ordered — the model saying the
two are indistinguishable, and the renderer overriding it.

`Bytes.view?` is a different thing. It projects the byte **algebra**, whose
sub-functors really are disjoint (`BytesView.view_pack_ne`), so probes may be
listed in any order and at most one can answer. What is derived is therefore
SHAPE, never type: structure can say `[name(…), lit#2, hash(vk(…))]`, and can
never say "this is a DS RRset". That is the point rather than a defect — it also
surfaces indistinguishability instead of hiding it.

Where structure is available it takes the trusted position and the author's prose
is demoted to a `/- … -/` comment, matching how steps already read:

```
  root->>wire: /- RRSIG over DS RRset -/<br/>[27] sign(rand#32@4, rand#32@25,
    [lit#2, lit#32, lit#2, name(lit#32, lit#4), lit#2, lit#2,
     hash([name(lit#32, lit#4), lit#2, vk(rand#32@12)]), lit#0])
```

The DNSSEC chain is now readable off the diagram: the root's key signs a DS that
hashes the child's KSK.

`concat` is the one **transparent** constructor — serialization builds
right-nested concats, so an n-field message is an n-deep tree that means nothing.
Everything else stays a visible wrapper. The risk worth guarding against is not a
shown wrapper being misread (nobody sees `hash(x)` and concludes `x` is public)
but the renderer flattening *through* something it should not and presenting `x`
at top level, looking like a field sent in the clear. A sub-functor no probe
opens renders `?`: ugly and obviously incomplete, which is the right direction.

Flattening has one exception, and it is what makes a signature readable. Splicing
a nested concat into its parent discards that node's identity, so the node never
takes a number — and the RRset a signature covers is exactly such a node, the
right operand of the signed form. It would show up as loose fields inside the
signature and then again, later, as a term that looks unrelated. So an operand
whose bytes are a message the diagram draws **somewhere else** is kept whole:

```
  [23] sign:23(rand:1, rand:12, concat:22[concat:14, concat:21[…]])
  [50] concat:14
  [51] concat:21
```

and "this signature covers exactly that RRset" is read off the numbers. The
exception is narrow by construction — only concat nodes, and only on exact byte
equality with a drawn message — so it cannot fire on a literal that happens to sit
inside everything, and it needs no heuristic.

A campaign registers the probes matching its own byte-functor combine:

```lean
instance : BytesShape where
  probes := stdProbes ++ [vkSymProbe, signSymProbe, hashSymProbe, dnsNameProbe]
```

`stdProbes` covers `Literal`, `Concat` and `Random`, which every algebra has.
A project's own constructors get their probes in that project, next to the
constructors they project (in DyAeneas: `DyAeneas/DYVis.lean`), so `DYVis` itself
stays DY-only and its checks stay
self-contained. DY's own `Hash` / `Sign` / `DiffieHellman` equational theories are
deliberately not imported: a project may ship replacements that collide with them
on names like `DY.Bytes.dhSkLabel` (DyAeneas does).

A term's structure is printed the first time it appears and referenced by number
afterwards, so a repeated message costs one token: the delivery of a TLS record
is just `[15] concat:18`.

## Reading a diagram

Each file holds the same run twice. **Overview** carries only the handles and the
author's prose — who acted and what moved. **Terms** carries the bytes. The
scenario is run once and the log drawn twice, so the two cannot disagree about
what happened; a handle in the overview names the term below it.


- `activate X` … `deactivate X` — one step by `X`: what it read, what it did,
  what it left on the trace. Activations never nest, because a step wraps a
  `Traceful` and covers a disjoint interval of the trace.
- `Note over X: ▸ …` — the step's name, taken from the definition it calls. The
  `▸` marks where a bar starts: Mermaid draws no gap between one activation and
  the next on the same lane.
- `Note over X: · name` — an event the step logged, named by its constructor.
- `Note over X: «n entries»` — entries no decoder claimed. Not hidden, counted.
- `⟦n⟧` — the trace handle of the message. Distinct brackets so it does not
  read as a concatenation.
- `‹name›` — what the author called that value. Declared, not derived.
- `f:k(x)` — a constructor of the byte algebra; `k` is the term's instance number.
- `concat:k[a, b]` — a concatenation, flattened. SHAPE, never message type.
- `concat:n[a, concat:k]` — `k` was kept whole: it is also a message on the wire.
- `f:k`, `concat:k` — that same term again; its structure is printed once, earlier.
- `x ×n` — n adjacent copies of that same term.
- A message longer than 60 characters breaks at the next `, `, never inside a
  quoted literal.
- `?:k` — a sub-functor no probe opens.
- `…` — the depth limit cut here. Unnumbered: it was never printed whole.
- `X->>wire: ⟦n⟧ …` — bytes `X` placed on the network, at trace handle `n`.
- `wire->>X: ⟦n⟧ …` — handle `n` read back, drawn just before the step reading it.
- An arrow with no `⟦n⟧` is a send the trace refused; every other arrow carries
  the real handle.
- `— REJECTED` — the driver returned `none`; the run stopped there.

The wire is drawn with Mermaid's `queue` stereotype rather than as a participant,
because it is not a principal: it is the public medium every message passes
through, readable and writable by anyone. That syntax needs Mermaid v11.12+; if
your renderer is older, drop the `@{ … }` in `participantLine`.

## Notes

Diagrams are output only. They carry no claim and are not asserted by any
`#guard`; the `#guard`s scan `Scenario.trace`, which is the same trace the
drivers would have produced without DYVis.

`Scenario.writeDiagram` writes a Markdown file with a `mermaid` fence, relative
to the directory `lake build` runs in (the workspace root). Diagrams live in a folder
beside the module that generates them — `…/Standalone/SanityScenarios/` — and are
**committed**, so they can be read on GitHub, which renders `mermaid` fences,
without building the project. There is no CI, so keeping them fresh is a
convention: they are rewritten by `#eval` on every build that re-elaborates their
module, so commit the regenerated files alongside whatever changed them.

`#eval` only runs when the module is elaborated, so `touch` the file to force a
regeneration after a cached build.

`Scenario` is defined directly rather than as `StateT _ Traceful`: `Traceful`
keeps the trace on failure but drops the value, so a `StateT` would discard every
line accumulated before an intended abort.

## Checks

`DYVis/Trace/Check/` is isolated and self-contained: it brings its own minimal
execution config built from DY alone, so DYVis depends on no protocol. It is not
imported by `DYVis/Trace.lean` — `Check/Config.lean` registers global instances, and a
campaign picking those up alongside its own would have two of each. It builds
with the library because the lib globs `DYVis.+`.

Assertions are semantic, never golden strings. The scenarios double as a demo
tour: regenerate `DYVis/Trace/Check/Basic/` and look at them when changing the renderer.

## Status

Prototype. Exercised by
`Protocols/DNS/Security/Standalone/SanityScenarios.lean` and
`Protocols/TLS/Security/Standalone/SanityScenarios.lean`.
