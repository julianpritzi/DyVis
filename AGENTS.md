# Working on DYVis.Theorem (the theorem diagrams)

Read `DYVis/Theorem/README.md` before editing anything there. It is the design
record, not an overview: the notation, the rewrites and their proofs, and the
known gaps are all in it, and most mistakes made here are ones it already warns
about.

## A NUMBER IS NOT A COLOUR. THEY ARE DIFFERENT FACTS.

**`⟦n⟧` on an edge says WHAT IS FORBIDDEN ON THAT STEP.**
**A COLOUR says WHICH WALK YOU ARE ON.**

They are not two views of one thing, they are not interchangeable, and a
sentence that uses one to reason about the other is wrong. Every edge carries
both, independently:

- The **number** names a forbidden shape and scopes it to *the stretch that one
  arrow spans*. Nothing more. An unannotated arrow means anything could have
  happened there.
- The **colour** is an identifier for a WALK, and that is the whole of what it
  is. A walk is a commitment a reader carries *along a path* rather than reads
  off one step: picking a run means picking an arrow into the bar **and** a
  colour, and thereafter only arrows of that colour continue it.

### A COLOUR IS NOT AN ABSENCE

A walk is a path identity. It is not a `∄`, it does not mean a `∄`, and it does
not imply one. It happens that **the only thing in this tool that currently
declares a walk is an unbounded `∄`** — because that is, so far, the only
constraint a reader has to carry forward instead of reading off the arrow in
front of them. That is a fact about what has been built, **not** about what a
colour means. Any future constraint that has to be carried along a path would
declare a walk too, and none of the colour machinery would need to know it was
not an absence.

So: never argue from "this edge is coloured" to "something is forbidden here",
and never argue from "this run has no colour" to "this run is unconstrained".
Ask what declared the walk.

A `∄` over the whole run is drawn as **its number repeated on every step of the
walk**, and the colour is what tells the reader they are still on that walk. The
number and the colour coincide on most diagrams here only because the corpus's
walks are all declared by absences today — which is exactly why it is easy to
say something false about them and not notice.

Consequences you will get wrong if you blur them:

- "No arrow into the bar carries `⟦2⟧`" is **not** a statement about colour
  enterability. It is a statement that the last step is unbanned.
- A number on one arrow is a **correct and complete** drawing of a bounded
  absence, and a **broken** drawing of a whole-run one. The mark looks identical
  in both cases. You cannot tell which you are looking at without knowing what
  the claim said.
- Half the marked arrows in the corpus are each kind. Do not generalise from one.

## HOW TO DEBUG A DIAGRAM: ONE AT A TIME, SMALLEST FIRST

A count of broken diagrams is not a finding. Reporting "17 of 24 fail" tells
nobody what is wrong and gives nobody anything to look at. The corpus's diagrams
share machinery, so one defect shows up in a dozen of them at once — the number
measures reach, not causes.

The loop is:

1. **Pick the SIMPLEST failing diagram.** Fewest runs, fewest marks, fewest
   nodes. `compromised_unroll` beats `reached_deployed_server_or_trust_base_
   subverted` by a factor of three even though both carry the same defect.
2. **Find the pattern**, not the diagram's symptom. "Two boxes with the same
   name" is a pattern; "this one reads back wrong" is not.
3. **Isolate it as a theorem in `Example.lean`** that reproduces it on its own.
   Check that the minimal case really does have the same CAUSE and not merely
   the same look — a symptom usually has more than one route to it, and a
   reproducer built from the wrong one leads the fix astray.
4. **Then** fix it, and the example becomes the control that stops it returning.

### ISOLATE MEANS ISOLATE. DO NOT FIX IN THE SAME BREATH.

When asked to reproduce or isolate, **stop when it reproduces**. Fixing it in
the same step is not being helpful and it is not merely premature:

- **It destroys the artefact that was asked for.** An example that no longer
  reproduces is not a reproducer; it is a regression test for a fix nobody has
  reviewed, and the thing the user wanted to look at is gone.
- The user cannot see the defect on their own tree to judge whether it is the
  defect they meant.
- A fix chosen before the cause is agreed is a guess with a diff attached.

Report what reproduces and what the cause is. Wait to be asked for the fix.

## ACCEPTING A DIAGRAM IS THE USER'S DECISION, NEVER THE AGENT'S

**Never run `scripts/snapshot.sh --accept`, and never write to
any data directory's `accepted/`.** Not for a diagram you added, not for one you
changed, not for one that "obviously" looks right.

The baselines are an *approval* record. They say a human looked at the picture
and agreed it says what the theorem says — that is the entire content of the
test. An agent accepting its own output writes down the claim that a review
happened when none did, and destroys the only evidence that the pipeline is
checked by anything other than itself. It is worse than leaving the diagram
unreviewed, because unreviewed shows up in the counter and accepted does not.

What to do instead:

- Run `scripts/snapshot.sh` (no flags) to regenerate, and
  `--check` to confirm no *approved* diagram changed.
- Report which diagrams are NEW or CHANGED and say what to look at in each.
- Leave them for the user, who accepts from the picture with
  `scripts/review.sh`.

If an approved diagram changed, that is a finding to report, not a baseline to
refresh.

## The checks do not check everything

Before claiming a drawing is right because the tooling is green, know what the
green means:

- **The read-back cannot see WHERE a `∄` sits.** `read.js` compares bags of
  atoms per run, and an unbounded absence is deliberately collapsed by
  idempotence — so a mark on one step reads identically to the same mark spread
  over the whole path it governs. Under-scoped absences are invisible to it.
- **The read-back only inspects the UNFOLDED diagram.**
- **The audit checks the notation, not the theorem**, and its colour rules only
  reach absences that were given a colour in the first place.
- **`status: ok` means nothing was self-reported**, not that the picture is
  right.

So read the picture. `--check` passing is the floor, not the verdict.
