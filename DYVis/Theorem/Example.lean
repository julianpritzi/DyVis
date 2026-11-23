-- A minimal reference theorem in the DY framework: the smallest statement that
-- still has the shape every security theorem here has -- a trigger event, an
-- ordering between two events, and an escape disjunct.
--
-- The proof is `sorry` on purpose. This file exists to be READ by the theorem
-- graph extraction, not to prove anything.
--
-- Each theorem is traced where it stands, and the file writes them all at the
-- foot -- the same way a campaign would use this from its own module.
--
-- THE AUDIT SURFACE IS INLINE. `#traceClaim` emits `<thm>.claim`, the shape it
-- proposes, and `<thm>.isClaim`, a proof that the theorem IS that shape. The
-- proof is `Iff.rfl`, so the claim is not merely equivalent to the theorem but
-- the same proposition. Each trace is followed by its `#print axioms`, and the
-- check a reviewer runs is: no `sorryAx` in any of them.
--
-- Certification is FAITHFULNESS, not understanding. `denote (opaque p) tr` is
-- `p`, so a part of the statement the translation did not understand still
-- certifies -- truthfully, but saying nothing. The second number to read is the
-- `opaque` count the extractor warns about and records in the JSON; a claim is
-- only informative when that is zero. `accepted_or_attacker_knows` is the
-- worked example of one that is not.
--
-- See `not_a_trace_property` at the foot for what refusal looks like. What
-- remains unchecked is listed under "Known gaps" in README.md.
module

public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentGlobalState
public import DY.Trace.Reachability
import DYVis.Theorem.Extract

namespace DYVis.Theorem

open DY

/-- A one-message exchange plus the one thing that can go wrong. Polymorphic in
    the payload carrier, as real event alphabets are. -/
public inductive ExampleEvent (B : Type) where
  | sent (payload : B)
  | received (payload : B)
  | offered (payloads : List B)
  | accepted (payload : B)
  | revoked (payload : B)
  | keyLeaked (payload : B)

/-- A second alphabet, so one theorem can name events from two protocols the way
    a composed campaign's headline does. -/
public inductive OtherEvent (B : Type) where
  | connected (payload : B)

section

variable [BytesFunctor] [ExecTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (ExampleEvent Bytes))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (OtherEvent Bytes))]
-- Abstract, so the reference needs no `#combine`d model of its own.
variable (reachability : ReachabilityConfig)

/-- **Reference theorem.** A received payload was sent strictly before it was
    received, or the key protecting it leaked strictly before that too. -/
public theorem authentic (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was received at position `i` -/
      tr.EventLoggedAt (ExampleEvent.received payload) i →
      /- then it was sent strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∨
      /- or the key protecting it leaked strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.keyLeaked payload) := by
  sorry

#traceClaim authentic
#print axioms authentic.isClaim

/-- The exchange behind an acceptance: received before position `i`, and sent
    before that. A named predicate, so the diagram has a level to unfold into. -/
@[expose]
public def SentThenReceived (tr : ExecTrace) (payload : Bytes) (i : Nat) : Prop :=
  ∃ j, (tr.prefix i).EventLoggedAt (ExampleEvent.received payload) j ∧
    (tr.prefix j).EventLogged (ExampleEvent.sent payload)

/-- **Second reference theorem.** Acceptance needs BOTH earlier events, so its
    happy path is a conjunction rather than a single predecessor. -/
public theorem accepted_is_authentic (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was both sent and received strictly before that -/
      ((tr.prefix i).EventLogged (ExampleEvent.sent payload) ∧
       (tr.prefix i).EventLogged (ExampleEvent.received payload)) ∨
      /- or the key protecting it leaked strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.keyLeaked payload) := by
  sorry

#traceClaim accepted_is_authentic
#print axioms accepted_is_authentic.isClaim

/-- **Third reference theorem.** Same trigger as the second, but its happy path
    is a chain rather than a conjunction, so it unfolds twice. -/
public theorem accepted_follows_exchange (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was received earlier, having been sent before that -/
      SentThenReceived tr payload i ∨
      /- or the key protecting it leaked strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.keyLeaked payload) := by
  sorry

#traceClaim accepted_follows_exchange
#print axioms accepted_follows_exchange.isClaim

/-- **Fourth reference theorem.** The escape is stated over the whole trace, not
    over `tr.prefix i`, so it claims only that the leak is somewhere in the run.
    This is the common shape, and the one the diagram cannot draw as an arrow. -/
public theorem accepted_or_leak_anywhere (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∨
      /- or the key leaked at some point in the run, before or after -/
      tr.EventLogged (ExampleEvent.keyLeaked payload) := by
  sorry

#traceClaim accepted_or_leak_anywhere
#print axioms accepted_or_leak_anywhere.isClaim

/-- A receive with nothing on record behind it: the payload was received, and no
    send of it appears anywhere in the run. The escape is an ABSENCE, which no
    event can witness. -/
@[expose]
public def ForgedReceive (tr : ExecTrace) (payload : Bytes) (i : Nat) : Prop :=
  (tr.prefix i).EventLogged (ExampleEvent.received payload) ∧
  ¬ tr.EventLogged (ExampleEvent.sent payload)

/-- **Fifth reference theorem.** One disjunct says the send happened, the other
    says it never did -- so the diagram has to draw a non-event. -/
public theorem accepted_was_sent_or_forged (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∨
      /- or it was received although nothing ever sent it -/
      ForgedReceive tr payload i := by
  sorry

#traceClaim accepted_was_sent_or_forged
#print axioms accepted_was_sent_or_forged.isClaim

/-- Nothing revoked the payload between positions `j` and `i`. An absence with
    BOTH ends pinned to an event, rather than one running back to the start. -/
@[expose]
public def NoRevocationBetween (tr : ExecTrace) (payload : Bytes) (j i : Nat) : Prop :=
  ∀ k, j < k → k < i → ¬ tr.EventLoggedAt (ExampleEvent.revoked payload) k

/-- **Sixth reference theorem.** The absence is bounded by two drawn events, so
    it belongs to the stretch between them rather than to the whole run. -/
public theorem accepted_after_unrevoked_send (payload : Bytes) :
    ∀ (tr : ExecTrace) (i j : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at `i`, having been sent at `j` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      tr.EventLoggedAt (ExampleEvent.sent payload) j →
      /- then nothing revoked it in between -/
      NoRevocationBetween tr payload j i ∨
      /- or the key protecting it leaked -/
      tr.EventLogged (ExampleEvent.keyLeaked payload) := by
  sorry

#traceClaim accepted_after_unrevoked_send
#print axioms accepted_after_unrevoked_send.isClaim

/-- **Seventh reference theorem.** Most of the content is CHECKS relating the
    trigger's argument to a witness the earlier event bound, which is what real
    statements are mostly made of. -/
public theorem accepted_was_offered (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then some earlier offer listed it, and the offer was not empty -/
      ∃ offers : List Bytes,
        (tr.prefix i).EventLogged (ExampleEvent.offered offers) ∧
        payload ∈ offers ∧
        offers ≠ [] := by
  sorry

#traceClaim accepted_was_offered
#print axioms accepted_was_offered.isClaim

/-- An offer listing the payload. Used twice below, and each use binds its OWN
    `offers`, so the two witnesses are different values. -/
@[expose]
public def OfferedIn (tr : ExecTrace) (payload : Bytes) (i : Nat) : Prop :=
  ∃ offers : List Bytes,
    (tr.prefix i).EventLogged (ExampleEvent.offered offers) ∧ payload ∈ offers

/-- **Eighth reference theorem.** The same predicate appears in both disjuncts,
    as `RegisteredDnskeyExec` does across DANE's escapes. The two `offers` are
    unrelated values that happen to share a binder name. -/
public theorem accepted_offer_leaked_or_revoked (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was offered and the key leaked -/
      (OfferedIn tr payload i ∧ tr.EventLogged (ExampleEvent.keyLeaked payload)) ∨
      /- or it was offered and later revoked -/
      (OfferedIn tr payload i ∧ tr.EventLogged (ExampleEvent.revoked payload)) := by
  sorry

#traceClaim accepted_offer_leaked_or_revoked
#print axioms accepted_offer_leaked_or_revoked.isClaim

/-- **Ninth reference theorem.** Two `OfferedIn`s CONJOINED, so both witnesses
    live on one path and their binders -- both written `offers` -- are unrelated
    values that have to be told apart. -/
public theorem both_offered (payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then both payloads were offered, by offers that need not be the same -/
      OfferedIn tr payload i ∧ OfferedIn tr other i := by
  sorry

#traceClaim both_offered
#print axioms both_offered.isClaim

/-- **Tenth reference theorem.** `mid` is bound here and used by both
    sub-derivations, so the check relating it to `payload` spans the two -- the
    shape of `CompromisedExec`'s `isNameSubzoneOf` conjuncts. It is drawn on the one
    event that carries `mid`. -/
public theorem accepted_via_intermediate (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then some OTHER payload was offered and later revoked -/
      ∃ mid : Bytes,
        payload ≠ mid ∧
        OfferedIn tr mid i ∧
        tr.EventLogged (ExampleEvent.revoked mid) := by
  sorry

#traceClaim accepted_via_intermediate
#print axioms accepted_via_intermediate.isClaim

/-- Any offer at all listing the payload -- an event TOGETHER with the check
    that selects it. Negated below. -/
@[expose]
public def EverOffered (tr : ExecTrace) (payload : Bytes) : Prop :=
  ∃ offers : List Bytes,
    tr.EventLogged (ExampleEvent.offered offers) ∧ payload ∈ offers

/-- **Eleventh reference theorem.** The escape negates a DERIVATION, not a bare
    event -- the shape all three of DANE's absences take. -/
public theorem accepted_offered_or_unoffered (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then an offer listed it -/
      OfferedIn tr payload i ∨
      /- or it was received although no offer ever listed it -/
      (tr.EventLogged (ExampleEvent.received payload) ∧ ¬ EverOffered tr payload) := by
  sorry

#traceClaim accepted_offered_or_unoffered
#print axioms accepted_offered_or_unoffered.isClaim

/-- **MVE: ONE absence drawn as two.** `¬ EverOffered payload` is reached on two
    branches here -- once where the premises fail, once beside the premise that
    asserts the positive `EverOffered`. It is one absence: one forbidden shape,
    one number, one walk.

    It is not drawn as one. The positive premise binds `offers`, and
    `toClaimExpr` threads the names it has used into the next conjunct, so the
    negation's own
    witness comes out as `offers'` -- while on the branch where the premises
    fail nothing has been bound and it stays `offers`. `sharedAbsence` is keyed
    on the claim's JSON, so the two spellings are not recognised as the same
    absence: the page draws TWO shapes, numbers them apart, and offers the step
    under both once per colour -- a choice of walk that forbids exactly the same
    thing whichever way a reader takes it.

    A witness under a `∄` is bound by it, so nothing outside can name it and it
    has nothing to be told apart FROM. This is the shape `compromised_unroll`
    has, and the smallest instance of it. -/
public theorem accepted_offered_or_never_offered (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- and some offer listed it -/
      EverOffered tr payload →
      /- then it was sent -/
      tr.EventLogged (ExampleEvent.sent payload) ∨
      /- or no offer ever listed it after all -/
      ¬ EverOffered tr payload := by
  sorry

#traceClaim accepted_offered_or_never_offered
#print axioms accepted_offered_or_never_offered.isClaim

/-- **The other side of that control: two absences that must NOT be merged.**
    Binders under a `∄` are local, but its ARGUMENTS are not -- they name values
    of the run. So these two are different forbidden shapes however their own
    witnesses happen to be spelled, and a rule that merged absences by their
    contents alone would collapse them and claim the theorem forbids one thing
    where it forbids two. Kept beside the one above so a merge that goes too far
    fails here rather than in a campaign. -/
public theorem accepted_neither_offered (payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then no offer ever listed either of the two payloads -/
      ¬ EverOffered tr payload ∧ ¬ EverOffered tr other := by
  sorry

#traceClaim accepted_neither_offered
#print axioms accepted_neither_offered.isClaim

/-- **The other side of the walk collapse: two absences that must stay apart.**
    The same two `∄`s as above, now ALTERNATIVES rather than conjoined. The
    collapse must leave them as two walks: merged, the page would say "no offer
    listed either" where the theorem says "no offer listed one of them" --
    strictly stronger, refusing runs the theorem allows.

    Note what this does and does not pin. `accepted -> bar` really is ONE step
    carrying `⟦2⟧` on one copy and `⟦3⟧` on the other, which is the shape a
    collapse keyed on steps alone would get wrong. But the two branches reach
    that step from start dots of their own, so their walks differ anyway and
    the merge is refused whichever key is used. **The case where two walks agree
    on every step and differ only in their bans is pinned by nothing** -- no
    statement here produces it, and the `∨`-sharing rule may well make it
    unreachable, since a stretch two branches share has to impose the same
    constraints on both. The key pairs the step with the bans regardless: it
    costs nothing and does not rest on that argument holding. -/
public theorem accepted_one_or_other_unoffered (payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then no offer ever listed one or the other -- either will do -/
      ¬ EverOffered tr payload ∨ ¬ EverOffered tr other := by
  sorry

#traceClaim accepted_one_or_other_unoffered
#print axioms accepted_one_or_other_unoffered.isClaim

/-- **Nested contexts: the smaller must not swallow the larger.** Both
    alternatives forbid an offer listing `other`; one of them also forbids an
    offer listing `payload`. So the step they share is reached under two
    contexts, `{B}` and `{A, B}`.

    Drawn once per absence, `{A, B}` put TWO arrows on that step wearing the
    colours of `A` and of `B` -- so the colour no longer said which run you were
    on, and the `B`-coloured copy forbade strictly more than the `{B}` arrow
    beside it while offering the reader nothing to tell them apart by. A walk is
    named by its whole context instead, so `{A, B}` is one walk in a colour of
    its own: neither number alone continues a run on which both must hold.

    `peer_proof_of_possession_reachable` had 4 of these, and it was the shape
    every diagram failing its read-back for a reason other than an opaque leaf
    had in common. -/
public theorem accepted_unoffered_one_or_both (payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent, with neither payload ever offered -/
      (tr.EventLogged (ExampleEvent.sent payload) ∧
        ¬ EverOffered tr payload ∧ ¬ EverOffered tr other) ∨
      /- or it was sent, with only the other never offered -/
      (tr.EventLogged (ExampleEvent.sent payload) ∧ ¬ EverOffered tr other) := by
  sorry

#traceClaim accepted_unoffered_one_or_both
#print axioms accepted_unoffered_one_or_both.isClaim

/-- **The case that breaks the obvious repair.** Three alternatives on one step,
    under `{A}`, `{B}` and `{A, B}`. In the one above the redundant copy could
    have been dropped by drawing the larger context only under the member that
    tells it from the smaller -- and here `{A, B}` has NO such member. That rule
    would give this one nothing to be drawn under at all, and an alternative
    would vanish from the page: a picture offering too few runs refuses ones the
    theorem allows, silently.

    Naming a walk by its whole context has no such gap -- `{A, B}` is simply a
    third walk, in a third colour -- and this is what pins that. Nothing in the
    corpus has this shape today, which is exactly why it needs a control. -/
public theorem accepted_unoffered_either_or_both (payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent, with neither payload ever offered -/
      (tr.EventLogged (ExampleEvent.sent payload) ∧
        ¬ EverOffered tr payload ∧ ¬ EverOffered tr other) ∨
      /- or it was sent, with only this payload never offered -/
      (tr.EventLogged (ExampleEvent.sent payload) ∧ ¬ EverOffered tr payload) ∨
      /- or it was sent, with only the other never offered -/
      (tr.EventLogged (ExampleEvent.sent payload) ∧ ¬ EverOffered tr other) := by
  sorry

#traceClaim accepted_unoffered_either_or_both
#print axioms accepted_unoffered_either_or_both.isClaim

/-- An absence as one ALTERNATIVE inside a name -- the shape both DANE escapes
    have, and the shape `EverOffered` alone does not: negated bare, the `∄` is
    all there is to the branch, and the name's entry-less branch is what
    declares a walk. -/
@[expose]
public def UnofferedOrRevoked (tr : ExecTrace) (payload : Bytes) : Prop :=
  ¬ EverOffered tr payload ∨ tr.EventLogged (ExampleEvent.revoked payload)

/-- **The fill pass must copy onto ONE alternative of a member.** Each name is a
    CHOICE -- never offered, or revoked -- and only one of the two alternatives
    declares a walk. Conjoining two of them gives four genuine runs, and the four
    contexts on the box are all real: `{A, B}`, `{A}` alone (this one unoffered,
    the other revoked), `{B}` alone, and neither.

    On the `{A}` run the second name is met via its REVOKED alternative. A
    conjunction is met in full, so every member has to be walkable in every
    colour the box is entered on -- but copying every arrow inside the member
    made it walkable on branches the run does not take. The dot declaring `B`
    grew an `A`-coloured arrow: a reader who committed to the run under `A`
    alone was walked into the declaration of `B`, which that run is not under.
    Mirrored on the other side, `B`-coloured out of `A`'s dot. Which branch a
    walk takes is determined -- it is the one whose own context is the walk
    restricted to the absences that member declares -- so the copy goes there
    and nowhere else, and the eight arrows left are the four runs read twice.

    `accepted_neither_offered` is the same conjunction with the absences bare --
    no alternative beside them, one context, one walk. The three DANE headlines
    are this shape at `PublishedKeysAreRegisteredTlsKeys` (`⟦3⟧`) conjoined with
    `CompromisedExec` (`⟦4⟧`), and none of them read back until this. -/
public theorem accepted_with_two_named_absences (payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then each of the two payloads was never offered, or was revoked -/
      UnofferedOrRevoked tr payload ∧ UnofferedOrRevoked tr other := by
  sorry

#traceClaim accepted_with_two_named_absences
#print axioms accepted_with_two_named_absences.isClaim

@[expose]
public def AnchorUnofferedOrRevoked (tr : ExecTrace) (anchor payload : Bytes) : Prop :=
  ¬ EverOffered tr anchor ∨ tr.EventLogged (ExampleEvent.revoked payload)

/-- **MVE: two boxes holding the SAME absence.** `UnofferedOrRevoked` above with
    the absence's argument split off, and that is the whole difference: there the
    `∄` names the box's own payload, so two boxes hold two forbidden shapes; here
    it names the anchor, so two boxes at different payloads hold one.

    The theorem is met by taking one alternative from each box, and the two
    boxes are independent, so all four combinations are runs. The page offers
    only three: both absences (which are one shape, so they collapse to a single
    run) and both revocations. Take the absence in one box and the revocation in
    the other and there is no arrow for it -- 3 runs against the claim's 5,
    counting the branch where the premises fail.

    Too few runs is the direction that matters: the picture refuses runs the
    theorem allows, and nothing on it says an alternative is missing.

    `compromised_unroll` is this shape at `CompromisedExec`, whose `∄
    RegisteredDnskeyExec apex anchor` names the apex rather than the queried
    name. It appears either side of an implication there, which `denote_imp`
    puts side by side, and the inner DNSKEY-or-DS choice doubles each
    alternative -- so its picture has 12 runs where the claim has 16, and the
    four it loses are these two twice over. -/
public theorem accepted_with_one_shared_absence (anchor payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then each of the two payloads was revoked, unless the anchor was never
         offered -- and that is the same anchor both times -/
      AnchorUnofferedOrRevoked tr anchor payload ∧
        AnchorUnofferedOrRevoked tr anchor other := by
  sorry

#traceClaim accepted_with_one_shared_absence
#print axioms accepted_with_one_shared_absence.isClaim

/-- **Not-understood control.** The escape is a KNOWLEDGE fact rather than an
    event: it holds of the trace, but no entry witnesses it and it does not
    unfold here, so the extractor has no shape for it and records it as
    `opaque`. This is the common real case -- DANE's escapes are exactly this.

    The point of the control is that the certificate STILL goes through, because
    `denote (opaque p) tr` is `p`, so `isClaim` is as true here as anywhere. It
    is the warning below, and the `opaque` count in the JSON, that say the
    picture is missing a part of the statement. `#guard_msgs` pins both, so the
    day the extractor learns to read knowledge facts this control fails and has
    to be retired rather than quietly passing. -/
public theorem accepted_or_attacker_knows
    [BaseAttackerKnowledge] [AttackerKnowledge] (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∨
      /- or the attacker knew it all along, which no event records -/
      payload.AttackerKnows tr := by
  sorry

/- Attacker knowledge is a leaf like any other, so this certifies with nothing
   opaque. It is not an EVENT -- no action logs it -- but that only changes how
   the picture MARKS it, not whether the reader can follow it. Held as opaque it
   could never take a bound, and the whole disjunct went undrawn. -/
/--
info: traced DYVis.Theorem.accepted_or_attacker_knows (certified)
-/
#guard_msgs in
#traceClaim accepted_or_attacker_knows
#print axioms accepted_or_attacker_knows.isClaim

/-- **MVE: two event alphabets.** A real campaign's headline names events from
    several protocols -- DANE's mentions `DaneEvent`, `TlsEvent` and `DnsEvent`
    -- while `Claim E` carries exactly one event type. This is the smallest
    statement with that shape. -/
public theorem accepted_after_connect (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then a connection for it was opened strictly before that -/
      (tr.prefix i).EventLogged (OtherEvent.connected payload) := by
  sorry

#traceClaim accepted_after_connect
#print axioms accepted_after_connect.isClaim

/-- **MVE: value premises beside an event premise.** `offers ≠ []` and the
    disjunction constrain the PARAMETERS, not the trace: for a fixed `offers`
    each is simply true or false, so neither selects runs and neither can be
    drawn as one. The `offered` premise is different -- "no such offer in this
    run" is a real set of traces.

    The value premises are only readable because an event binds what they talk
    about, which is the shape DANE's R2 has. -/
public theorem accepted_from_listed_offer (payload : Bytes) (offers extras : List Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- given a non-empty offer list -/
      offers ≠ [] →
      /- in which the payload appears, here or among the extras -/
      (payload ∈ offers ∨ payload ∈ extras) →
      /- if that offer was made, and the payload accepted after it -/
      (tr.prefix i).EventLogged (ExampleEvent.offered offers) →
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) := by
  sorry

#traceClaim accepted_from_listed_offer
#print axioms accepted_from_listed_offer.isClaim

/-- **MVE: a check that projects a field of its witness.** A check rides on the
    event binding the witness it mentions. `offers.length` names `offers`, but
    only as a prefix, so the check does not recognise its own host and is drawn
    in a box of its own. DANE's R5 has the same shape at `rrset.rdata`. -/
public theorem accepted_offer_was_long (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then an earlier offer listed it alongside at least one other -/
      ∃ offers : List Bytes,
        (tr.prefix i).EventLogged (ExampleEvent.offered offers) ∧
        payload ∈ offers ∧
        offers.length ≠ 1 := by
  sorry

#traceClaim accepted_offer_was_long
#print axioms accepted_offer_was_long.isClaim

/-- **MVE: two alternative conditions on ONE event.** Not two runs -- one offer,
    qualifying either way. The alternatives are pure checks with no event of
    their own, and the event they qualify sits outside the `∨`, so there is
    nothing to converge them on and they are drawn as a divided cell on that
    event instead.

    This is the shape six of DANE's eight theorems turn on, at
    `RegisteredDnskeyExec`: "a DNSKEY RRset containing this key, or a DS RRset at
    the parent containing its digest" -- one signed RRset, two ways to qualify.
    None of them drew until the divided cell existed. -/
public theorem accepted_offer_listed_or_empty (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then one earlier offer qualifies, either by listing it or by being the
         catch-all empty offer -/
      ∃ offers : List Bytes,
        (tr.prefix i).EventLogged (ExampleEvent.offered offers) ∧
        (payload ∈ offers ∨ offers = []) := by
  sorry

#traceClaim accepted_offer_listed_or_empty
#print axioms accepted_offer_listed_or_empty.isClaim

/-- Both earlier events, behind a name: a conjunction the diagram can fold. -/
@[expose]
public def SentAndReceived (tr : ExecTrace) (payload : Bytes) (i : Nat) : Prop :=
  (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∧
  (tr.prefix i).EventLogged (ExampleEvent.received payload)

/-- Either earlier event, behind a name. Identical to `SentAndReceived` but for
    `∨`, so the two diagrams differ in exactly one thing. -/
@[expose]
public def SentOrLeaked (tr : ExecTrace) (payload : Bytes) (i : Nat) : Prop :=
  (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∨
  (tr.prefix i).EventLogged (ExampleEvent.keyLeaked payload)

/-- **MVE: a conjunct and a disjunct on one event.** The baseline for the two
    below: both hang off `accepted`, and the page has to say that one is
    required and the other is a choice. -/
public theorem accepted_with_conjunct_and_disjunct (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent, and also received or leaked -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∧
      ((tr.prefix i).EventLogged (ExampleEvent.received payload) ∨
       (tr.prefix i).EventLogged (ExampleEvent.keyLeaked payload)) := by
  sorry

#traceClaim accepted_with_conjunct_and_disjunct
#print axioms accepted_with_conjunct_and_disjunct.isClaim

/-- **MVE: a conjunction behind a name.** -/
public theorem accepted_via_named_conjunction (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then both earlier events happened -/
      SentAndReceived tr payload i := by
  sorry

#traceClaim accepted_via_named_conjunction
#print axioms accepted_via_named_conjunction.isClaim

/-- **MVE: a disjunction behind a name.** The pair to compare with: the same
    statement with `∧` replaced by `∨` inside the name. Nothing outside the box
    changes, so whatever tells the two diagrams apart is the notation for
    alternatives INSIDE a named box -- which DANE needs and no other reference
    theorem here exercises. -/
public theorem accepted_via_named_disjunction (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then one of the two earlier events happened -/
      SentOrLeaked tr payload i := by
  sorry

#traceClaim accepted_via_named_disjunction
#print axioms accepted_via_named_disjunction.isClaim

/-- **MVE: a trigger with no position.** Every reference theorem above is
    triggered by `EventLoggedAt … i`, and the bound a conclusion gets is stated
    against that `i`. This one is triggered by `EventLogged`, which names no
    position -- the shape DANE's R5 has, and the only one there. Without a
    position the conclusion cannot be bounded, and the ordering the theorem does
    give goes undrawn. -/
public theorem sent_before_acceptance (payload : Bytes) :
    ∀ tr : ExecTrace,
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at all -/
      tr.EventLogged (ExampleEvent.accepted payload) →
      /- then it was sent -/
      tr.EventLogged (ExampleEvent.sent payload) := by
  sorry

#traceClaim sent_before_acceptance
#print axioms sent_before_acceptance.isClaim

/-- **MVE: a non-recursive inductive predicate.** An escape defined by
    CONSTRUCTORS rather than by a `def`, which is what the corpus's chain and
    break predicates are. There is no body to delta-reduce, so this is not the
    `named` case; the extractor states the constructor characterisation, proves
    it, and draws that -- the box below is tied to its name by
    `Escaped.dyvisCases` rather than by defeq, which is what the extra info
    line reports. A predicate whose proof failed would be `opaque` instead.

    Also the smallest instance of a name whose alternatives include an ABSENCE,
    which is the shape `KeyBroken` has and no other reference theorem here. -/
public inductive Escaped (tr : ExecTrace) : Bytes → Prop where
  | leaked (payload : Bytes) :
      tr.EventLogged (ExampleEvent.keyLeaked payload) → Escaped tr payload
  | neverOffered (payload : Bytes) :
      (∀ i, ¬ tr.EventLoggedAt (ExampleEvent.offered [payload]) i) → Escaped tr payload

public theorem accepted_or_escaped (payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∨
      /- or it was beyond help, in one of the two ways that means -/
      Escaped tr payload := by
  sorry

/--
info: DYVis.Theorem.accepted_or_escaped: drawn via proved characterisation DYVis.Theorem.Escaped.dyvisCases; depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: traced DYVis.Theorem.accepted_or_escaped (certified)
-/
#guard_msgs in
#traceClaim accepted_or_escaped
#print axioms accepted_or_escaped.isClaim
#print axioms Escaped.dyvisCases

/-- **Recursive-inductive control.** The same thing one constructor deeper: the
    step cites the predicate again, so its characterisation cites itself.

    The tie is a ONE-STEP UNFOLDING rather than a closed form -- `I args ↔ base
    ∨ ∃ fields, indices = args ∧ I args' ∧ rest` -- and it is proved and kernel-
    checked like any other. What is drawn is one turn, whose events and checks
    are read like anything else, and a LOOP arrow back to the box. Both ends
    print their own arguments -- `ReachedFrom root mid` re-entering
    `ReachedFrom root payload` -- so what the turn does to them is on the page
    without a substitution beside it.

    That is not a claim that the recursion is understood. `Claim.again` denotes
    the predicate at the arguments this turn produced, exactly as `opaque` does,
    so nothing is asserted about chains of any particular length. What changed
    is that the turn itself is no longer a hole. -/
public inductive ReachedFrom (tr : ExecTrace) (root : Bytes) : Bytes → Prop where
  | here : ReachedFrom tr root root
  | step (mid next : Bytes) :
      ReachedFrom tr root mid → tr.EventLogged (ExampleEvent.sent next) →
      ReachedFrom tr root next

public theorem accepted_reached_from_root (root payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then a chain of sends of unbounded length reached it -/
      ReachedFrom tr root payload := by
  sorry

/--
info: DYVis.Theorem.accepted_reached_from_root: drawn via proved characterisation DYVis.Theorem.ReachedFrom.dyvisCases; depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: traced DYVis.Theorem.accepted_reached_from_root (certified)
-/
#guard_msgs in
#traceClaim accepted_reached_from_root
#print axioms accepted_reached_from_root.isClaim
#print axioms ReachedFrom.dyvisCases

/-- **Refusal control: a repetition under a `¬`.** The loop is drawn only in
    POSITIVE position. Negated, the claim is "no chain of ANY length reached
    it" -- a `∄` over an unbounded family, which the forbidden-shape notation
    does not have, and a single turn drawn under a `∄` would forbid far less
    than the theorem says. So the extractor refuses it and it stays `opaque`,
    which is the same treatment `distribute` gives an `∨` under a `¬`.

    `denote_imp` draws every premise negated in one branch, so this is not an
    exotic position: it is what any theorem taking a chain as a HYPOTHESIS
    would produce. Nothing in the corpus does today -- all twelve occurrences
    are positive -- which is exactly why it needs a control. -/
public theorem accepted_or_never_reached (root payload : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then it was sent strictly before that -/
      (tr.prefix i).EventLogged (ExampleEvent.sent payload) ∨
      /- or no chain of sends of any length reached it -/
      ¬ ReachedFrom tr root payload := by
  sorry

/--
warning: DYVis.Theorem.accepted_or_never_reached: 1 part(s) of the statement not understood; the certificate covers them as opaque
---
info: traced DYVis.Theorem.accepted_or_never_reached (certified, 1 opaque)
-/
#guard_msgs in
#traceClaim accepted_or_never_reached
#print axioms accepted_or_never_reached.isClaim

/-- A participant's stored state. Only the `stored` MVE below needs it. -/
public structure ExampleState where
  tag : Nat

/-- **FIXED: a conjunction was drawn as a choice when a check joined it.**
    The picture drew every atom and still offered more runs than the claim:
    three of its five held ONE of the three conjuncts where the claim requires
    all three. Arrows into one node with different labels is the notation for a
    CHOICE, so a conjunction reaching an event as separate arrows says the
    theorem permits any one of them.

    Every ingredient is load-bearing, and each was checked by removing it: with
    one event instead of two it read back; with the events but no check it read
    back; with all three but no escape beside them it read back.

    The cause was the guard against boxing members that are differently PLACED.
    A box has one outgoing arrow and can claim only what its weakest member
    claims, so boxing a bounded member with an unbounded one throws the bound
    away -- right for events, wrong for a CHECKS node, which has no region
    because it has no position rather than because it is unbounded. Counting it
    dissolved the box, and the members reached the event separately. The
    conjunction is a box again, and the choice is between the box and the
    escape. `response_authentication` was this shape. -/
public theorem accepted_with_check_and_two_events (payload other : Bytes) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then some OTHER payload was both sent and received -/
      (payload ≠ other ∧
        (tr.EventLogged (ExampleEvent.sent other) ∧
         tr.EventLogged (ExampleEvent.received other))) ∨
      /- or the key leaked -/
      tr.EventLogged (ExampleEvent.keyLeaked payload) := by
  sorry

#traceClaim accepted_with_check_and_two_events
#print axioms accepted_with_check_and_two_events.isClaim

/-- **FIXED: a whole-run state ENTRY was drawn on no run at all.** Two of the
    picture's four runs each dropped one of the two conjuncts.

    `narrow` bounded only `occurs`, on a stated assumption nothing backed, so a
    whole-run `stored` stayed unplaced -- and an unplaced member dissolves the
    box around its conjunction, exactly as the check above did. The entry ended
    up in the picture with nothing pointing at it and nothing pointing from it.
    Every leaf that carries a region is narrowed now, which is precisely the set
    `denote_bound` has a case for, so the lemma justifying the bound and the
    rewrite taking it agree on their scope.

    A caution about this one. It was built to reduce
    `endorsement_chain_soundness` and it reproduced that theorem's disagreement
    atom for atom -- and fixing this did NOT fix that theorem, which still fails
    with the same atom missing for a further reason: its state entry sits inside
    a named box. Reproducing a symptom is not reproducing a cause. -/
public theorem accepted_with_stored_and_event
    [ExecTraceTypes.Has (PersistentGlobalState.State.ExecEntryT ExampleState)]
    (payload : Bytes) (st : ExampleState) :
    ∀ (tr : ExecTrace) (i : Nat),
      /- for every trace the attacker can actually schedule -/
      tr.Reachable reachability →
      /- if this payload was accepted at position `i` -/
      tr.EventLoggedAt (ExampleEvent.accepted payload) i →
      /- then this state was stored and the payload was sent -/
      (tr.StateStored st ∧ tr.EventLogged (ExampleEvent.sent payload)) ∨
      /- or the key leaked -/
      tr.EventLogged (ExampleEvent.keyLeaked payload) := by
  sorry

#traceClaim accepted_with_stored_and_event
#print axioms accepted_with_stored_and_event.isClaim

/-- **Out-of-scope control.** Nothing to do with traces, put through the same
    procedure. The extractor must REFUSE it rather than invent a shape: there is
    no trace, so `stmt ↔ claim.denote tr` cannot even be stated, and no `claim`
    or `isClaim` is emitted. `#guard_msgs` makes that refusal a checked fact --
    this file stops building if the extractor ever silently accepts it. -/
public theorem not_a_trace_property (n : Nat) : n + 0 = n := by simp

/-- error: DYVis.Theorem.not_a_trace_property: no ExecTrace argument -- not a trace property -/
#guard_msgs in
#traceClaim not_a_trace_property

#traceClaimsToFile "diagrams/claims/reference.json"

end

end DYVis.Theorem
