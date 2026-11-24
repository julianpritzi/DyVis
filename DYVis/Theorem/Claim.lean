-- The grammar a theorem's conclusion is translated into. `denote` is written so
-- that "this claim means exactly this conclusion" is `Iff.rfl` -- see the
-- `#traceClaim` sites in `Example.lean` for the evidence, including a must-fail
-- control.
--
-- Binary `and`/`or` rather than n-ary: a list fold introduces the unit
-- (`A ∧ (B ∧ True)`), which is not definitionally the statement being matched.
module

public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentGlobalState
public import DY.Trace.Reachability

namespace DYVis.Theorem

open DY

/-- Which stretch of trace a claim is about. -/
public inductive Region where
  | whole
  | before (i : Nat)

section

variable [ExecTraceTypes]

-- The event type sits on the CONSTRUCTORS, not on `Claim`. A real headline
-- names events from several protocols at once -- DANE's mentions `DaneEvent`,
-- `TlsEvent` and `DnsEvent` -- which a single parameter cannot hold. Keeping
-- `ev : E` as data rather than a `Prop` is what makes `occurs` mean "an event
-- was logged" in the TYPE, so a reader of `<thm>.claim` need not trust the
-- extractor about it.
public inductive Claim where
  | occurs {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
      (ev : E) (region : Region)
  | occursAt {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
      (ev : E) (i : Nat) (region : Region)
  /-- No `ev` anywhere strictly between two positions. The stretch between two
      drawn events, which is where the diagram hangs a `∄` label. -/
  | absentBetween {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
      (ev : E) (lo hi : Nat) (region : Region)
  /-- A state ENTRY sitting in the run. `storeGlobalState` appends one of these
      rather than a `ProtocolEvent`, so `EventLogged` does not reach it -- but
      it is the same kind of fact, a thing at a position in the trace, and the
      diagram draws it as one. Kept apart from `occurs` because a reader asking
      "what emits this?" needs to know which of the two it is. -/
  | stored {S : Type} [ExecTraceTypes.Has (PersistentGlobalState.State.ExecEntryT S)]
      (st : S) (region : Region)
  | storedAt {S : Type} [ExecTraceTypes.Has (PersistentGlobalState.State.ExecEntryT S)]
      (st : S) (i : Nat) (region : Region)
  /-- The attacker knows this byte string. NOT an event -- nothing in the run
      logs it, and the picture marks it apart -- but a fact about a STRETCH of
      trace like any other, so it carries a `Region` and the bound rewrite
      narrows it to the trigger exactly as it does an unbounded `occurs`.

      Held as `opaque` it could not be re-scoped (`Below` is `False` there), so
      it never got the bound, never got an arrow, and refused every diagram it
      appeared in. -/
  | knows [BytesFunctor] [BaseAttackerKnowledge] [AttackerKnowledge]
      (b : Bytes) (region : Region)
  /-- A condition that does NOT mention the trace: a constraint on values. -/
  | check (p : Prop)
  /-- A trace property the extractor could not classify. Rendered as a hole and
      reported, so giving up is never silent. -/
  | opaque (p : Prop)
  /-- One turn on of a RECURSIVE inductive: the same predicate at the arguments
      this turn produced. Denotes what it holds, exactly as `opaque` does, so
      the certificate is untouched -- but it says which box it is a turn of,
      and the picture draws the loop back to that box in place of a hole.

      It is not a claim that the recursion is UNDERSTOOD. What is drawn is one
      turn, whose events and checks are read like any other, and an arrow
      saying the same box begins again with these arguments.

      `n` is what the loop node reads, `of` the predicate it re-enters. Both are
      here rather than recovered downstream so that the drawn node and the
      certified term are one object. -/
  | again (n of : String) (p : Prop)
  | and (a b : Claim)
  | or (a b : Claim)
  | not (c : Claim)
  /-- A theorem's premises implying its conclusion. Kept as an implication so
      that translating a statement stays definitional; the diagram draws it via
      `denote_imp` below, which is proved rather than assumed. -/
  | imp (a b : Claim)
  | ex (α : Type) (f : α → Claim)
  /-- A `∀` over data. HELD rather than rewritten on the way in, so translating
      a statement stays definitional and the certificate stays `Iff.rfl`; the
      diagram draws it via `denote_all_imp` below, which is proved. -/
  | all (α : Type) (f : α → Claim)
  /-- A named predicate from the source. Semantically transparent, so unfolding
      it in the diagram costs nothing. -/
  | named (n : String) (c : Claim)
  /-- An INDUCTIVE predicate. `denote` reads the predicate itself, so the
      certificate stays `Iff.rfl`; `arms` is the constructor characterisation
      the diagram draws in its place.

      The difference from `named` is the whole point of having both. A `named`
      body is the predicate delta-reduced, so it IS the predicate and `denote`
      may read it. An inductive has no body to reduce, and its characterisation
      is equivalent but not definitionally so -- so it is tied to `p` by a
      theorem `Extract.lean` generates and the kernel checks, and where that
      proof does not go through the predicate stays `opaque`. Nothing here can
      be reached by giving up.

      `tie` names that theorem. It is the one part of a drawing proved rather
      than definitional, so it belongs in the claim a reader audits. -/
  | cases (n of tie : String) (p : Prop) (arms : Claim)

@[expose]
public def Region.of (r : Region) (tr : ExecTrace) : ExecTrace :=
  match r with
  | .whole => tr
  | .before i => tr.prefix i

-- A constructor's instance field is NOT added to the instance context by a
-- match, so every event case binds it and passes it explicitly.
@[expose]
public def Claim.denote : Claim → ExecTrace → Prop
  | @Claim.occurs _ _ inst ev r, tr => @Trace.EventLogged _ _ inst ev (r.of tr)
  | @Claim.occursAt _ _ inst ev i r, tr => @Trace.EventLoggedAt _ _ inst ev i (r.of tr)
  | @Claim.absentBetween _ _ inst ev lo hi r, tr =>
      ∀ k, lo < k → k < hi → ¬ @Trace.EventLoggedAt _ _ inst ev k (r.of tr)
  | @Claim.stored _ _ inst st r, tr => @Trace.StateStored _ _ inst st (r.of tr)
  | @Claim.storedAt _ _ inst st i r, tr => @Trace.StateStoredAt _ _ inst st i (r.of tr)
  | @Claim.knows _ instBF instBAK instAK b r, tr =>
      @Bytes.AttackerKnows instBF _ instBAK instAK b (r.of tr)
  | .check p, _ => p
  | .opaque p, _ => p
  | .again _ _ p, _ => p
  | .and a b, tr => a.denote tr ∧ b.denote tr
  | .or a b, tr => a.denote tr ∨ b.denote tr
  | .not c, tr => ¬ c.denote tr
  | .imp a b, tr => a.denote tr → b.denote tr
  | .ex _ f, tr => ∃ a, (f a).denote tr
  | .all _ f, tr => ∀ a, (f a).denote tr
  | .named _ c, tr => c.denote tr
  | .cases _ _ _ p _, _ => p

/-- Why the premises may be gathered into one antecedent. A theorem states them
    curried, one arrow each, and that is the form the certificate is over; the
    diagram wants them as a single "these all held" so that failing them is ONE
    alternative rather than a chain of nested ones. -/
public theorem denote_curry (a b c : Claim) (tr : ExecTrace) :
    (Claim.imp a (.imp b c)).denote tr ↔ (Claim.imp (.and a b) c).denote tr := by
  simp only [Claim.denote]
  constructor
  · rintro h ⟨ha, hb⟩; exact h ha hb
  · intro h ha hb; exact h ⟨ha, hb⟩

/-- Why a condition may be moved next to the event it constrains. A value
    premise is not a statement about the run, so a branch of its own would read
    "no trace in which this condition fails" -- which is not a set of traces.
    Grouped onto its event, the branch becomes "no event of this description
    occurred", which is. -/
public theorem denote_and_comm (a b : Claim) (tr : ExecTrace) :
    (Claim.and a b).denote tr ↔ (Claim.and b a).denote tr := by
  simp only [Claim.denote]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

public theorem denote_and_assoc (a b c : Claim) (tr : ExecTrace) :
    (Claim.and a (.and b c)).denote tr ↔ (Claim.and (.and a b) c).denote tr := by
  simp only [Claim.denote]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- Why a trigger stated without a position may be given one. `EventLogged` IS
    `∃ i, EventLoggedAt … i`, so naming that position asserts nothing new -- but
    it is what lets the conclusion be bounded by the trigger, since the bound is
    stated against the trigger's own index. -/
public theorem denote_occurs_at {E : Type}
    [inst : ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    (ev : E) (tr : ExecTrace) :
    (Claim.occurs ev .whole).denote tr
      ↔ (Claim.ex Nat fun i => Claim.occursAt ev i .whole).denote tr := by
  simp only [Claim.denote, Region.of, Trace.EventLogged_iff]

/-- Why an implication may be drawn as two complete runs. The redundant `a ∧ b`
    is the point: plain `¬a ∨ b` would draw a branch that does not say whether
    `a` happened, and the diagram is read by following one branch down. -/
public theorem denote_imp (a b : Claim) (tr : ExecTrace) :
    (Claim.imp a b).denote tr ↔ (Claim.or (.not a) (.and a b)).denote tr := by
  simp only [Claim.denote]
  constructor
  · intro h
    rcases Classical.em (a.denote tr) with ha | ha
    · exact Or.inr ⟨ha, h ha⟩
    · exact Or.inl ha
  · rintro (hna | ⟨_, hb⟩) ha
    · exact absurd ha hna
    · exact hb

/-- Why "these did not all happen" may be split into one branch per premise:
    each branch is then a single absence, which is drawable. -/
public theorem denote_not_and (a b : Claim) (tr : ExecTrace) :
    (Claim.not (.and a b)).denote tr ↔ (Claim.or (.not a) (.not b)).denote tr := by
  simp only [Claim.denote]
  constructor
  · intro h
    rcases Classical.em (a.denote tr) with ha | ha
    · exact Or.inr fun hb => h ⟨ha, hb⟩
    · exact Or.inl ha
  · rintro (hna | hnb) ⟨ha, hb⟩
    · exact hna ha
    · exact hnb hb
/-- Why an alternative inside a conjunction may be lifted out. A solid box means
    "all of these", so a branch drawn inside one would read as a requirement;
    distributing turns each alternative into a complete run instead. -/
public theorem denote_and_or (a b c : Claim) (tr : ExecTrace) :
    (Claim.and a (.or b c)).denote tr
      ↔ (Claim.or (.and a b) (.and a c)).denote tr := by
  simp only [Claim.denote]
  constructor
  · rintro ⟨ha, hb | hc⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hc⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)
    · exact ⟨ha, Or.inl hb⟩
    · exact ⟨ha, Or.inr hc⟩

/-- Why a witness may be pulled out of a conjunction. `∃` is a binder, not
    structure: left where it is, it keeps the conjunction from flattening, and
    the events under it cannot be placed against the ones they sit beside. -/
public theorem denote_and_ex {α : Type} (a : Claim) (f : α → Claim)
    (tr : ExecTrace) :
    (Claim.and a (.ex α f)).denote tr
      ↔ (Claim.ex α fun x => .and a (f x)).denote tr := by
  simp only [Claim.denote]
  constructor
  · rintro ⟨ha, x, hx⟩; exact ⟨x, ha, hx⟩
  · rintro ⟨x, ha, hx⟩; exact ⟨ha, x, hx⟩

public theorem denote_ex_and {α : Type} (a : Claim) (f : α → Claim)
    (tr : ExecTrace) :
    (Claim.and (.ex α f) a).denote tr
      ↔ (Claim.ex α fun x => .and (f x) a).denote tr := by
  simp only [Claim.denote]
  constructor
  · rintro ⟨⟨x, hx⟩, ha⟩; exact ⟨x, hx, ha⟩
  · rintro ⟨x, hx, ha⟩; exact ⟨⟨x, hx⟩, ha⟩

/-- Why a `∀` over data may be drawn as a forbidden shape. "For every `x`, if
    `a x` then `b x`" is "there is no `x` with `a x` and not `b x`", and `∄` is
    what the notation already has for that -- so the obligation is drawn in the
    same vocabulary as everything else rather than as a hole. Classical, like
    `denote_imp`.

    A `∀` that is not an implication is left alone: there is nothing to forbid,
    and the shape has no reading here. -/
public theorem denote_all_imp {α : Type} (a b : α → Claim) (tr : ExecTrace) :
    (Claim.all α fun x => .imp (a x) (b x)).denote tr
      ↔ (Claim.not (.ex α fun x => .and (a x) (.not (b x)))).denote tr := by
  simp only [Claim.denote]
  constructor
  · rintro h ⟨x, ha, hnb⟩; exact hnb (h x ha)
  · intro h x ha
    rcases Classical.em ((b x).denote tr) with hb | hb
    · exact hb
    · exact absurd ⟨x, ha, hb⟩ h

/-- Why an obligation whose conclusion does not mention what it quantifies is a
    CHOICE rather than a nested absence. `∀x, a x → c` with `c` closed in `x` is
    "either nothing satisfies `a`, or `c` holds" -- one forbidden shape beside
    one ordinary claim, both of which the notation already draws.

    Without this the shape goes through `denote_all_imp` to `∄x, a x ∧ ¬c`, and
    when `c` is itself an `∃` -- as a registration or a key lookup is -- that
    `¬c` is an absence INSIDE an absence, which has no reading here.

    The side condition is the whole content: where `c` does mention `x` the two
    are not equivalent, and `denote_all_imp` is what applies. Classical. -/
public theorem denote_all_imp_const {α : Type} (a : α → Claim) (c : Claim)
    (tr : ExecTrace) :
    (Claim.all α fun x => .imp (a x) c).denote tr
      ↔ (Claim.or (.not (.ex α a)) c).denote tr := by
  simp only [Claim.denote]
  constructor
  · intro h
    rcases Classical.em (∃ x, (a x).denote tr) with ⟨x, hx⟩ | hn
    · exact Or.inr (h x hx)
    · exact Or.inl hn
  · rintro (hn | hc) x hx
    · exact absurd ⟨x, hx⟩ hn
    · exact hc

/-- Why the tail of a curried premise unfolds the same way. `∀x, a → b → c`
    leaves `¬(b → c)` behind, and this is what turns it into `b ∧ ¬c`, so a
    forbidden shape ends up as a plain list of what must have held. -/
public theorem denote_not_imp (a b : Claim) (tr : ExecTrace) :
    (Claim.not (.imp a b)).denote tr ↔ (Claim.and a (.not b)).denote tr := by
  simp only [Claim.denote]
  constructor
  · intro h
    rcases Classical.em (a.denote tr) with ha | ha
    · exact ⟨ha, fun hb => h fun _ => hb⟩
    · exact absurd (fun hx => absurd hx ha) h
  · rintro ⟨ha, hnb⟩ h; exact hnb (h ha)

/-- Why a telescope of binders becomes ONE forbidden shape. A statement is
    quantified one binder at a time, so once the innermost `∀` has become a `∄`
    every binder outside it is a `∀` of a negation -- and each of those is the
    same `∄` one witness wider. Without this only the innermost collapses and
    the rest are left as holes. -/
public theorem denote_all_not {α : Type} (f : α → Claim) (tr : ExecTrace) :
    (Claim.all α fun x => .not (f x)).denote tr
      ↔ (Claim.not (.ex α f)).denote tr := by
  simp only [Claim.denote]
  exact ⟨fun h ⟨x, hx⟩ => h x hx, fun h x hx => h ⟨x, hx⟩⟩

/-- Why a doubly negated claim is just the claim. A theorem's premise is drawn
    negated in the branch where it fails; a premise that is ITSELF an absence --
    an obligation over every publication -- therefore arrives as `¬¬`. Drawn
    literally that is a forbidden shape whose body is another one, which has
    nothing to show, so the box comes out empty. Transparent through a name,
    since `denote (named n c)` is `denote c`. -/
public theorem denote_not_not (c : Claim) (tr : ExecTrace) :
    (Claim.not (.not c)).denote tr ↔ c.denote tr := by
  simp only [Claim.denote]
  exact ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

/-! ### Congruence

The rewrites above are stated at the ROOT of a claim, but they are applied
wherever they match. These lift a rewrite of a part to a rewrite of the whole,
so a normaliser can compose one proof per step with `Iff.trans` rather than
mirroring the lemmas in meta code and hoping the mirror is faithful.

`cases` needs none: `denote` reads the predicate and not the arms, so rewriting
inside an arm changes the picture and not the proposition. What ties the arms to
the predicate is `tie`, not this. -/

public abbrev Rewrites (a b : Claim) : Prop := ∀ tr : ExecTrace, a.denote tr ↔ b.denote tr

public theorem Rewrites.rfl (a : Claim) : Rewrites a a := fun _ => Iff.rfl

public theorem Rewrites.trans {a b c : Claim} (h₁ : Rewrites a b) (h₂ : Rewrites b c) :
    Rewrites a c := fun tr => (h₁ tr).trans (h₂ tr)

public theorem Rewrites.and {a a' b b' : Claim} (ha : Rewrites a a') (hb : Rewrites b b') :
    Rewrites (.and a b) (.and a' b') := fun tr => and_congr (ha tr) (hb tr)

public theorem Rewrites.or {a a' b b' : Claim} (ha : Rewrites a a') (hb : Rewrites b b') :
    Rewrites (.or a b) (.or a' b') := fun tr => or_congr (ha tr) (hb tr)

public theorem Rewrites.imp {a a' b b' : Claim} (ha : Rewrites a a') (hb : Rewrites b b') :
    Rewrites (.imp a b) (.imp a' b') := fun tr => imp_congr (ha tr) (hb tr)

public theorem Rewrites.not {a a' : Claim} (ha : Rewrites a a') :
    Rewrites (.not a) (.not a') := fun tr => not_congr (ha tr)

public theorem Rewrites.named {a a' : Claim} (n : String) (ha : Rewrites a a') :
    Rewrites (.named n a) (.named n a') := fun tr => ha tr

public theorem Rewrites.ex {α : Type} {f g : α → Claim} (h : ∀ x, Rewrites (f x) (g x)) :
    Rewrites (.ex α f) (.ex α g) := fun tr => exists_congr fun x => h x tr

public theorem Rewrites.all {α : Type} {f g : α → Claim} (h : ∀ x, Rewrites (f x) (g x)) :
    Rewrites (.all α f) (.all α g) := fun tr => forall_congr' fun x => h x tr

public theorem Rewrites.cases (n of tie : String) (p : Prop) (a a' : Claim) :
    Rewrites (.cases n of tie p a) (.cases n of tie p a') := fun _ => Iff.rfl

/-! ### Re-scoping a claim to a truncation of the run -/

@[expose]
public def Region.bound (n : Nat) : Region → Region
  | .whole => .before n
  | .before j => .before j

/-- A region that is already narrower than `n` is unaffected by cutting the run
    back to `n`; one that is wider is not. -/
@[expose]
public def Region.Below (n : Nat) : Region → Prop
  | .whole => True
  | .before j => j ≤ n

@[expose]
public def Claim.Below (n : Nat) : Claim → Prop
  | @Claim.occurs _ _ _ _ r => r.Below n
  | @Claim.occursAt _ _ _ _ _ r => r.Below n
  | @Claim.absentBetween _ _ _ _ _ _ r => r.Below n
  | @Claim.stored _ _ _ _ r => r.Below n
  | @Claim.storedAt _ _ _ _ _ r => r.Below n
  | @Claim.knows _ _ _ _ _ r => r.Below n
  | .check _ => True
  -- An unclassified `Prop` mentions `tr` in a way nothing here can re-scope.
  | .opaque _ => False
  -- The predicate itself, one turn on; nothing here can re-scope that either.
  | .again _ _ _ => False
  | .and a b => a.Below n ∧ b.Below n
  | .or a b => a.Below n ∧ b.Below n
  | .imp a b => a.Below n ∧ b.Below n
  | .not c => c.Below n
  | .ex _ f => ∀ x, (f x).Below n
  | .all _ f => ∀ x, (f x).Below n
  | .named _ c => c.Below n
  -- `denote` reads the predicate, and nothing here can re-scope that.
  | .cases _ _ _ _ _ => False

@[expose]
public def Claim.bound (n : Nat) : Claim → Claim
  | @Claim.occurs _ _ inst ev r => @Claim.occurs _ _ inst ev (r.bound n)
  | @Claim.occursAt _ _ inst ev i r => @Claim.occursAt _ _ inst ev i (r.bound n)
  | @Claim.absentBetween _ _ inst ev lo hi r =>
      @Claim.absentBetween _ _ inst ev lo hi (r.bound n)
  | @Claim.stored _ _ inst st r => @Claim.stored _ _ inst st (r.bound n)
  | @Claim.storedAt _ _ inst st i r => @Claim.storedAt _ _ inst st i (r.bound n)
  | @Claim.knows _ instBF instBAK instAK b r =>
      @Claim.knows _ instBF instBAK instAK b (r.bound n)
  | .check p => .check p
  | .opaque p => .opaque p
  | .again n of p => .again n of p
  | .and a b => .and (a.bound n) (b.bound n)
  | .or a b => .or (a.bound n) (b.bound n)
  | .imp a b => .imp (a.bound n) (b.bound n)
  | .not c => .not (c.bound n)
  | .ex α f => .ex α fun x => (f x).bound n
  | .all α f => .all α fun x => (f x).bound n
  | .named s c => .named s (c.bound n)
  | .cases n of tie p arms => .cases n of tie p arms

public theorem Claim.Below.mono {c : Claim} {m n : Nat}
    (hmn : m ≤ n) : c.Below m → c.Below n := by
  induction c with
  | occurs _ r | occursAt _ _ r | absentBetween _ _ _ r | stored _ r | storedAt _ _ r
  | knows _ r =>
    cases r <;> simp only [Claim.Below, Region.Below] <;> first | omega | exact id
  | check _ => exact id
  | «opaque» _ => exact id
  | «again» _ _ _ => exact id
  | cases _ _ _ _ _ _ => exact id
  | and _ _ iha ihb | or _ _ iha ihb | imp _ _ iha ihb =>
    exact fun h => ⟨iha h.1, ihb h.2⟩
  | not _ ih => exact ih
  | ex _ _ ih | all _ _ ih => exact fun h x => ih x (h x)
  | named _ _ ih => exact ih

theorem region_bound_of (n : Nat) (tr : ExecTrace) (hn : n ≤ tr.length)
    (r : Region) (hr : r.Below n) : (r.bound n).of tr = r.of (tr.prefix n) := by
  cases r with
  | whole => rfl
  | before j =>
    have hlen := Trace.length_prefix tr n hn
    simp only [Region.Below] at hr
    simp only [Region.bound, Region.of]
    exact (Trace.le_imp_prefix_le_length_eq _ _ j (Trace.prefix_le_self tr n) (by omega)).symm

/-- Reading a claim on the run cut back to `n` is the same as reading the claim
    with its unbounded regions narrowed to `n`. This is what turns "the theorem
    also holds of the truncated run" into "these events happened by then". -/
public theorem denote_bound (n : Nat) (tr : ExecTrace) (hn : n ≤ tr.length) :
    ∀ c : Claim, c.Below n → (c.bound n).denote tr = c.denote (tr.prefix n) := by
  intro c
  induction c with
  | occurs ev r => intro h; simp only [Claim.bound, Claim.denote,
      region_bound_of n tr hn r h]
  | occursAt ev i r => intro h; simp only [Claim.bound, Claim.denote,
      region_bound_of n tr hn r h]
  | absentBetween ev lo hi r => intro h; simp only [Claim.bound, Claim.denote,
      region_bound_of n tr hn r h]
  | stored st r => intro h; simp only [Claim.bound, Claim.denote,
      region_bound_of n tr hn r h]
  | storedAt st i r => intro h; simp only [Claim.bound, Claim.denote,
      region_bound_of n tr hn r h]
  | knows b r => intro h; simp only [Claim.bound, Claim.denote,
      region_bound_of n tr hn r h]
  | check p => intro _; rfl
  | «opaque» p => intro h; exact absurd h (by simp [Claim.Below])
  | «again» _ _ p => intro h; exact absurd h (by simp [Claim.Below])
  | and a b iha ihb => intro h; simp only [Claim.bound, Claim.denote,
      iha h.1, ihb h.2]
  | or a b iha ihb => intro h; simp only [Claim.bound, Claim.denote,
      iha h.1, ihb h.2]
  | imp a b iha ihb => intro h; simp only [Claim.bound, Claim.denote,
      iha h.1, ihb h.2]
  | not c ih => intro h; simp only [Claim.bound, Claim.denote, ih h]
  | ex α f ih =>
    intro h
    simp only [Claim.bound, Claim.denote]
    exact congrArg Exists (funext fun x => ih x (h x))
  | all α f ih =>
    intro h
    simp only [Claim.bound, Claim.denote]
    exact congrArg (fun p => ∀ x, p x) (funext fun x => ih x (h x))
  | named s c ih => intro h; simp only [Claim.bound, Claim.denote, ih h]
  | cases _ _ _ p arms _ => intro h; exact absurd h (by simp [Claim.Below])
end

end DYVis.Theorem
