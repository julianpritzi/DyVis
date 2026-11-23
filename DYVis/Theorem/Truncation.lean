-- Why a conclusion stated over the whole trace is still bounded by the event
-- that triggered it.
--
-- A security theorem holds of EVERY reachable trace, so it also holds of the run
-- truncated to just after its trigger. Whatever the conclusion says exists must
-- therefore already exist by then. This is what would license drawing an
-- unbounded `EventLogged` in a conclusion as happening no later than the trigger.
module

public import DYVis.Theorem.Claim
public import DY.Actions.ProtocolEvent
public import DY.Trace.Reachability

namespace DYVis.Theorem

open DY

variable [ExecTraceTypes]

/-- A guarantee that some event occurred *somewhere*, if it holds of every
    reachable trace, already holds of the run truncated just after its trigger.

    The bound is a step boundary, not the trigger's own index: one step may log
    several entries, so this says "by the end of the step that logged the
    trigger", which is weaker than "strictly before the trigger". -/
public theorem occurs_by_trigger
    {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {config : ReachabilityConfig} (trigger goal : E) (i : Nat)
    (H : ∀ tr : ExecTrace, tr.Reachable config →
           tr.EventLoggedAt trigger i → tr.EventLogged goal)
    (tr : ExecTrace) (hr : tr.Reachable config)
    (hi : tr.EventLoggedAt trigger i) :
    ∃ n, i < n ∧ (tr.prefix n).EventLogged goal := by
  have hlen := Trace.EventLoggedAt_implies_i_le_length trigger i tr hi
  obtain ⟨n, hin, hnle, hn⟩ := hr.exists_prefix_containing i hlen
  exact ⟨n, hin, H (tr.prefix n) hn
    (Trace.EventLoggedAt_prefix trigger i n tr hin hnle hi)⟩

/-- The payoff. A theorem's conclusion may be read with its unbounded regions
    narrowed to a point just past the trigger, because the theorem also holds of
    the run truncated there.

    `n` is only known to exceed `i`, not to equal `i + 1`: one step may log
    several events, so this places the conclusion's events no later than the
    trigger's STEP rather than strictly before the trigger itself.

    `i` is fixed before `H`, so `c` may be scoped to it -- which it usually is,
    the trigger's index being what the conclusion is stated relative to. -/
public theorem conclusion_bounded_by_trigger
    {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {config : ReachabilityConfig} (trigger : E) (i : Nat) (c : Claim)
    (H : ∀ tr : ExecTrace, tr.Reachable config →
           tr.EventLoggedAt trigger i → c.denote tr)
    (tr : ExecTrace) (hr : tr.Reachable config)
    (hi : tr.EventLoggedAt trigger i) (hc : c.Below i) :
    ∃ n, i < n ∧ (c.bound n).denote tr := by
  have hlen := Trace.EventLoggedAt_implies_i_le_length trigger i tr hi
  obtain ⟨n, hin, hnle, hn⟩ := hr.exists_prefix_containing i hlen
  refine ⟨n, hin, ?_⟩
  rw [denote_bound n tr hnle c (Claim.Below.mono (Nat.le_of_lt hin) hc)]
  exact H (tr.prefix n) hn (Trace.EventLoggedAt_prefix trigger i n tr hin hnle hi)

end DYVis.Theorem
