-- Decoders that name trace entries using the constructor names of the event type.
--
-- The alternative is a per-protocol table mapping events to strings, which is
-- prose: it drifts, and nothing catches it. `eventDecoder%` reads the inductive's
-- constructors instead, so a decoder cannot describe an event as something it is
-- not, and a renamed constructor renames itself in the diagram.
--
-- Which types to decode still has to be listed --- `TraceEntryHas` projects at a
-- KNOWN entry type and the entry sum carries no generic tag, so there is no way
-- to ask "what kind of entry is at index 17". Omitting a type is safe: its
-- entries are counted as `<<n entries>>` rather than dropped.
module

public import DYVis.Trace.Scenario
public import Lean

open Lean Elab Term Meta

namespace DYVis

/-- A `Decoder` for one protocol event type, built from its constructor names.
    `T` must be a fully applied inductive, e.g. `eventDecoder% (DnsEvent SBytes)`. -/
elab "eventDecoder% " t:term:max : term => do
  let ty ← elabType t
  let .const declName _ := (← instantiateMVars ty).getAppFn
    | throwError "eventDecoder%: expected an applied inductive, got{indentExpr ty}"
  let indVal ← getConstInfoInduct declName
  let arms ← indVal.ctors.toArray.mapM fun c =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) .. => $(quote c.toString))
  let stx ← `(fun (tr : DY.ExecTrace) (i : Nat) =>
    (tr.getEventAt $t i).map (fun $arms:matchAlt*))
  elabTerm stx none

end DYVis
