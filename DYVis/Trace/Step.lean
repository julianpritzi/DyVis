-- Step names and read-sets taken from the code rather than from prose and lists.
--
-- Two things a scenario should not be trusted to state are derived here from the
-- call itself:
--
-- * the step's NAME, read off the head constant and resolved by the elaborator,
--   so it cannot drift from the definition being called;
-- * the step's READS, read off the argument TYPES. Every `Handle` argument is a
--   wire message the driver is about to consume, so the delivery arrows are the
--   handles actually passed. There is no list to forget and none to pad.
--
-- Prose stays available, and renders as a comment above the name.
module

public import DYVis.Trace.Scenario
public import Lean

open Lean Elab Term Meta

namespace DYVis

/-- Look through parentheses. -/
meta def unparen : Nat → Syntax → Syntax
  | 0, stx => stx
  | fuel + 1, stx =>
    match stx with
    | .node _ k args =>
        if k == ``Lean.Parser.Term.paren then unparen fuel (args[1]?.getD stx) else stx
    | _ => stx

/-- The head identifier of an application. Fuel rather than `partial`: nesting is
    bounded by the source. -/
meta def headIdent? : Nat → Syntax → Option Syntax
  | 0, _ => none
  | fuel + 1, stx =>
    let stx := unparen fuel stx
    if stx.isIdent then some stx
    else match stx with
      | .node _ k args =>
          if k == ``Lean.Parser.Term.app then args[0]?.bind (headIdent? fuel) else none
      | _ => none

/-- Is this argument a `Handle` in the current context? Elaborated only to read
    its type; anything that will not elaborate on its own is left alone. -/
meta def isHandleArg (a : Syntax) : TermElabM Bool := do
  try
    let e ← elabTerm a none
    let t ← whnf (← instantiateMVars (← inferType e))
    return t.isConstOf ``Handle
  catch _ => return false

/-- The step's name, the handles it reads, and the call with those handles
    replaced by the `Nat` the driver expects. -/
meta def analyze (act : Term) : TermElabM (String × Array Term × Term) := do
  let raw := unparen 8 act.raw
  let nm ←
    match headIdent? 64 raw with
    | some id =>
        try pure (← realizeGlobalConstNoOverloadWithInfo id).toString
        catch _ => pure id.getId.toString
    | none => pure "(anonymous)"
  if raw.getKind != ``Lean.Parser.Term.app then
    return (nm, #[], act)
  let fn : Term := ⟨raw[0]⟩
  let mut ids : Array Term := #[]
  let mut newArgs : Array Term := #[]
  for a in raw[1].getArgs do
    let aT : Term := ⟨a⟩
    if ← isHandleArg a then
      let idStx ← `(Handle.id $aT)
      ids := ids.push idStx
      newArgs := newArgs.push idStx
    else
      newArgs := newArgs.push aT
  return (nm, ids, ← `($fn $newArgs*))

meta def stepLabel (nm : String) (prose : TSyntax `str) : TermElabM Term :=
  if prose.getString.isEmpty then `($(quote nm))
  else `("/- " ++ $prose ++ " -/<br/>" ++ $(quote nm))

/-- A function marking every `Nat` in a driver's result as a `Handle`, or `none`
    if there is nothing to mark. Built here rather than by a typeclass so the
    step's result type stays concrete: a class with a type field would leave every
    result as a projection and break field notation on it. -/
meta def wrapperFor : Nat → Expr → TermElabM (Option Term)
  | 0, _ => return none
  | fuel + 1, ty => do
    if ty.isConstOf ``Nat then
      return some (← `(Handle.mk))
    else if ty.isAppOfArity ``Prod 2 then
      let args := ty.getAppArgs
      let wa ← wrapperFor fuel args[0]!
      let wb ← wrapperFor fuel args[1]!
      match wa, wb with
      | none, none => return none
      | _, _ =>
        let fa ← match wa with | some f => pure f | none => `(id)
        let fb ← match wb with | some f => pure f | none => `(id)
        return some (← `(fun p => ($fa p.1, $fb p.2)))
    else return none

/-- `step! lane [names for what it sends] "prose" (driver …)`.

    All four are required. `[]` and `""` say "nothing to add" explicitly, which
    costs a reviewer nothing and keeps the parser unambiguous --- with optional
    parts, a bracketed list and a parenthesised call are both terms, and the
    wrong one gets picked silently. -/
elab "step! " who:term:max outs:term:max prose:str act:term:max : term => do
  let (nm, ids, act') ← analyze act
  let lbl ← stepLabel nm prose
  let core ← `(stepIO $who $lbl [$ids,*] $outs $act')
  -- `Traceful` is a `def`, so the type is read unreduced to keep its head.
  let ty ← instantiateMVars (← inferType (← elabTerm act' none))
  let w ← if ty.getAppFn.isConstOf ``DY.Traceful then
      match ty.getAppArgs.back? with
      | some r => wrapperFor 8 r
      | none => pure none
    else pure none
  let stx ← match w with
    | some f => `($f <$> $core)
    | none => pure core
  elabTerm stx none

/-- `send! "name" bytes` --- the same as `send`, spelled to match `step!`. -/
macro "send! " text:str b:term : term => `(send $text $b)

end DYVis
