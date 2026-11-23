-- Value identity, derived at render time.
--
-- Two questions a reader of a sequence diagram cannot otherwise answer: is this
-- the same value as that one, and what is it. The first is DERIVED --- `Bytes` has
-- `DecidableEq`, so equality is a fact about the run, not a claim by the author.
-- The second cannot be derived at all, so a name is author commentary and renders
-- marked as such.
--
-- Both are computed here rather than recorded while the scenario runs, because a
-- name has to apply to the whole diagram: otherwise the same bytes would render
-- differently before and after the declaration that names them.
module

public import DYVis.Trace.Scenario
public import DY.Actions.Network

namespace DYVis

open DY

/-- What the identity pass derived, keyed by trace handle. -/
public structure Marks where
  /-- Author-assigned names, resolved from byte values to the handles carrying them. -/
  names : List (Nat × String) := []
  /-- Declared names that matched no drawn message. -/
  unmatched : List String := []
  /-- Values given more than one name. -/
  conflicts : List String := []

section

variable [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has Network.ExecEntryT]

/-- The values the diagram draws, by handle, in first-appearance order.

    Keyed by HANDLE, so a send and its delivery are one occurrence. Counting drawn
    arrows instead would tag every ordinary send/delivery pair as a repetition,
    which is noise and would discredit the marker entirely. -/
private def drawnValues (s : Log) : List (Nat × Bytes) :=
  s.lines.reverse.foldl
    (fun acc l =>
      match l with
      | .msg _ _ (some i) _ =>
          if acc.any (fun p => p.1 == i) then acc
          else match s.tr.getMessageSentAt i with
            | some b => acc ++ [(i, b)]
            | none => acc
      | _ => acc)
    []

/-- Distinct byte values with the handles carrying them, in first-occurrence order. -/
private def groupByValue (vs : List (Nat × Bytes)) : List (Bytes × List Nat) :=
  vs.foldl
    (fun gs (v : Nat × Bytes) =>
      if gs.any (fun g => g.1 == v.2)
      then gs.map (fun g => if g.1 == v.2 then (g.1, g.2 ++ [v.1]) else g)
      else gs ++ [(v.2, [v.1])])
    []

/-- Resolve declared names onto handles. First name wins on conflict: two names for
    one value is a scenario bug, and silently picking one would hide it. -/
private def nameMarks (decls : List (Bytes × String)) (groups : List (Bytes × List Nat)) :
    List (Nat × String) × List String × List String :=
  let (kept, conflicts) := decls.foldl
    (fun (acc : List (Bytes × String) × List String) (d : Bytes × String) =>
      match acc.1.find? (fun k => k.1 == d.1) with
      | some k => if k.2 == d.2 then acc
                  else (acc.1, acc.2 ++ [s!"{d.2} / {k.2}"])
      | none => (acc.1 ++ [d], acc.2))
    ([], [])
  let marks := groups.flatMap (fun g =>
    match kept.find? (fun k => k.1 == g.1) with
    | some k => g.2.map (fun i => (i, k.2))
    | none => [])
  let unmatched := (kept.filter (fun k => !groups.any (fun g => g.1 == k.1))).map (·.2)
  (marks, conflicts, unmatched)

public def marksOf (s : Log) : Marks :=
  let groups := groupByValue (drawnValues s)
  let (names, conflicts, unmatched) := nameMarks s.names groups
  { names, unmatched, conflicts }

end

/-- What the author called the value at a handle, as a prefix. -/
public def Marks.at (m : Marks) (i : Nat) : String :=
  match m.names.find? (fun p => p.1 == i) with
  | some p => s!"‹{p.2}› "
  | none => ""

/-- Scenario bugs the identity pass found. Rendered in the diagram, not returned:
    a name that reached nothing has to be as visible as one that worked. -/
public def Marks.problems (m : Marks) : List String :=
  m.conflicts.map (fun c => s!"«two names for one value: {c}»")
  ++ m.unmatched.map (fun n => s!"«name ‹{n}› matched no drawn message»")

end DYVis
