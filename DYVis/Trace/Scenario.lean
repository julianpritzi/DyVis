-- A trace builder that draws while it runs.
--
-- A DY execution trace records WHAT happened. It does not record who did it: a
-- `Network.ExecEntryT` carries a `msg` and no sender, because in a Dolev-Yao model
-- every message is public and anybody may have placed it. Recovering attribution
-- afterwards means guessing from content, which is brittle and is itself a pile of
-- code a reviewer has to audit before trusting the picture.
--
-- So attribution is taken where it is not in doubt: the call site. A scenario is
-- an ordinary `Traceful` run in which each step also says who is acting. The
-- drivers, the byte algebra and the trace are untouched --- `Scenario` only
-- carries a drawing alongside.
--
-- ## What is declared and what is derived
--
-- Only the lane and the label are declared. Whether the step ran at all, and how
-- many trace entries it appended, come from the trace itself, so a stale label can
-- mis-NAME a step but cannot invent one. A step whose action fails is drawn as
-- REJECTED, which is why the runs that are supposed to abort still produce a
-- diagram.
--
-- ## Failure keeps the drawing
--
-- `Traceful`'s bind drops the value on failure but keeps the trace. `Scenario`
-- does the same for the drawing, which is why it is defined directly rather than
-- as `StateT _ Traceful`: a `StateT` would discard every line accumulated before
-- an intended abort.
module

public import DY.Trace
public import DY.Actions.Network

namespace DYVis

open DY

/-- A column in the diagram: a participant, or the wire. -/
public abbrev Lane := String

/-- The public network. Every message has it at one end. -/
public def wire : Lane := "wire"

/-- One drawn line. `note` is local to a participant; `msg` travelled.

    A `msg` carries the trace handle of the entry it refers to, which DYVis takes
    from the action itself. The scenario supplies only the text, so a reader can
    match a delivery to its send on the bracketed id without trusting either
    label. `none` means there is no handle to name --- a send the trace refused,
    or a line the renderer has already folded the handle into. -/
public inductive Line where
  /-- Something a participant did on its own. -/
  | note (lane : Lane) (text : String)
  /-- Bytes moving between lanes. -/
  | msg (src dst : Lane) (id : Option Nat) (text : String)
  /-- One participant starts executing. A step is local to a single lane, so the
      bracket is on that lane's lifeline rather than across the diagram. -/
  | activate (lane : Lane)
  /-- That participant stops executing. -/
  | deactivate (lane : Lane)

/-- A wire handle.

    Opaque on purpose. `Network.receiveMessage` reads with `getEntry`, which
    appends nothing, so a read leaves NO evidence in the trace and cannot be
    derived from it. What can be derived is the type: a driver wants a `Nat`, the
    only route to one is `.id`, and the step macros insert that themselves while
    recording the read. Omitting a read therefore stops being possible rather
    than being merely discouraged. -/
public structure Handle where
  /-- The trace index the message was appended at. -/
  id : Nat

/-- The run's state: the real trace, plus the drawing being built beside it.
    `lines` and `lanes` are kept reversed and in first-appearance order. -/
public structure Log [BytesFunctor] [ExecTraceTypes] where
  /-- The execution trace the drivers actually produced. -/
  tr : ExecTrace
  /-- Drawn lines, most recent first. -/
  lines : List Line := []
  /-- Lanes in order of first use. -/
  lanes : List Lane := []
  /-- Name prefixes to drop when rendering. Presentation only. -/
  strip : List String := []
  /-- What each sent message was called, by handle, so a later consumer can be
      drawn receiving it under the name the sender gave it. -/
  labels : List (Nat × String) := []
  /-- Author-assigned names for byte values, in declaration order. Resolved to
      handles at render time by byte equality, so a name reaches every occurrence
      of the value and not just the one in front of the declaration. -/
  names : List (Bytes × String) := []

@[expose]
public def Scenario [BytesFunctor] [ExecTraceTypes] (α : Type) := Log → Option α × Log

section

variable [BytesFunctor] [ExecTraceTypes]

public instance : Monad Scenario where
  pure x := fun s => (some x, s)
  bind x f := fun s =>
    match x s with
    | (none, s') => (none, s')
    | (some a, s') => f a s'

public instance : Alternative Scenario where
  failure := fun s => (none, s)
  orElse x y := fun s =>
    match x s with
    | (some a, s') => (some a, s')
    | (none, s') => y () s'

/-- `Err` never touches the trace, so lifting it needs no accounting. There is
    deliberately NO lift from `Traceful`: an action that can append entries has to
    go through `step!`, `send!` or `peek`, which is what keeps every entry either
    displayed or counted. -/
public instance : MonadLift Err Scenario where
  monadLift x := fun s => (x, s)

private def touch (l : Lane) (s : Log) : Log :=
  if s.lanes.contains l then s else { s with lanes := s.lanes ++ [l] }

private def push (l : Line) (s : Log) : Log := { s with lines := l :: s.lines }

/-- No label is the empty string, not a placeholder: the handle and the term's
    structure identify a message on their own, so an unnamed one needs no prose. -/
private def labelOf (s : Log) (h : Nat) : String :=
  match s.labels.find? (fun p => p.1 == h) with
  | some p => p.2
  | none => ""

/-- Names the entry at one trace index, or declines. -/
public abbrev Decoder := ExecTrace → Nat → Option String

/-- The entry kinds a campaign's diagrams name. Decoders are tried in order and
    the first to answer wins; anything none of them claims is COUNTED rather than
    dropped, so choosing not to decode something shows up as `«n entries»` and
    never as silence. -/
public class ScenarioView where
  /-- Built with `eventDecoder%`, which reads the constructor names off the
      inductive rather than taking them as prose. -/
  decoders : List Decoder

/-- Campaigns that name nothing still get message arrows and entry counts. -/
public instance (priority := low) emptyView : ScenarioView := ⟨[]⟩

/-- Run a driver that only READS --- a directory or state lookup, which appends
    nothing. If it does append, the entries are counted as unattributed rather
    than vanishing, so `peek` cannot be used to slip entries past the drawing. -/
public def peek (x : Traceful α) : Scenario α := fun s =>
  let before := s.tr.length
  let (a, tr') := x.run s.tr
  let s := { s with tr := tr'.val }
  let n := tr'.val.length - before
  (a, if n == 0 then s
      else push (.note wire s!"«{n} unattributed»") (touch wire s))

/-- Fix the left-to-right order of the diagram's lanes. Any lane not named here is
    appended when it is first used, so this is an ordering hint and not a
    declaration --- a lane the run touches always appears. -/
public def format_lanes (ls : List Lane) : Scenario Unit := fun s =>
  (some (), ls.foldl (fun s l => touch l s) s)

/-- Drop these substrings from step names when rendering. Derived names are fully
    qualified, and a campaign's steps come from several unrelated namespaces
    (`Protocols.…`, `DY.…`), so there is no common prefix to strip automatically.
    Presentation only: it cannot change which definition was called. -/
public def format_strip (ps : List String) : Scenario Unit := fun s =>
  (some (), { s with strip := s.strip ++ ps })

/-- Give a byte value a name, used wherever those exact bytes are drawn.

    Only the name is declared; the EQUALITY is derived, so a badly chosen name
    still correctly identifies where the same bytes recur. It renders marked as
    author-assigned for exactly that reason.

    Declaration order does not matter --- a name applies to the whole diagram,
    like `format_strip`, or the same bytes would render differently before and
    after the declaration. A name matching no drawn message is reported rather
    than silently ignored. -/
public def format_name (n : String) (b : Bytes) : Scenario Unit := fun s =>
  (some (), { s with names := s.names ++ [(b, n)] })

/-- A local observation, drawn in `who`'s lane. Touches neither the trace nor the
    protocol. -/
public def note (who : Lane) (text : String) : Scenario Unit := fun s =>
  (some (), push (.note who text) (touch who s))

public def Scenario.run (x : Scenario α) (tr : ExecTrace) : Option α × Log :=
  x { tr }

/-- The trace a scenario produced, for the `#guard`s to scan. -/
public def Scenario.trace (x : Scenario α) (tr : ExecTrace) : ExecTrace :=
  (x.run tr).snd.tr

end

section

variable [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has Network.ExecEntryT]

/-- Put bytes on the wire outside any step.
    Both ends are the wire, because nobody was seen to send them: no driver ran,
    and `Network.ExecEntryT` records no sender. Bytes staged this way are the
    inputs a run hands to the participants --- assembled by the environment, or by
    an attacker, or provisioned out of band --- and the model does not tell them
    apart. What it does say is that they became public.

    The handle is the real one, so the value is usable exactly as
    `Network.sendMessage`'s. -/
public def send (text : String) (b : Bytes) : Scenario Handle := fun s =>
  let (h, tr') := (Network.sendMessage b).run s.tr
  let s := push (.msg wire wire h text) (touch wire { s with tr := tr'.val })
  (h.map Handle.mk, match h with
      | some n => { s with labels := (n, text) :: s.labels }
      | none => s)

/-- Read bytes off the wire, and draw who read them. For a read the scenario needs
    the VALUE of rather than just the effect --- an attacker unpacking compromised
    state, say. The label is not the caller's to choose: it is the one the sender
    registered for this handle, so a receive cannot describe the bytes as
    something other than what was sent. -/
public def recv (dst : Lane) (h : Handle) : Scenario Bytes := fun s =>
  let (b, tr') := (Network.receiveMessage h.id).run s.tr
  (b, push (.msg wire dst (some h.id) (labelOf s h.id))
        (touch wire (touch dst { s with tr := tr'.val })))

/-- Mark where a bar starts, since Mermaid draws no gap between one activation and
    the next on the same lane. The marker goes on the name, so a prose comment
    rendered above it keeps reading like the call site. -/
private def markStart (t : String) : String :=
  match (t.splitOn "<br/>").reverse with
  | last :: revInit => String.intercalate "<br/>" (revInit.reverse ++ ["▸ " ++ last])
  | [] => "▸ " ++ t

/-- What a step left at one trace index. -/
private inductive Item where
  | send (idx : Nat)
  | event (idx : Nat) (name : String)
  | other

private def scanFrom [ScenarioView] (tr : ExecTrace) (i fuel : Nat) : List Item :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let rest := scanFrom tr (i + 1) fuel
    match tr.getMessageSentAt i with
    | some _ => .send i :: rest
    | none =>
      match ScenarioView.decoders.findSome? (fun d => d tr i) with
      | some n => .event i n :: rest
      | none => .other :: rest

private def flushOther (who : Lane) (n : Nat) (s : Log) : Log :=
  if n == 0 then s
  else if n == 1 then push (.note who "«1 entry»") s
  else push (.note who s!"«{n} entries»") s

/-- Run `x` as a step by `who`, and draw it as an activation bar covering the
    messages it read, the step, and everything it left on the trace.

    Only the lane and the labels are declared. Everything else is read off the
    trace: whether the step ran, every message it put on the wire --- including
    ones sent deep inside a driver that the caller never sees a handle for --- and
    every entry it appended. Entries no `ScenarioView` decoder claims are counted,
    so the displayed items and the counts together account for the whole range.
    `outs` names the sends in order; unnamed ones still get an arrow.

    A step is local to one participant, so the bracket is on that lane rather than
    across the diagram. A step that neither reads nor appends gets no bar. -/
public def stepIO [ScenarioView] (who : Lane) (what : String) (inputs : List Nat)
    (outs : List String) (x : Traceful α) : Scenario α := fun s =>
  let before := s.tr.length
  let (a, tr') := x.run s.tr
  let after := tr'.val.length
  let s := touch who { s with tr := tr'.val }
  let items := scanFrom s.tr before (after - before)
  let usesWire :=
    !inputs.isEmpty || items.any (fun i => match i with | .send _ => true | _ => false)
  let active := !inputs.isEmpty || !items.isEmpty
  let s := if active then push (.activate who) (if usesWire then touch wire s else s) else s
  -- A handle whose index is not a network entry is local state, not a message:
  -- drivers hand those back as `Nat` too, and there is nothing to deliver.
  let s := inputs.foldl
    (fun s h =>
      if (s.tr.getMessageSentAt h).isSome then
        push (.msg wire who (some h) (labelOf s h)) s
      else s)
    s
  let text := match a with
    | none => s!"{what} — REJECTED"
    | some _ => what
  let s := push (.note who (if active then markStart text else text)) s
  let (s, _, pending) := items.foldl
    (fun (acc : Log × Nat × Nat) it =>
      let (s, k, pending) := acc
      match it with
      | .other => (s, k, pending + 1)
      | .send idx =>
          let s := flushOther who pending s
          let t := outs[k]?.getD (labelOf s idx)
          (push (.msg who wire (some idx) t) { s with labels := (idx, t) :: s.labels },
            k + 1, 0)
      | .event _ n => (push (.note who ("· " ++ n)) (flushOther who pending s), k, 0))
    (s, 0, 0)
  let s := flushOther who pending s
  (a, if active then push (.deactivate who) s else s)

private def sendsIn (tr : ExecTrace) (i fuel : Nat) (acc : List Handle) : List Handle :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
    sendsIn tr (i + 1) fuel (if (tr.getMessageSentAt i).isSome then ⟨i⟩ :: acc else acc)

/-- Run `x` and also return the wire handles it appended, in trace order.

    For drivers that send a message but hand back something else --- an exported
    secret, or only the last of several records --- so a follow-on driver can be
    given the messages the first one actually put on the wire instead of a guessed
    index. Read off the trace, so it finds sends made deep inside a driver too. -/
public def withSends (x : Scenario α) : Scenario (α × List Handle) := fun s =>
  let before := s.tr.length
  match x s with
  | (none, s') => (none, s')
  | (some a, s') => (some (a, sendsIn s'.tr before (s'.tr.length - before) []), s')

end

end DYVis
