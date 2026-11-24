-- Isolated checks for DYVis behaviour, on its own minimal config.
--
-- NOT imported by `DYVis.lean`: `Check.Config` registers global instances, and a
-- campaign that picked those up alongside its own would have two of each. It
-- builds with the library (`lake build DYVis`) because the lib globs `DYVis.+`.
--
-- The scenarios are deliberately tiny and readable end to end --- as much a demo
-- tour of the mechanisms as a test. Regenerate `DYVis/Check/Basic/` and look at
-- them when changing the renderer.
--
-- Assertions are SEMANTIC, never golden strings. Pinning rendered text makes
-- every intentional change a chore and catches nothing these do not.
module

public import DYVis.Trace
public import DYVis.Trace.Check.Config
import DY.Meta
import DY.Meta.Utils
public meta import DYVis.Trace
public meta import DYVis.Trace.Check.Config
public meta import DY.Trace.Monad

open DY

namespace DYVis.Trace.Check

private def alice : Lane := "alice"
private def bob : Lane := "bob"

instance : ScenarioView where
  decoders := [eventDecoder% DemoEvent]

instance : BytesShape where probes := stdProbes

private def logOf {α : Type} (x : Scenario α) : Log := (x.run Trace.empty).snd

private def texts (l : Log) : List String :=
  l.lines.filterMap fun
    | .note _ t => some t
    | .msg _ _ _ t => some t
    | _ => none

private def deliveriesTo (l : Log) (who : Lane) : Nat :=
  (l.lines.filter fun
    | .msg s d _ _ => s == wire && d == who
    | _ => false).length

private def bars (l : Log) : Nat :=
  (l.lines.filter fun | .activate _ => true | _ => false).length

private def mermaidOf {α : Type} (x : Scenario α) : String := (logOf x).mermaid true

private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-! ## A named send, and a read drawn where it happens -/

private def named : Scenario Unit := do
  format_lanes [alice, wire, bob]
  format_strip ["DYVis.Trace.Check.", "DY."]
  let msg ← step! alice ["a fresh value"] "" (Random.genRand 32)
  let h ← send! "the value, on the wire" msg
  let _ ← step! bob [] "" (Network.receiveMessage h)
  pure ()

-- A named send renders its prose as a comment above the structure.
#guard has (mermaidOf named) "/- the value, on the wire -/"

-- Passing the handle to a later step draws exactly one delivery. A handle that
-- silently stayed a `Nat` would make this 0.
#guard deliveriesTo (logOf named) bob == 1

/-! ## An unnamed send gets no comment

Not an empty one and not a placeholder: the handle and the structure identify the
message on their own. -/

private def unnamedSend : Scenario Unit := do
  format_lanes [alice, wire]
  let v ← step! alice [] "" (Random.genRand 32)
  let _ ← step! alice [] "" (Network.sendMessage v)
  pure ()

#guard !has (mermaidOf unnamedSend) "/-"
#guard has (mermaidOf unnamedSend) "rand:1"

/-! ## Events are named by their constructor -/

private def logsEvent : Scenario Unit := do
  format_lanes [alice, wire, bob]
  format_strip ["DYVis.Trace.Check.", "DY."]
  let v ← step! alice [] "" (Random.genRand 32)
  let _ ← step! bob [] "" (ProtocolEvent.logEvent (DemoEvent.acceptedSomething v))
  pure ()

-- `format_strip` runs at render time, so the stored text is the full name.
#guard (texts (logOf logsEvent)).any (·.endsWith "DemoEvent.acceptedSomething")

/-! ## A step that does nothing opens no bar

So a scenario cannot manufacture a bar for a driver that neither read nor
appended. -/

private def quiet : Scenario Unit := do
  format_lanes [alice, wire]
  let v ← step! alice [] "" (Random.genRand 32)
  let h ← send! "some bytes" v
  let _ ← peek (Network.receiveMessage h.id)
  pure ()

-- Only the `genRand` step; the `peek` adds none.
#guard bars (logOf quiet) == 1

/-! ## Names -/

private def marksFor {α : Type} (x : Scenario α) : Marks := marksOf (logOf x)


private def namedValue : Scenario Unit := do
  format_lanes [alice, wire]
  let v ← step! alice [] "" (Random.genRand 32)
  format_name "the secret" v
  let _ ← send! "first copy" v
  let _ ← send! "second copy" v
  pure ()

-- A name reaches every occurrence, not just the one after the declaration.
#guard (marksFor namedValue).names.length == 2
#guard (marksFor namedValue).problems.isEmpty

private def badNames : Scenario Unit := do
  format_lanes [alice, wire]
  let v ← step! alice [] "" (Random.genRand 32)
  let w ← step! alice [] "" (Random.genRand 32)
  format_name "sent" v
  format_name "also sent" v
  format_name "never sent" w
  let _ ← send! "the value" v
  pure ()

-- First name wins, and both the conflict and the name that reached nothing are
-- reported. A silently-ignored name is the failure mode this rules out.
#guard (marksFor badNames).names.all (·.2 == "sent")
#guard (marksFor badNames).conflicts.length == 1
#guard (marksFor badNames).unmatched == ["never sent"]
#guard (marksFor badNames).problems.length == 2

/-! ## Structure and instance numbers

Rendering is checked as exact unit tests; the traversal is checked on real
`Bytes`. Neither pins a whole diagram. -/

private def lit (s : String) : Bytes := DY.Literal.literalToBytes ⟨s.toUTF8.toList.toArray⟩

private def noNames : Bytes → Option String := fun _ => none

/-- Render from an empty table, which is what a fresh diagram starts with. -/
private def draw (sh : Shape Bytes) : String := (sh.render {}).fst

/-- Render two terms in sequence, as two message lines would be. -/
private def draw2 (a b : Shape Bytes) : String × String :=
  let (x, st) := a.render {}
  let (y, _) := b.render st
  (x, y)

private def cat3 : Bytes :=
  DY.Concat.concat (lit "a") (DY.Concat.concat (lit "b") (lit "c"))

private def shape (b : Bytes) : Shape Bytes :=
  shapeOf (fun _ => false) noNames 6 spineMax b

-- Right-nested concats are one flat list: an n-field message is an n-deep tree
-- that means nothing, and flattening it is the point of the transparency rule.
-- Post-order numbering puts the parts below the whole.
#guard draw (shape cat3) == "concat:4[\"a\":1, \"b\":2, \"c\":3]"

-- Left-nested too, so the flattening is not an artefact of one association.
#guard draw (shape (DY.Concat.concat (DY.Concat.concat (lit "a") (lit "b")) (lit "c")))
  == "concat:4[\"a\":1, \"b\":2, \"c\":3]"

-- Post-order at a wrapper too, not just at a concatenation: the parts are
-- numbered before the term built from them.
#guard draw (.node "h" [.atom "x" (lit "a")] (lit "b")) == "h:2(x:1)"

-- Equal bytes take the same number; different bytes never do.
#guard (draw2 (shape (lit "a")) (shape (lit "a"))) == ("\"a\":1", "\"a\":1")
#guard (draw2 (shape (lit "a")) (shape (lit "b"))) == ("\"a\":1", "\"b\":2")

-- A term prints its structure once. The second sighting is the number alone,
-- which is what keeps a repeated message short.
#guard (draw2 (shape cat3) (shape cat3)).snd == "concat:4"

-- A term already inside an earlier one is not re-expanded either.
#guard (draw2 (shape cat3) (shape (lit "b"))).snd == "\"b\":2"

-- Adjacent copies of the SAME instance collapse.
#guard draw (.cat [.atom "x" (lit "a"), .atom "x" (lit "a"), .atom "y" (lit "b")] (lit "c"))
  == "concat:3[x:1 ×2, y:2]"

-- Same tag, DIFFERENT bytes: distinct numbers, so no collapse. This is what
-- makes `×n` a claim about bytes rather than about text that looks alike.
#guard draw (.cat [.atom "x" (lit "a"), .atom "x" (lit "b")] (lit "c"))
  == "concat:3[x:1, x:2]"

-- Two DIFFERENT non-printable literals render alike, so only the number tells
-- them apart. Without this, a repeated `lit:3` would not mean the same bytes.
#guard (draw2 (shape (lit "\x00")) (shape (lit "\x01"))) == ("lit:1", "lit:2")

-- Non-printable literals carry no size; the number is the only identity.
#guard draw (shape (lit "\x00\x01")) == "lit:1"

-- The spine is not charged to depth: with a depth of 1 a flat concat is still
-- shown whole. Charging it would elide the last field of a wide message for no
-- reason a reader could follow.
#guard draw (shapeOf (fun _ => false) noNames 1 spineMax cat3)
  == "concat:4[\"a\":1, \"b\":2, \"c\":3]"

-- A sub-functor no probe opens is `?`, never flattened through, and still has an
-- identity so two of them can be told apart.
#guard draw (shapeOf (shape := ⟨[]⟩) (fun _ => false) noNames 6 spineMax (lit "a"))
  == "?:1"

-- A named value is not expanded, and takes no number: the name is the identity.
#guard draw (shapeOf (fun _ => false)
  (fun b => if b == lit "b" then some "B" else none) 6 spineMax
  (DY.Concat.concat (lit "a") (lit "b"))) == "concat:2[\"a\":1, ‹B›]"

-- A concat operand the diagram draws elsewhere is kept whole rather than
-- spliced, so it gets a number the later sighting can point back to.
#guard draw (shapeOf (fun b => b == DY.Concat.concat (lit "b") (lit "c"))
  noNames 6 spineMax cat3) == "concat:5[\"a\":1, concat:4[\"b\":2, \"c\":3]]"

/-! ## Line wrapping -/

private def wrapped : Scenario Unit := do
  format_lanes [alice, wire]
  let _ ← send! "" (DY.Concat.concat
    (lit "padding padding padding padding padding padding padding padding")
    (lit "alpha, beta"))
  pure ()

-- Long text breaks at a comma once past the width.
#guard has (mermaidOf wrapped) "<br/>"

-- A comma INSIDE a quoted literal, past the width, is not a break point: one
-- string would otherwise read as two fields. The padding has to sit inside the
-- quotes, or the break lands before them and resets the column.
private def quotedComma : Scenario Unit := do
  format_lanes [alice, wire]
  let _ ← send! "" (lit (String.ofList (List.replicate 85 'x') ++ ", tail"))
  pure ()

#guard has (mermaidOf quotedComma) ", tail\""
#guard !has (mermaidOf quotedComma) "<br/>"

/-! ## Mermaid escaping

`#` introduces an entity code and `;` separates statements, so a label carrying
either swallows the rest of its line. Labels are author text, so this is reachable
without anything in DYVis emitting those characters. -/

private def hashy : Scenario Unit := do
  format_lanes [alice, wire]
  let v ← step! alice [] "" (Random.genRand 32)
  let _ ← send! "a #hash; and more" v
  pure ()

private def hashyOut : String := mermaidOf hashy

#guard has hashyOut "#35;"
#guard has hashyOut "#59;"
#guard !has hashyOut "#hash"
-- The escape's own `;` must not be re-escaped, and the text must survive intact.
#guard has hashyOut "a #35;hash#59; and more"

/-! ## Demo tour -/

#eval named.writeDiagram Trace.empty
  "DYVis/Trace/Check/Basic/01-named-send-and-delivery.md" "DYVis — named send, drawn read"
#eval unnamedSend.writeDiagram Trace.empty
  "DYVis/Trace/Check/Basic/02-unnamed-send.md" "DYVis — an unnamed send"
#eval logsEvent.writeDiagram Trace.empty
  "DYVis/Trace/Check/Basic/03-logged-event.md" "DYVis — an event named by its constructor"
#eval quiet.writeDiagram Trace.empty
  "DYVis/Trace/Check/Basic/04-no-bar.md" "DYVis — a read that opens no bar"
#eval namedValue.writeDiagram Trace.empty
  "DYVis/Trace/Check/Basic/05-repeated-value.md" "DYVis — one value drawn twice"
#eval badNames.writeDiagram Trace.empty
  "DYVis/Trace/Check/Basic/06-name-problems.md" "DYVis — a name conflict and a name that reached nothing"

end DYVis.Trace.Check
