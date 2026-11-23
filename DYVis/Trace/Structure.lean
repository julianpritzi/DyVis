-- Message structure, derived from the byte algebra.
--
-- A label like "DS RRset for child" asserts something the model does not support:
-- `WireFormat` has round-trip laws WITHIN a type and no disjointness law ACROSS
-- types, so nothing says two message types encode to disjoint byte sets. An
-- earlier renderer that guessed types by trying `parseAs` in turn had `RrsigMeta`
-- and `DnskeyRdata` at the same serialized width, and every RRSIG rendered as a
-- DNSKEY until the attempts were hand-ordered. That was the model saying the two
-- are indistinguishable and the renderer overriding it.
--
-- `Bytes.view?` is a different thing entirely. It projects the byte ALGEBRA, whose
-- sub-functors really are disjoint --- that is what `BytesView.view_pack_ne`
-- states --- so a term packed at one sub-functor never views as another, and the
-- order probes are tried in cannot change the answer.
--
-- So what is derived here is SHAPE, never type. Structure can say
-- `[name, ds, [hash(k)]]`; it can never say "this is a DS RRset", and that is the
-- point rather than a defect. It also surfaces indistinguishability instead of
-- hiding it: if two message types render alike, the reader sees that.
-- Only the three sub-functors every byte algebra has are probed here. DY's own
-- `Hash` / `Sign` / `DiffieHellman` equational theories are deliberately NOT
-- imported: `Crypto` ships replacements for them that collide on names like
-- `DY.Bytes.dhSkLabel`, so importing both is an error, and every campaign in this
-- repo uses the `Crypto` ones. Their probes live in `Crypto/DYVis.lean`.
module

public import DYVis.Trace.Scenario
public import Std.Data.TreeMap
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.Actions.Random

namespace DYVis

open DY

/-- What one probe recognised: a leaf, an opaque wrapper, or a concatenation.

    `concat` is separate because it is the one TRANSPARENT constructor.
    Serialization builds right-nested concats, so an n-field message is an n-deep
    tree that means nothing; flattening it is the main verbosity win. -/
public inductive Frame (β : Type) where
  | atom (tag : String)
  | wrap (tag : String) (args : List β)
  | concat (lhs rhs : β)

/-- Recognise one byte sub-functor, or decline.

    Probes may be tried in any order: `view?` projects the byte algebra, whose
    sub-functors are disjoint, so at most one can ever answer. -/
public abbrev Probe [BytesFunctor] := Bytes → Option (Frame Bytes)

/-- The sub-functors a campaign's diagrams look inside.

    Assembled by the campaign rather than found by instance search, because a
    probe needs `BytesFunctor.Has` for its sub-functor and no campaign has them
    all. A sub-functor left out of the list renders `?`, opaque --- ugly and
    obviously incomplete, which is the right failure direction. The risk worth
    guarding against is not a shown wrapper being misread (nobody sees `hash(x)`
    and concludes `x` is public) but the renderer flattening THROUGH something it
    should not and presenting `x` at top level, looking like a field sent in the
    clear. -/
public class BytesShape [BytesFunctor] where
  probes : List Probe

public instance (priority := low) emptyShape [BytesFunctor] : BytesShape := ⟨[]⟩

/-- A term as far as the probes could see it. `β` is the value each node came
    from, kept so the renderer can tell two identical-looking terms apart and
    print each one's structure only once. -/
public inductive Shape (β : Type) where
  /-- No probe claimed this term. -/
  | opaque (key : β)
  /-- A leaf a probe named. -/
  | atom (tag : String) (key : β)
  /-- An opaque constructor, shown as a wrapper. -/
  | node (tag : String) (args : List (Shape β)) (key : β)
  /-- A flattened concatenation. -/
  | cat (parts : List (Shape β)) (key : β)
  /-- A value the author named, deliberately not expanded. -/
  | named (n : String)
  /-- The depth limit cut here. Carries no key: it was never printed whole, so
      there is nothing for a later reference to point back to. -/
  | elided

section

variable [BytesFunctor]

/-- Printable literals are usually protocol tags, and reading `"dnskey"` beats
    reading anything else. Everything else is just `lit`: its byte length says
    nothing a reader can use, and identity is supplied later by `instanceIds`. -/
private def literalTag (lit : ByteArray) : String :=
  if lit.toList.all (fun c => c.toNat ≥ 32 && c.toNat ≤ 126) && !lit.isEmpty then
    "\"" ++ String.ofList (lit.toList.map (fun c => Char.ofNat c.toNat)) ++ "\""
  else "lit"

public def literalProbe [BytesFunctor.Has Literal.Literal.SubF] : Probe := fun b =>
  (b.view? Literal.Literal.SubF).map fun x => .atom (literalTag x.lit)

/-- No trace handle: the instance number already says which random this is, and
    two numbers on one leaf would be two answers to the same question. -/
public def randomProbe [BytesFunctor.Has Random.SubF] : Probe := fun b =>
  (b.view? Random.SubF).map fun _ => .atom "rand"

public def concatProbe [BytesFunctor.Has Concat.Concat.SubF] : Probe := fun b =>
  (b.view? Concat.Concat.SubF).map fun x => .concat x.lhs x.rhs

/-- The sub-functors every campaign has. Campaigns append their own. -/
public def stdProbes
    [BytesFunctor.Has Literal.Literal.SubF] [BytesFunctor.Has Random.SubF]
    [BytesFunctor.Has Concat.Concat.SubF] : List Probe :=
  [literalProbe, randomProbe, concatProbe]

/-- Flatten a concat operand, unless it is itself a value the diagram draws
    somewhere else.

    Splicing loses the operand's KEY, so the node never gets an instance number
    and a later sighting of the same bytes looks unrelated. That is exactly the
    DNSSEC case: the RRset a signature covers is the right operand of the signed
    form, and it is also a message on the wire. Keeping it whole is what makes the
    two render as one number. -/
private def partsOf (keep : Bytes → Bool) (b : Bytes) :
    Shape Bytes → List (Shape Bytes)
  | .cat ps k => if keep b then [Shape.cat ps k] else ps
  | s => [s]

/-- How long a flattened concatenation may get. Separate from `depth` because the
    concat spine is not nesting the reader can see: a 10-field message is a
    10-deep right-nested tree, and charging it to `depth` would render the first
    field in full and elide the last for no reason a reader could follow. -/
public def spineMax : Nat := 160

/-- `depth` is the termination measure and the elision limit; a TLS record's term
    contains the whole transcript, so there has to be one. `spine` bounds a single
    flattened concatenation, which costs no depth, so every field of a message is
    shown to the SAME depth rather than degrading left to right. -/
public def shapeOf [shape : BytesShape] (keep : Bytes → Bool)
    (named : Bytes → Option String)
    (depth spine : Nat) (b : Bytes) : Shape Bytes :=
  match depth, spine with
  | 0, _ => .elided
  | _, 0 => .elided
  | d + 1, s + 1 =>
    match named b with
    | some n => .named n
    | none =>
      match BytesShape.probes.findSome? (fun p => p b) with
      | none => .opaque b
      | some (Frame.atom t) => .atom t b
      | some (Frame.wrap t args) =>
          .node t (args.map (shapeOf keep named d spineMax)) b
      | some (Frame.concat lhs rhs) =>
          .cat (partsOf keep lhs (shapeOf keep named (d + 1) s lhs)
             ++ partsOf keep rhs (shapeOf keep named (d + 1) s rhs)) b
termination_by (depth, spine)

end

/-- Values already printed in full, and the number given to each.

    A number is handed out at the moment a term is first printed WHOLE, so every
    number has exactly one expansion, earlier in the diagram. That is also what
    keeps a depth-cut term from claiming a number it never explains. -/
public structure Insts (β : Type) [Ord β] where
  seen : Std.TreeMap β Nat := Std.TreeMap.empty
  next : Nat := 1

private def Insts.mark [Ord β] (st : Insts β) (k : β) : Insts β :=
  { seen := st.seen.insert k st.next, next := st.next + 1 }

/-- Collapse adjacent identical parts. Sound in a way the earlier version was
    not: a rendering now carries the term's instance number, so equal strings mean
    equal BYTES rather than merely text that happens to look alike. -/
private def collapse : List String → List String
  | [] => []
  | x :: xs =>
    let n := (xs.takeWhile (· == x)).length
    (if n == 0 then x else s!"{x} ×{n + 1}") :: collapse (xs.drop n)
termination_by l => l.length
decreasing_by simp_wf; omega

mutual

/-- Print a term, expanding it only the first time it is seen.

    Numbering is post-order --- sub-terms are numbered before the term containing
    them --- so a composite always outranks its parts. That is what makes the data
    flow readable: in any message, numbers below the previous high-water mark came
    from somewhere earlier and the contiguous block above it was built here. -/
public def Shape.render [Ord β] (st : Insts β) : Shape β → String × Insts β
  | .elided => ("…", st)
  | .named n => (s!"‹{n}›", st)
  | .atom t k =>
      match st.seen.get? k with
      | some i => (s!"{t}:{i}", st)
      | none => (s!"{t}:{st.next}", st.mark k)
  | .opaque k =>
      match st.seen.get? k with
      | some i => (s!"?:{i}", st)
      | none => (s!"?:{st.next}", st.mark k)
  | .node t args k =>
      match st.seen.get? k with
      | some i => (s!"{t}:{i}", st)
      | none =>
        let (ss, st) := Shape.renderAll st args
        (s!"{t}:{st.next}(" ++ String.intercalate ", " ss ++ ")", st.mark k)
  | .cat ps k =>
      match st.seen.get? k with
      | some i => (s!"concat:{i}", st)
      | none =>
        let (ss, st) := Shape.renderAll st ps
        (s!"concat:{st.next}[" ++ String.intercalate ", " (collapse ss) ++ "]", st.mark k)

public def Shape.renderAll [Ord β] (st : Insts β) :
    List (Shape β) → List String × Insts β
  | [] => ([], st)
  | s :: rest =>
      let (x, st) := Shape.render st s
      let (xs, st) := Shape.renderAll st rest
      (x :: xs, st)

end

/-- Whether anything was seen at all. A message the probes cannot open renders as
    a bare `?`, which is worth suppressing in favour of the author's prose. -/
public def Shape.isOpaque : Shape β → Bool
  | .opaque _ => true
  | _ => false

end DYVis
