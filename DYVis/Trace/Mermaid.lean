-- Mermaid emission. Nothing here decides anything: it prints the lines the
-- scenario already recorded, in the order it recorded them.
module

public import DYVis.Trace.Scenario
public import DYVis.Trace.Identity
public import DYVis.Trace.Structure

namespace DYVis

open DY

/-- Mermaid reads `#` as the start of an entity code (`#35;`, `#quot;`) and accepts
    `;` as a statement separator, so both have to be escaped or the rest of the
    line is swallowed. Done in one character pass: escaping `#` first would then
    have its own `;` re-escaped, and escaping `;` first would leave the `;` that
    `#35;` introduces. -/
private def clean (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '#' => "#35;"
      | ';' => "#59;"
      | '\n' => " "
      | c => c.toString)) ""

/-- Break a long message at the first `, ` past this many characters. Crude, but a
    term's arguments are exactly where a break reads naturally. -/
private def width : Nat := 60

/-- Never inside a quoted literal: `"TLS 1.3, server CertificateVerify"` carries a
    comma, and breaking there would read as two fields rather than one string. -/
private def wrapFrom : Nat → Bool → List Char → List Char
  | _, _, [] => []
  | col, false, ',' :: ' ' :: cs =>
      if col ≥ width then ',' :: "<br/>".toList ++ wrapFrom 0 false cs
      else ',' :: ' ' :: wrapFrom (col + 2) false cs
  | col, q, c :: cs => c :: wrapFrom (col + 1) (if c == '"' then !q else q) cs

/-- Segments already separated by `<br/>` are wrapped independently, so a prose
    comment above a term does not count toward the term's own line length. -/
private def wrap (s : String) : String :=
  String.intercalate "<br/>"
    ((s.splitOn "<br/>").map (fun seg => String.ofList (wrapFrom 0 false seg.toList)))

/-- The handle is folded into the message text by `msgLabel`, which has to put the
    author's prose above it, so nothing here needs the marks. -/
private def body : Line → String
  | .note l t => s!"Note over {l}: {clean t}"
  | .msg s d _ t => s!"{s}->>{d}: {clean (wrap t)}"
  | .activate l => s!"activate {l}"
  | .deactivate l => s!"deactivate {l}"

/-- Activations never nest: a step wraps a `Traceful`, which knows nothing of
    them, so each one covers a disjoint interval of the trace. Hence one flag,
    not a depth. The indentation is for whoever reads the Markdown source;
    Mermaid ignores it, as it does the blank line closing each bar. -/
private def renderFrom : Bool → List Line → List String
  | _, [] => []
  | _, .activate l :: rest => ("  " ++ body (.activate l)) :: renderFrom true rest
  | _, .deactivate l :: rest =>
      ("  " ++ body (.deactivate l)) :: "" :: renderFrom false rest
  | active, l :: rest =>
      ((if active then "    " else "  ") ++ body l) :: renderFrom active rest

/-- The wire is not a principal: it is the public medium every message passes
    through, so it is drawn with Mermaid's `queue` stereotype rather than as
    another participant. -/
private def participantLine (l : Lane) : String :=
  if l == wire then "  participant " ++ l ++ "@{ \"type\" : \"queue\" }"
  else "  participant " ++ l

private def stripAll (ps : List String) (s : String) : String :=
  ps.foldl (fun acc p => acc.replace p "") s

section

variable [BytesFunctor] [ExecTraceTypes] [ExecTraceTypes.Has Network.ExecEntryT]

/-- How deep a term is shown before eliding. A TLS record's term contains the
    whole transcript, so there has to be a limit. A concatenation costs no depth
    (`spineMax` bounds that separately), so every field of a message is shown to
    this same depth. -/
private def depth : Nat := 6

/-- The values the diagram draws as messages.

    A concat operand that is one of them is kept whole rather than flattened
    away, so it gets an instance number here and the later sighting renders as
    that same number. Only CONCAT nodes are preserved, and only on exact byte
    equality, so a stray literal that happens to sit inside everything cannot
    trigger it.

    Membership goes through a `TreeSet` rather than a scan of the sent list. The
    predicate is the same one -- `Ord Bytes` is `LawfulEqOrd`, so set membership
    and `List.any (· == ·)` decide the same terms -- but the scan compared the
    candidate against EVERY sent message, structurally, and it is asked once per
    sub-term of every message drawn. That is quadratic in trace length with a
    whole-term comparison as its constant, which is what made a long scenario's
    diagram cost minutes rather than seconds. -/
private def keepDrawn (s : Log) : Bytes → Bool :=
  let sent : Std.TreeSet Bytes :=
    ((List.range s.tr.length).filterMap (fun j => s.tr.getMessageSentAt j)).foldl
      (fun acc v => acc.insert v) Std.TreeSet.empty
  fun v => sent.contains v

/-- The text of one message arrow, and the instance table after it.

    Without `detail` the author's prose is the whole label: the overview answers
    who sent what to whom, and the handle is enough to find the term below. With
    it, the structure takes the trusted position and the prose is demoted to a
    `/- … -/` comment above it, matching how steps already read. Where the probes
    cannot open the term there is nothing derived to show either way. -/
private def msgLabel [BytesShape] (detail : Bool) (keep : Bytes → Bool) (m : Marks)
    (s : Log) (st : Insts Bytes) (i : Nat) (t : String) : String × Insts Bytes :=
  let named := fun (v : Bytes) =>
    (s.names.find? (fun (p : Bytes × String) => p.1 == v)).map (·.2)
  let plain := (s!"⟦{i}⟧ {m.at i}{t}", st)
  if !detail then plain else
  match s.tr.getMessageSentAt i with
  | none => plain
  | some b =>
    let sh := shapeOf keep named depth spineMax b
    -- Nothing derived to show, so nothing is numbered either.
    if sh.isOpaque then plain
    else
      let (txt, st) := sh.render st
      let prose := if t.isEmpty then "" else s!"/- {t} -/<br/>"
      (s!"{prose}⟦{i}⟧ {m.at i}{txt}", st)

/-- The drawing as a Mermaid `sequenceDiagram`. Lanes appear in the order the
    scenario established with `format_lanes`, then in order of first use.

    Message text is built by folding along the lines in order rather than mapping
    over them: a term prints its structure the first time it appears and only its
    number afterwards, so each line depends on everything drawn before it. -/
public def Log.mermaid [BytesShape] (detail : Bool) (s : Log) : String :=
  let m := marksOf s
  let keep := keepDrawn s
  let (lines, _) := s.lines.reverse.foldl
    (fun (acc : List Line × Insts Bytes) l =>
      match l with
      | .note lane t => (acc.1 ++ [.note lane (stripAll s.strip t)], acc.2)
      | .msg a b (some i) t =>
          let (txt, st) := msgLabel detail keep m s acc.2 i t
          (acc.1 ++ [.msg a b none (stripAll s.strip txt)], st)
      | other => (acc.1 ++ [other], acc.2))
    ([], {})
  -- A campaign with no probes gets no structure anywhere, which would otherwise
  -- look like a run whose messages happen to be opaque.
  let missing := if detail && (BytesShape.probes : List Probe).isEmpty then
      ["«no BytesShape probes: message structure not shown»"] else []
  let problems := match s.lanes.head? with
    | some l => (m.problems ++ missing).map (fun p => "  " ++ body (.note l p))
    | none => []
  String.intercalate "\n"
    ("sequenceDiagram"
      :: s.lanes.map participantLine
      ++ problems
      ++ renderFrom false lines)

/-- Run a scenario and return its diagram. Runs that abort still draw: the
    aborting step is the last line, marked REJECTED. -/
public def Scenario.diagram [BytesShape] (detail : Bool) (x : Scenario α)
    (tr : ExecTrace) : String :=
  (x.run tr).snd.mermaid detail

end

/-- Short enough to be read once and skipped thereafter. -/
private def legend : String := String.intercalate "\n"
  [ "## Legend",
    "",
    "| | |",
    "|---|---|",
    "| `▸ Name` | a step; `Name` is the definition it calls |",
    "| `/- … -/` | comment, maybe helpful for understanding the step |",
    "| `· name` | an event the step logged, named by its constructor |",
    "| `‹name›` | what the author called that value — declared, not derived |",
    "| `⟦n⟧` | the trace handle of the message |",
    "| `f:n(x)` | a constructor of the byte algebra `f`, and the term's instance number `n` |",
    "| `concat:n[a, b]` | a concatenation, flattened |",
    "| `concat:n[a, concat:k]` | `k` kept whole: it is also a message on the wire |",
    "| `f:n`, `concat:n` | that same term again; its structure is printed once, earlier |",
    "| `x ×n` | n adjacent copies of that same term |",
    "| `?:n` | a term without formatting information |",
    "| `…` | the depth limit cut here |",
    "| `«n entries»` | omitted trace entries |",
    "| `— REJECTED` | the driver returned `none`; the run stopped there |",
    "",
     ]

/-- Write the diagram as Markdown with a `mermaid` fence, creating the directory
    if needed. Paths are relative to the process working directory, which under
    `lake build` is the `lean/` root.

    Twice: the overview carries only the handles and the author's prose, and the
    detail carries the terms. The scenario is run once and the log drawn twice, so
    the two cannot disagree about what happened. -/
public def Scenario.writeDiagram [BytesFunctor] [ExecTraceTypes] [BytesShape]
    [ExecTraceTypes.Has Network.ExecEntryT] (x : Scenario α) (tr : ExecTrace)
    (path : System.FilePath) (title : String) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  let l := (x.run tr).snd
  IO.FS.writeFile path <| String.intercalate "\n"
    [ s!"# {title}", "",
      "## Overview", "",
      "```mermaid", l.mermaid false, "```", "",
      "## Terms", "",
      "The same run with the bytes shown.", "",
      "```mermaid", l.mermaid true, "```", "",
      legend, "" ]

end DYVis
