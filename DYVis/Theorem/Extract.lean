-- `#traceClaim thm` prints the claim tree the extractor reads out of a
-- theorem's conclusion. This is the UNCERTIFIED stage: it shows what the
-- classifier sees, so the mapping to a picture can be judged before the
-- `Iff.rfl` certificate is wired in.
--
-- A `Prop` that mentions the trace but is not recognised becomes `opaque`
-- rather than `check`, so giving up is visible instead of being disguised as a
-- value condition.
module

public import DYVis.Theorem.Claim
public meta import Lean

open Lean Elab Command Meta

namespace DYVis.Theorem.Extract

/-- Does `e` mention the trace variable? That is what separates a value
    condition from a trace property we failed to classify. -/
meta def mentions (tr : Expr) (e : Expr) : Bool :=
  (e.find? (· == tr)).isSome

/-- `tr` itself, or `tr.prefix i`. -/
meta def regionOf (tr : Expr) (t : Expr) : MetaM (Option Json) := do
  if t == tr then return some (Json.mkObj [("kind", "whole")])
  match t.getAppFnArgs with
  | (``DY.Trace.prefix, args) =>
      if args.size ≥ 2 && args[args.size - 2]! == tr then
        return some (Json.mkObj [("kind", "before"), ("i", toString (← ppExpr args[args.size - 1]!))])
      else return none
  | _ => return none

meta def render (e : Expr) : MetaM String := do
  return toString (← ppExpr e)

/-- The statement's own names that an expression mentions -- its free variables,
    not a scan of the printed form. A condition belongs to the event that binds
    what it talks about, and deciding that from text mistakes `rrset.rdata` for
    something other than `rrset`, and `= true` for a name. -/
meta def localsOf (e : Expr) : MetaM Json := do
  let mut out : Array Json := #[]
  let mut seen : Std.HashSet String := {}
  for fv in (Lean.collectFVars {} e).fvarIds do
    let d ← fv.getDecl
    -- Instances and type variables are carried by every term alike, so they
    -- say nothing about which event a condition is about.
    if d.binderInfo == .instImplicit then continue
    if (← isProp d.type) || (← whnfR d.type).isSort then continue
    let n := d.userName.toString
    unless seen.contains n do
      seen := seen.insert n
      out := out.push (Json.str n)
  return Json.arr out

/-- Split `a < b`. -/
meta def ltArgs? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``LT.lt, args) =>
      if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none
  | _ => none

/-- The event's own constructor, kept beside the rendered text so the viewer can
    ask where the model logs it. -/
meta def ctorField (ev : Expr) : List (String × Json) :=
  match ev.getAppFn with
  | .const c _ => [("ctor", Json.str c.toString)]
  | _ => []

/-- Recognise `∀ k, lo < k → k < hi → ¬ ev@k`. The two bounds must be the
    strict-order facts about the bound index, in that order; anything else falls
    through to `opaque` rather than being bent into this shape. -/
meta def absentBetween? (tr : Expr) (e : Expr) : MetaM (Option Json) := do
  forallTelescope e fun xs body => do
    if xs.size != 3 then return none
    let k := xs[0]!
    unless (← whnfR (← inferType k)).isConstOf ``Nat do return none
    let some (lo, k1) := ltArgs? (← whnfR (← inferType xs[1]!)) | return none
    let some (k2, hi) := ltArgs? (← whnfR (← inferType xs[2]!)) | return none
    -- Both bounds must actually be about `k`, else this is some other `∀`.
    unless k1 == k && k2 == k do return none
    let some inner := (← whnfR body).not? | return none
    match (← whnfR inner).getAppFnArgs with
    | (``DY.Trace.EventLoggedAt, args) =>
        let ev := args[args.size - 3]!
        unless args[args.size - 2]! == k do return none
        let some r ← regionOf tr args[args.size - 1]! | return none
        -- The event must not depend on `k`, or the picture cannot name it.
        if (ev.find? (· == k)).isSome then return none
        return some <| Json.mkObj
          (([("kind", "absentBetween"), ("ev", ← render ev),
             ("lo", ← render lo), ("hi", ← render hi),
             ("region", r)] : List (String × Json)) ++ ctorField ev)
    | _ => return none

/-- Name a predicate by the VALUES it constrains: drop instances, the trace and
    the position indices, which are plumbing the picture already shows as
    structure. `OfferedIn tr payload i` becomes `OfferedIn payload`. -/
meta def predArgs (tr : Expr) (f : Expr) (args : Array Expr) : MetaM (Array String) := do
  let ft ← inferType f
  let explicit ← forallBoundedTelescope ft args.size fun xs _ => do
    let mut out := #[]
    for i in [0:args.size] do
      if h : i < xs.size then
        if (← xs[i].fvarId!.getBinderInfo).isExplicit then out := out.push args[i]!
    return out
  let mut parts := #[]
  for a in explicit do
    if a == tr then continue
    let t ← whnfR (← inferType a)
    if t.isConstOf ``Nat then continue
    parts := parts.push (← render a)
  return parts

meta def predLabel (tr : Expr) (n : Name) (f : Expr) (args : Array Expr) : MetaM String := do
  let parts ← predArgs tr f args
  return " ".intercalate ((n.toString.splitOn "." |>.getLast!) :: parts.toList)

/-- A display name for a binder that is not already taken on this path. The
    notation rule is that a name means one value along a path, so two witnesses
    that meet in a conjunction must be told apart; alternatives may reuse.
    Primes rather than digits: the result has to be a legible Lean identifier,
    and `offers.1` comes back out of the pretty-printer as `«offers.1»`. -/
meta def freshName (used : Std.HashSet String) (base : String) : String := Id.run do
  let mut n := base
  for _ in [0:16] do
    if !used.contains n then return n
    n := n ++ "'"
  return n

/-- Whether a curried obligation concludes something that does not mention what
    it quantifies over. `denote_all_imp_const` is then the reading, and a `∀`
    whose conclusion is itself an `∃` stays a CHOICE rather than becoming an
    absence nested inside an absence.

    Decided here rather than in the renderer because it is a question about
    BINDERS: `forallTelescope` opens them as free variables and the answer is
    exact, where the renderer has only the printed names to match against. -/
meta def concludesIndependently (e : Expr) : MetaM Bool :=
  forallTelescope e fun xs body =>
    return !xs.any (fun x => body.containsFVar x.fvarId!)

private meta def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- `set_option dyvis.model "Protocols Crypto DY DYVis"`: the module-name
    prefixes whose declarations count as the model. Used twice, for the same
    reason both times: a constant mentioned in core is neither a protocol action
    nor a protocol predicate. The default covers DyLean (`DY`) and this library,
    so that `Example.lean` can carry controls for both; a project adds its own
    prefixes in the files that trace its theorems. -/
public meta initialize dyvisModelOption : Lean.Option String ←
  Lean.Option.register `dyvis.model
    { defValue := "DY DYVis"
      descr := "space-separated module prefixes whose declarations DYVis unfolds and searches for event emitters" }

private meta def modelPrefixes (opts : Options) : List Name :=
  ((dyvisModelOption.get opts).splitOn " ").filter (· ≠ "") |>.map String.toName

/-- Model modules only; see `dyvis.model`.

    `getModuleIdxFor?` answers only for IMPORTED declarations, and the one case
    it leaves is a declaration of the module being elaborated -- which is the
    model by construction. -/
private meta def ownModule (env : Environment) (opts : Options) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => (modelPrefixes opts).any (·.isPrefixOf m)
  | none => true

/-! ### Inductive predicates

`unfoldDefinition?` does not fire on an `inductive`: there is no body to
delta-reduce. So a predicate defined that way falls to the `opaque` case and is
drawn as a hole -- which is what every chain predicate in the corpus was.

Where the inductive is NOT recursive, its constructor characterisation is a
disjunction of existentials, which this grammar already has. All that is missing
is the TIE between the two, and that tie is not definitional -- so it is PROVED.
`casesThm?` states `∀ args, I args ↔ ⋁ᵢ ∃ fields, indices = args ∧ premises`,
discharges it, and adds it to the environment where the kernel checks it. The
rebuild direction is EMITTED from the same walk that built the arms rather than
searched for -- see `revScript`, and the paragraph there on what searching for it
cost. A predicate whose proof does not go through stays `opaque`, and there is no
`sorry` route in: the failure mode is a hole, never a false picture.

The drawn body is read back OFF that theorem rather than rebuilt, so the shape
in the picture and the shape the kernel checked are one object.

A RECURSIVE inductive is refused. Its characterisation cites itself, and the
notation has no repetition form -- see the README.
-/

/-- What one constructor's arm is made of: its name, the number of `∃`-bound
    data witnesses it opens with, whether each index equation is `HEq` rather
    than `Eq`, and how many `Prop` premises follow. That is everything the tie
    proof needs to write the arm's `obtain` pattern and discharge it. -/
private meta structure ArmPlan where
  ctor : Name
  data : Nat
  heqs : Array Bool
  props : Nat
  deriving Inhabited

/-- The characterisation of ONE constructor: its data fields become witnesses,
    its `Prop` fields and the equations pinning the indices become conjuncts. -/
private meta def ctorArm? (us : List Level) (params idxs : Array Expr) (c : Name) :
    MetaM (Option (Expr × ArmPlan)) := do
  let ctorTy ← inferType (mkAppN (mkConst c us) params)
  forallTelescope ctorTy fun fields concl => do
    let cargs := concl.getAppArgs
    if cargs.size != params.size + idxs.size then return none
    let mut parts : Array Expr := #[]
    let mut heqs : Array Bool := #[]
    for j in [0:idxs.size] do
      let a := cargs[params.size + j]!
      let b := idxs[j]!
      unless a == b do
        -- A DEPENDENT index -- `ChainAuthExec`'s `{nz} → SBytes nz` -- pins the
        -- two at different types, so the equation between them is `HEq`, and
        -- the tie proof has to peel the `Eq` ones off first. It draws as an
        -- ordinary check either way.
        if ← isDefEq (← inferType a) (← inferType b) then
          parts := parts.push (← mkEq a b)
          heqs := heqs.push false
        else
          parts := parts.push (← mkAppM ``HEq #[a, b])
          heqs := heqs.push true
    let mut data : Array Expr := #[]
    for f in fields do
      if ← isProp (← inferType f) then parts := parts.push (← inferType f)
      else data := data.push f
    let mut body : Expr := mkConst ``True
    if parts.size > 0 then
      body := parts[parts.size - 1]!
      for i in [1:parts.size] do body := mkAnd parts[parts.size - 1 - i]! body
    -- Explicitly bound, whatever the constructor's own binder info was: a
    -- field declared `{nc}` closes as `∃ {nc}`, and the tie's `grind` does not
    -- instantiate through one of those.
    for i in [0:data.size] do
      let lam ← mkLambdaFVars #[data[data.size - 1 - i]!] body
      body ← mkAppM ``Exists #[match lam with
        | .lam nm t b _ => .lam nm t b .default
        | other => other]
    -- A field whose type depends on a `Prop` field cannot be closed off this
    -- way: proof-irrelevant or not, the term would escape with a loose variable.
    if fields.any (fun f => body.containsFVar f.fvarId!) then return none
    return some (body, { ctor := c, data := data.size, heqs,
                         props := fields.size - data.size })

/-- Predicates whose characterisation could not be proved, so the proof is not
    re-attempted once per occurrence per walk. -/
public meta initialize casesRefused : IO.Ref NameSet ← IO.mkRef {}

/-- `⋁ᵢ (arm of constructor i)` for an application of a `Prop` inductive. For a
    RECURSIVE one the arm cites the predicate again, so this is one turn of the
    loop rather than a closed form -- which is exactly what `Claim.again` is
    for. MUTUAL recursion is still refused: `all.length != 1`. -/
private meta def casesBody? (e : Expr) : MetaM (Option (Expr × Array ArmPlan)) := do
  let .const n us := e.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? n | return none
  if iv.isNested || iv.all.length != 1 || iv.ctors.isEmpty then return none
  unless ← isProp e do return none
  -- `Iff`, `Eq` and `Nonempty` are non-recursive `Prop` inductives too, and
  -- expanding one to its constructor fields tells a reader nothing they wanted.
  unless ownModule (← getEnv) (← getOptions) n do return none
  let args := e.getAppArgs
  if args.size != iv.numParams + iv.numIndices then return none
  let params := args.extract 0 iv.numParams
  let idxs := args.extract iv.numParams args.size
  let mut arms : Array Expr := #[]
  let mut plans : Array ArmPlan := #[]
  for c in iv.ctors do
    let some (a, plan) ← ctorArm? us params idxs c | return none
    arms := arms.push a
    plans := plans.push plan
  let mut body := arms[arms.size - 1]!
  for i in [1:arms.size] do
    body := mkApp2 (mkConst ``Or) arms[arms.size - 1 - i]! body
  return some (body, plans)

/-- The proof that the arms REBUILD the predicate, written out from the plans
    rather than searched for.

    This direction used to be a `grind`, and that made whether a predicate could
    be drawn depend on things that have nothing to do with the predicate: the
    same `ChainAuthExec`, copied verbatim between two campaigns, tied in DANE
    and not in aDNS because aDNS's trace is a seventeen-source `#combine`
    instead of a twelve-source one. Nothing about that is visible to a reader,
    and the failure shows up two files away as a hole in a picture.

    So the script is emitted from the same walk that built the arm. Peel the
    `Eq` index equations first -- each has one of the theorem's own index
    variables on the right, so `subst` always fires -- which makes the `HEq`
    ones homogeneous, and then the arm's `Prop` premises ARE the constructor's
    arguments. `first` picks the arm by name resolution: each arm's script only
    mentions names its own branch bound. -/
private meta def revScript (plans : Array ArmPlan) :
    TermElabM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let mut pats : Array (TSyntax `rcasesPat) := #[]
  let mut alts : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[]
  for i in [0:plans.size] do
    let p := plans[i]!
    let eN : Nat → Ident := fun j => mkIdent (Name.mkSimple s!"dvE{i}_{j}")
    let pN : Nat → Ident := fun j => mkIdent (Name.mkSimple s!"dvP{i}_{j}")
    let hN : Nat → Ident := fun j => mkIdent (Name.mkSimple s!"dvH{i}_{j}")
    let mut comps : Array (TSyntax ``Lean.Parser.Tactic.rcasesPatLo) := #[]
    for _ in [0:p.data] do comps := comps.push (← `(Lean.Parser.Tactic.rcasesPatLo| _))
    for j in [0:p.heqs.size] do comps := comps.push (← `(Lean.Parser.Tactic.rcasesPatLo| $(eN j):ident))
    for j in [0:p.props] do comps := comps.push (← `(Lean.Parser.Tactic.rcasesPatLo| $(pN j):ident))
    -- An arm with no equations and no premises ends in `True`, which is still a
    -- component of the tuple.
    if p.heqs.size + p.props == 0 then comps := comps.push (← `(Lean.Parser.Tactic.rcasesPatLo| _))
    pats := pats.push (← `(rcasesPat| ⟨$comps,*⟩))
    let mut steps : Array (TSyntax `tactic) := #[]
    for j in [0:p.heqs.size] do
      unless p.heqs[j]! do steps := steps.push (← `(tactic| subst $(eN j):ident))
    for j in [0:p.heqs.size] do
      if p.heqs[j]! then
        steps := steps.push (← `(tactic| have $(hN j):ident := eq_of_heq $(eN j)))
        steps := steps.push (← `(tactic| subst $(hN j):ident))
    let ctorId := mkIdent p.ctor
    let args : Array Term := (Array.range p.props).map (fun j => pN j)
    -- `exact` where the data fields are implicit, as they are throughout the
    -- corpus; `apply` for a constructor that takes some of them explicitly.
    steps := steps.push (← `(tactic| first
      | exact $ctorId $args*
      | (apply $ctorId <;> assumption)))
    let seq ← `(tacticSeq| $[$steps]*)
    alts := alts.push seq
  let pat ← `(Lean.Parser.Tactic.rcasesPatMed| $[$pats]|*)
  `(tacticSeq| intro dvh
               obtain $pat := dvh <;> first $[| $alts]*)

/-- `<I>.dyvisCases`, generating it if this is the first sight of `I`. `none`
    where the predicate is not one this handles, or where the proof fails. -/
private meta def casesThm? (n : Name) : TermElabM (Option Name) := do
  let thm := n ++ `dyvisCases
  if (← getEnv).contains thm then return some thm
  if (← casesRefused.get).contains n then return none
  let refuse : TermElabM (Option Name) := do casesRefused.modify (·.insert n); return none
  let some (.inductInfo iv) := (← getEnv).find? n | refuse
  let us := iv.levelParams.map Level.param
  let msgs := (← getThe Core.State).messages
  -- Elaborate as if inside the PREDICATE's namespace, not the traced theorem's.
  -- The tactics below need the scoped instances declared alongside `I`, and a
  -- consumer citing `I` from its own protocol has none of them -- so the same
  -- proof that lands where `I` is declared fails one import away. Scoped entries
  -- are activated into the ENVIRONMENT by `namespace`, so setting the reader's
  -- namespace alone does nothing. The activation is NOT undone: the tactic's
  -- auxiliary proofs are declarations too, and rolling back would take them with
  -- it, leaving the characterisation citing constants that no longer exist.
  let ns := n.getPrefix
  let nsChain := (ns.components.foldl (init := (([] : List Name), Name.anonymous))
    fun (acc, cur) c => let cur := cur ++ c; (acc ++ [cur], cur)).1
  for p in nsChain do activateScoped p
  -- In an EMPTY context: the caller is inside the traced theorem's own binders,
  -- and a proof that picked one up would be a declaration with free variables.
  let out ← withTheReader Core.Context (fun ctx =>
      { ctx with currNamespace := ns, openDecls := .simple ns [] :: ctx.openDecls }) <|
    withLCtx {} {} <| forallTelescope iv.type fun xs _ => do
    let e := mkAppN (mkConst n us) xs
    let some (body, plans) ← casesBody? e | return none
    let goal ← mkAppM ``Iff #[e, body]
    let fwds : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[
      (← `(tacticSeq| intro h; cases h <;> grind)),
      (← `(tacticSeq| intro h; cases h <;> grind [$(mkIdent n):ident])),
      (← `(tacticSeq| intro h; cases h <;> (subst_eqs <;> grind [$(mkIdent n):ident]))),
      (← `(tacticSeq| intro h; induction h <;> grind [$(mkIdent n):ident]))]
    -- The emitted rebuild first; the `grind` stays behind it for a shape the
    -- plans do not cover.
    let revs : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[
      (← revScript plans),
      (← `(tacticSeq| intro h; grind [$(mkIdent n):ident]))]
    let mut tacs : Array (TSyntax `tactic) := #[]
    for r in revs do
      for f in fwds do
        tacs := tacs.push (← `(tactic| (constructor
                                        · $f:tacticSeq
                                        · $r:tacticSeq)))
    let attempt : TSyntax `tactic → TermElabM (Option Expr) := fun tac => try
        Term.withoutErrToSorry do
          let mvar ← mkFreshExprSyntheticOpaqueMVar goal
          let (rem, _) ← runTactic mvar.mvarId! tac
          let pf ← instantiateMVars mvar
          if rem.isEmpty && !pf.hasSorry && !pf.hasExprMVar
              && !(← getThe Core.State).messages.hasErrors then
            pure (some pf)
          else pure none
      catch _ => pure none
    let mut pf? : Option Expr := none
    for tac in tacs do
      if pf?.isNone then
        modifyThe Core.State fun s => { s with messages := msgs }
        pf? ← attempt tac
    let some pf := pf? | return none
    return some ((← mkForallFVars xs goal), (← mkLambdaFVars xs pf))
  modifyThe Core.State fun s => { s with messages := msgs }
  let some (ty, val) := out | refuse
  try
    addDecl (.thmDecl { name := thm, levelParams := iv.levelParams,
                        type := ty, value := val })
    return some thm
  catch _ => refuse

/-- The `⋁` chain `casesBody?` built, back into one expression per constructor.
    It is right-nested and exactly as long as the constructor list, so splitting
    off the first `n-1` left components recovers the arms -- and does so even
    where an arm is itself a disjunction. -/
private meta partial def orChain (n : Nat) (e : Expr) : Array Expr :=
  if n ≤ 1 then #[e]
  else match e.getAppFnArgs with
    | (``Or, #[a, b]) => #[a] ++ orChain (n - 1) b
    | _ => #[e]

/-- The tie theorem for `e`, the body it draws, and the constructor each
    alternative of that body came from. The body is read OFF the theorem rather
    than rebuilt, so what the picture shows and what the kernel checked cannot
    drift apart.

    The constructor names are carried because the arms HAVE names in the source
    -- `compromised` and `unregistered` are the author's own words for the two
    ways a key is beyond help -- and an anonymous alternative makes the reader
    recover that from the shape. Qualified by the predicate, as an event name
    is by its type: two inductives may well both have a `here`, and the audit
    reads one name as one thing. -/
private meta def casesOf? (e : Expr) : TermElabM (Option (Name × Expr × Array String)) := do
  let .const n us := e.getAppFn | return none
  let some thm ← casesThm? n | return none
  let ty ← instantiateForall ((← getConstInfo thm).instantiateTypeLevelParams us) e.getAppArgs
  let some (.inductInfo iv) := (← getEnv).find? n | return none
  let ctors := iv.ctors.toArray.map fun c =>
    ".".intercalate ((c.componentsRev.take 2).reverse.map toString)
  match ty.getAppFnArgs with
  | (``Iff, #[lhs, rhs]) => if lhs == e then return some (thm, rhs, ctors) else return none
  | _ => return none

/-! ### The claim as a TERM

The statement is walked ONCE, into a `Claim` term, so that the translation can
be stated as a theorem and checked rather than believed. `jsonOfClaim` below
then reads the renderer's JSON off that term, so the drawn shape and the
certified shape cannot drift apart -- they had, at the arm labels, for as long
as there were two walks. -/

/-- The event type is inferred from the event itself, and the `Has` instance
    synthesised, so one claim may mix alphabets. -/
meta def mkClaim (ctor : Name) (args : Array Expr) : MetaM Expr :=
  mkAppM ctor args

meta def regionExpr (tr : Expr) (t : Expr) : MetaM (Option Expr) := do
  if t == tr then return some (mkConst ``Region.whole [])
  match t.getAppFnArgs with
  | (``DY.Trace.prefix, args) =>
      if args.size ≥ 2 && args[args.size - 2]! == tr then
        return some (mkApp (mkConst ``Region.before []) args[args.size - 1]!)
      else return none
  | _ => return none

/-- The `Claim` term for a proposition. `none` where the
    shape is not one this grammar has a constructor for. -/
meta def absentBetweenExpr? (tr : Expr) (e : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  forallTelescope e fun xs body => do
    if xs.size != 3 then return none
    let k := xs[0]!
    unless (← whnfR (← inferType k)).isConstOf ``Nat do return none
    let some (lo, k1) := ltArgs? (← whnfR (← inferType xs[1]!)) | return none
    let some (k2, hi) := ltArgs? (← whnfR (← inferType xs[2]!)) | return none
    unless k1 == k && k2 == k do return none
    let some inner := (← whnfR body).not? | return none
    match (← whnfR inner).getAppFnArgs with
    | (``DY.Trace.EventLoggedAt, args) =>
        let ev := args[args.size - 3]!
        unless args[args.size - 2]! == k do return none
        let some r ← regionExpr tr args[args.size - 1]! | return none
        if (ev.find? (· == k)).isSome then return none
        return some (lo, hi, ev, r)
    | _ => return none

/-- Is this predicate one whose characterisation cites itself? -/
meta def isRecPred (n : Name) : MetaM Bool := do
  match (← getEnv).find? n with
  | some (.inductInfo iv) => return iv.isRec
  | _ => return false

/-- `expanding` is the predicates a turn of which is already open above here, so
    a second sight of one is the LOOP rather than a second box. `neg` is the
    polarity: a repetition under a `¬` would need "no chain of any length",
    which the forbidden-shape notation does not have, so it is refused there and
    falls to `opaque`. The antecedent of an `imp` counts as negative -- it is
    what `denote_imp` draws negated.

    `used` freshens binder names, so two witnesses both written `params` are
    told apart as `params` and `params'`. Done HERE rather than when exporting
    because the labels are baked into the term: a name resolved later cannot
    reach the string already written, and the two disagreed exactly there.
    Renaming a bound variable is alpha-equivalence, so `Iff.rfl` is untouched
    and the certified term now shows the names the picture does. -/
public meta partial def toClaimExpr (tr : Expr) (e0 : Expr) (used : Std.HashSet String)
    (expanding : NameSet := {}) (neg : Bool := false) (base : Std.HashSet String := {}) :
    TermElabM (Expr × Std.HashSet String) := do
  let e ← whnfR e0
  let structural := match e.getAppFnArgs with
    | (``And, #[_, _]) | (``Or, #[_, _]) | (``Exists, #[_, _]) => true
    | _ => false
  if !structural && !mentions tr e then
    return (← mkClaim ``Claim.check #[e0], used)
  match e.getAppFnArgs with
  | (``Or, #[a, b]) => do
      -- Alternatives never co-occur, so each branch starts from the same names.
      let (ja, ua) ← toClaimExpr tr a used expanding neg base
      let (jb, ub) ← toClaimExpr tr b used expanding neg base
      return (← mkClaim ``Claim.or #[ja, jb], ua.insertMany ub.toList)
  | (``And, #[a, b]) => do
      let (ja, ua) ← toClaimExpr tr a used expanding neg base
      let (jb, ub) ← toClaimExpr tr b ua expanding neg base
      return (← mkClaim ``Claim.and #[ja, jb], ub)
  | (``Not, #[a]) => do
      -- A witness under a `∄` is bound by it, so it has nothing to be told apart
      -- from among its siblings -- but it still shares the picture with the
      -- statement's own parameters, so the reset goes back to those, not to
      -- nothing. Resetting to nothing drew `∄ ... svc ...` beside an unrelated
      -- `svc` in eight theorems.
      let (ja, _) ← toClaimExpr tr a base expanding (!neg) base
      return (← mkClaim ``Claim.not #[ja], used)
  | (``Exists, #[α, f]) =>
      lambdaBoundedTelescope f 1 fun xs body => do
        let x := xs[0]!
        let n := freshName used (← x.fvarId!.getUserName).toString
        withLocalDeclD (Name.mkSimple n) (← inferType x) fun y => do
          let (inner, uc) ← toClaimExpr tr (body.replaceFVar x y) (used.insert n) expanding neg base
          return (← mkClaim ``Claim.ex #[α, ← mkLambdaFVars #[y] inner], uc)
  | (``DY.Trace.EventLogged, args) => do
      let ev := args[args.size - 2]!
      match ← regionExpr tr args[args.size - 1]! with
      | some r => return (← mkClaim ``Claim.occurs #[ev, r], used)
      | none => return (← mkClaim ``Claim.opaque #[e], used)
  | (``DY.Trace.EventLoggedAt, args) => do
      let ev := args[args.size - 3]!
      let i := args[args.size - 2]!
      match ← regionExpr tr args[args.size - 1]! with
      | some r => return (← mkClaim ``Claim.occursAt #[ev, i, r], used)
      | none => return (← mkClaim ``Claim.opaque #[e], used)
  | (``DY.Trace.StateStored, args) => do
      let st := args[args.size - 2]!
      match ← regionExpr tr args[args.size - 1]! with
      | some r => return (← mkClaim ``Claim.stored #[st, r], used)
      | none => return (← mkClaim ``Claim.opaque #[e], used)
  | (``DY.Bytes.AttackerKnows, args) => do
      let b := args[args.size - 2]!
      match ← regionExpr tr args[args.size - 1]! with
      | some r => return (← mkClaim ``Claim.knows #[b, r], used)
      | none => return (← mkClaim ``Claim.opaque #[e], used)
  | (``DY.Trace.StateStoredAt, args) => do
      let st := args[args.size - 3]!
      let i := args[args.size - 2]!
      match ← regionExpr tr args[args.size - 1]! with
      | some r => return (← mkClaim ``Claim.storedAt #[st, i, r], used)
      | none => return (← mkClaim ``Claim.opaque #[e], used)
  | _ => do
      if let some (lo, hi, ev, r) ← absentBetweenExpr? tr e then
        return (← mkClaim ``Claim.absentBetween #[ev, lo, hi, r], used)
      if e.isForall then
        if let .forallE _ d b _ := e then
          if !b.hasLooseBVars then
            if ← isProp d then
              let (ja, ua) ← toClaimExpr tr d used expanding (!neg) base
              let (jb, ub) ← toClaimExpr tr b ua expanding neg base
              return (← mkClaim ``Claim.imp #[ja, jb], ub)
          else if !(← isProp d) then
            -- A `∀` over DATA. Held as it stands, so the certificate stays
            -- `Iff.rfl`; `denote_all_imp` is what makes it drawable. Fails
            -- over for a binder this grammar's `α : Type` cannot hold.
            if let some c ← (try
                forallBoundedTelescope e (some 1) fun xs body => do
                  let x := xs[0]!
                  let n := freshName used (← x.fvarId!.getUserName).toString
                  withLocalDeclD (Name.mkSimple n) (← inferType x) fun y => do
                    let (inner, uc) ←
                      toClaimExpr tr (body.replaceFVar x y) (used.insert n) expanding neg base
                    return some (← mkClaim ``Claim.all #[d, ← mkLambdaFVars #[y] inner], uc)
              catch _ => pure none) then
              return c
      if let .const n _ := e.getAppFn then
        -- A turn of this predicate is already open above: this is the loop.
        if expanding.contains n then
          return (← mkClaim ``Claim.again
            #[mkStrLit (← predLabel tr n e.getAppFn e.getAppArgs),
              mkStrLit n.toString, e], used)
        if let some e' ← unfoldDefinition? e then
          let label ← predLabel tr n e.getAppFn e.getAppArgs
          let (jc, uc) ← toClaimExpr tr e' used expanding neg base
          return (← mkClaim ``Claim.named #[mkStrLit label, jc], uc)
        -- An inductive has no body to unfold; `Claim.cases` HOLDS it, so this
        -- stays as definitional as every other case.
        if !(neg && ( ← isRecPred n)) then
         if let some (thm, body, ctors) ← casesOf? e then
          let label ← predLabel tr n e.getAppFn e.getAppArgs
          let inner := expanding.insert n
          let head := fun (arms : Expr) => mkClaim ``Claim.cases
            #[mkStrLit label, mkStrLit n.toString, mkStrLit thm.toString, e, arms]
          let arms := orChain ctors.size body
          unless arms.size == ctors.size do
            let (jc, uc) ← toClaimExpr tr body used inner neg base
            return (← head jc, uc)
          -- The arm wears the predicate's ARGUMENTS as well as its constructor:
          -- bare, two arms of one name at different values read as one box.
          let argList ← predArgs tr e.getAppFn e.getAppArgs
          let mut js : Array Expr := #[]
          let mut u := used
          for i in [0:arms.size] do
            -- Alternatives never co-occur, so each starts from the same names.
            let (ja, ua) ← toClaimExpr tr arms[i]! used inner neg base
            js := js.push (← mkClaim ``Claim.named
              #[mkStrLit (" ".intercalate (ctors[i]! :: argList.toList)), ja])
            u := u.insertMany ua.toList
          let mut acc := js[js.size - 1]!
          for i in [1:js.size] do
            acc ← mkClaim ``Claim.or #[js[js.size - 1 - i]!, acc]
          return (← head acc, u)
      return (← mkClaim ``Claim.opaque #[e], used)

private meta def strOf (e : Expr) : String :=
  match e with
  | .lit (.strVal s) => s
  | _ => ""

private meta def regionJson (r : Expr) : MetaM Json := do
  match (← whnfR r).getAppFnArgs with
  | (``Region.before, args) =>
      return Json.mkObj [("kind", "before"), ("i", toString (← ppExpr args[args.size - 1]!))]
  | _ => return Json.mkObj [("kind", "whole")]

/-- `concludesIndependently` over a CLAIM rather than the `∀` it came from.
    `forallTelescope` walks arrows as well as binders, so the mirror descends
    through `imp` too, or a curried obligation answers differently here than it
    did on the way in. -/
private meta partial def claimConcludesIndependently
    (c : Expr) (xs : Array Expr) : MetaM Bool := do
  let c ← whnfR c
  let as := c.getAppArgs
  match c.getAppFn with
  | .const ``Claim.all _ =>
      lambdaBoundedTelescope as[as.size - 1]! 1 fun ys body =>
        claimConcludesIndependently body (xs ++ ys)
  | .const ``Claim.imp _ => claimConcludesIndependently as[as.size - 1]! xs
  | _ => return !xs.any (fun x => c.containsFVar x.fvarId!)

/-! ### Normalising the claim, with a proof for each step

The rewrites that turn a raw translation into the shape the picture needs used
to run on the JSON, mirroring lemmas proved in `Claim.lean`. Nothing checked the
mirror, so the drawn shape was not the certified shape. These run on the TERM
instead, and each returns its lemma instance; `Rewrites.trans` composes them, so
`isClaim` ends up about the shape that is actually drawn. -/

/-- A claim together with `Rewrites old new` -- the proof that the step did not
    change what is being said. -/
public meta abbrev Step := Expr × Expr

private meta def rwRfl (c : Expr) : MetaM Expr := mkAppM ``Rewrites.rfl #[c]

private meta def rwTrans (h₁ h₂ : Expr) : MetaM Expr := mkAppM ``Rewrites.trans #[h₁, h₂]

private meta def impArgs? (c : Expr) : Option (Expr × Expr) :=
  match c.getAppFnArgs with
  | (``Claim.imp, as) =>
      if as.size ≥ 2 then some (as[as.size - 2]!, as[as.size - 1]!) else none
  | _ => none

/-- `denote_curry`: premises arrive curried, one arrow each, because that is how
    a theorem is written. Drawn that way each premise reads as following from
    the last, so they are collected into one conjunction.

    Applied innermost first, so the conjunction comes out right-nested -- the
    way `∧` associates everywhere else here. -/
private meta partial def uncurryExpr (c : Expr) : MetaM Step := do
  let some (a, b) := impArgs? c | return (c, ← rwRfl c)
  let (b', hb) ← uncurryExpr b
  let hc ← mkAppM ``Rewrites.imp #[← rwRfl a, hb]
  match impArgs? b' with
  | some (p, concl) =>
      let step ← mkAppM ``denote_curry #[a, p, concl]
      return (← mkClaim ``Claim.imp #[← mkClaim ``Claim.and #[a, p], concl],
              ← rwTrans hc step)
  | none => return (← mkClaim ``Claim.imp #[a, b'], hc)

/-- Rewrite the one leaf of a conjunction that matches, lifting its proof back
    out through the `∧`s above it. `none` when nothing matches. -/
private meta partial def rwFirstAnd (p : Expr → Bool) (f : Expr → MetaM Step) (c : Expr) :
    MetaM (Option Step) := do
  match c.getAppFnArgs with
  | (``Claim.and, as) =>
      let a := as[as.size - 2]!
      let b := as[as.size - 1]!
      if let some (a', ha) ← rwFirstAnd p f a then
        return some (← mkClaim ``Claim.and #[a', b],
                     ← mkAppM ``Rewrites.and #[ha, ← rwRfl b])
      if let some (b', hb) ← rwFirstAnd p f b then
        return some (← mkClaim ``Claim.and #[a, b'],
                     ← mkAppM ``Rewrites.and #[← rwRfl a, hb])
      return none
  | _ => if p c then return some (← f c) else return none

private meta def isWholeOccurs (c : Expr) : Bool :=
  match c.getAppFnArgs with
  | (``Claim.occurs, as) =>
      as.size ≥ 1 && as[as.size - 1]!.isAppOf ``Region.whole
        || (as.size ≥ 1 && as[as.size - 1]!.isConstOf ``Region.whole)
  | _ => false

private meta partial def countAnd (p : Expr → Bool) (c : Expr) : Nat :=
  match c.getAppFnArgs with
  | (``Claim.and, as) =>
      countAnd p as[as.size - 2]! + countAnd p as[as.size - 1]!
  | _ => if p c then 1 else 0

/-- The claim on the right of an `Iff` in a `Rewrites` proof's own type -- so the
    shape produced is read OFF the lemma rather than rebuilt beside it. -/
private meta def rhsOfRewrites (h : Expr) : MetaM Expr := do
  forallTelescope (← inferType h) fun _ ty => do
    let some (_, rhs) := (← whnfR ty).iff? | throwError "not an Iff"
    let as := (← whnfR rhs).getAppArgs
    return as[as.size - 2]!

/-- `denote_occurs_at`: give a trigger stated without a position one, so the
    conclusion can be bounded by it.

    `EventLogged` IS `∃ i, EventLoggedAt … i`, so this asserts nothing new. But
    the bound `rescope` applies is stated against the trigger's index, and a
    trigger written `EventLogged` has none -- leaving the conclusion unbounded
    and the ordering it does have undrawn. Only a lone event premise is pinned:
    with one already positioned there is nothing to gain, and with two the bound
    is the later of them and the statement need not say which. -/
private meta def pinExpr (c : Expr) : MetaM Step := do
  let keep : MetaM Step := return (c, ← rwRfl c)
  let some (a, b) := impArgs? c | keep
  if (a.find? (·.isAppOf ``Claim.occursAt)).isSome then return ← keep
  if countAnd isWholeOccurs a != 1 then return ← keep
  let pinLeaf := fun (leaf : Expr) => do
    let ev := leaf.getAppArgs[leaf.getAppArgs.size - 2]!
    let h ← mkAppM ``denote_occurs_at #[ev]
    return ((← rhsOfRewrites h : Expr), h)
  match ← rwFirstAnd isWholeOccurs pinLeaf a with
  | some (a', ha) =>
      return (← mkClaim ``Claim.imp #[a', b], ← mkAppM ``Rewrites.imp #[ha, ← rwRfl b])
  | none => keep

/-- The JSON the picture is drawn from, read OFF the certified term instead of
    walked out of the statement a second time. Two walks agreed on every
    reference theorem and on nothing enforced; the arm labels had already
    drifted apart when this replaced them. -/
public meta partial def jsonOfClaim (c0 : Expr) : MetaM Json := do
  let c ← whnfR c0
  let as := c.getAppArgs
  let arg (k : Nat) : Expr := as[as.size - k]!
  let evNode (kind : String) (ev : Expr) (extra : List (String × Json))
      (region : Expr) : MetaM Json := do
    return Json.mkObj ((("kind", Json.str kind) :: ("ev", Json.str (← render ev)) :: extra)
      ++ [("vars", ← localsOf ev), ("region", ← regionJson region)] ++ ctorField ev)
  match c.getAppFn with
  | .const nm _ =>
    match nm with
    | ``Claim.occurs => evNode "occurs" (arg 2) [] (arg 1)
    | ``Claim.occursAt => evNode "occursAt" (arg 3) [("i", ← render (arg 2))] (arg 1)
    | ``Claim.stored => evNode "stored" (arg 2) [] (arg 1)
    | ``Claim.storedAt => evNode "storedAt" (arg 3) [("i", ← render (arg 2))] (arg 1)
    | ``Claim.absentBetween =>
        let ev := arg 4
        return Json.mkObj (([("kind", "absentBetween"), ("ev", ← render ev),
          ("lo", ← render (arg 3)), ("hi", ← render (arg 2)),
          ("region", ← regionJson (arg 1))] : List (String × Json)) ++ ctorField ev)
    | ``Claim.knows =>
        let b := arg 2
        return Json.mkObj [("kind", "knows"), ("ev", ← render b),
          ("vars", ← localsOf b), ("region", ← regionJson (arg 1))]
    | ``Claim.check =>
        return Json.mkObj [("kind", "check"), ("p", ← render (arg 1)),
          ("vars", ← localsOf (arg 1))]
    | ``Claim.opaque => return Json.mkObj [("kind", "opaque"), ("p", ← render (arg 1))]
    | ``Claim.again =>
        return Json.mkObj [("kind", "again"), ("n", Json.str (strOf (arg 3))),
          ("of", Json.str (strOf (arg 2)))]
    | ``Claim.and =>
        return Json.mkObj [("kind", "and"), ("a", ← jsonOfClaim (arg 2)),
          ("b", ← jsonOfClaim (arg 1))]
    | ``Claim.or =>
        return Json.mkObj [("kind", "or"), ("a", ← jsonOfClaim (arg 2)),
          ("b", ← jsonOfClaim (arg 1))]
    | ``Claim.imp =>
        return Json.mkObj [("kind", "imp"), ("a", ← jsonOfClaim (arg 2)),
          ("b", ← jsonOfClaim (arg 1))]
    | ``Claim.not => return Json.mkObj [("kind", "not"), ("c", ← jsonOfClaim (arg 1))]
    | ``Claim.named =>
        return Json.mkObj [("kind", "named"), ("n", Json.str (strOf (arg 2))),
          ("c", ← jsonOfClaim (arg 1))]
    | ``Claim.cases =>
        return Json.mkObj [("kind", "cases"), ("n", Json.str (strOf (arg 5))),
          ("tie", Json.str (strOf (arg 3))), ("of", Json.str (strOf (arg 4))),
          ("c", ← jsonOfClaim (arg 1))]
    | ``Claim.ex =>
        lambdaBoundedTelescope (arg 1) 1 fun xs body => do
          return Json.mkObj [("kind", "ex"),
            ("binder", Json.str (← xs[0]!.fvarId!.getUserName).toString),
            ("c", ← jsonOfClaim body)]
    | ``Claim.all =>
        lambdaBoundedTelescope (arg 1) 1 fun xs body => do
          return Json.mkObj [("kind", "all"),
            ("binder", Json.str (← xs[0]!.fvarId!.getUserName).toString),
            ("c", ← jsonOfClaim body),
            ("closed", Json.bool (← claimConcludesIndependently c #[]))]
    | _ => return Json.mkObj [("kind", "opaque"), ("p", ← render c)]
  | _ => return Json.mkObj [("kind", "opaque"), ("p", ← render c)]

/-- Trace one theorem: report its shape and hold it for the next
    `#traceClaimsToFile`. Meant to sit directly under the theorem it names. -/
syntax (name := traceClaimCmd) "#traceClaim " ident : command

/-- Write every theorem traced since the last write, to a path relative to the
    root of the package the module is in. Meant to sit at the foot of the file,
    or of the campaign. -/
syntax (name := traceClaimsToFileCmd) "#traceClaimsToFile " str : command

/-! ### Normalisation

Each rewrite below is the counterpart of a lemma proved in `Claim.lean`, and is
applied here rather than in the renderer so that whether a rewrite was licensed
is decided once, beside its proof, instead of being re-decided by the code that
draws the picture. -/

meta def kindOf (c : Json) : String := (c.getObjValAs? String "kind").toOption.getD ""

meta def field (c : Json) (k : String) : Json := (c.getObjVal? k).toOption.getD Json.null

meta def isClaim (c : Json) : Bool := kindOf c != ""

/-- Sub-claims of a node, whatever its shape. -/
meta def kids (c : Json) : List String :=
  ["a", "b", "c"].filter (fun k => isClaim (field c k))

meta def mapKids (f : Json → Json) (c : Json) : Json :=
  (kids c).foldl (fun acc k => acc.setObjVal! k (f (field acc k))) c

/-- `denote_curry`: the premises arrive curried, one arrow each, because that is
    the theorem's own shape and so the shape the certificate is over. The diagram
    wants them gathered, so that "the premises failed" is ONE alternative rather
    than a nest of them -- which draws the later premises as if they followed
    from the earlier. -/
meta partial def impChain (c : Json) (acc : Array Json) : Array Json × Json :=
  if kindOf c == "imp" then impChain (field c "b") (acc.push (field c "a")) else (acc, c)

meta def uncurry (c : Json) : Json := Id.run do
  let (ps, concl) := impChain c #[]
  if ps.size == 0 then return c
  -- Right-nested, matching how `∧` associates elsewhere.
  let mut p := ps[ps.size - 1]!
  for i in [1:ps.size] do
    p := Json.mkObj [("kind", "and"), ("a", ps[ps.size - 1 - i]!), ("b", p)]
  return Json.mkObj [("kind", "imp"), ("a", p), ("b", concl)]

meta partial def flattenAnd (c : Json) (acc : Array Json) : Array Json :=
  if kindOf c == "and" then flattenAnd (field c "b") (flattenAnd (field c "a") acc)
  else acc.push c

/-- Every statement variable a claim mentions, wherever it occurs. -/
meta partial def varsOf (c : Json) : Std.HashSet String := Id.run do
  let mut out : Std.HashSet String := {}
  if let Except.ok v := c.getObjVal? "vars" then
    if let Json.arr xs := v then
      for x in xs do
        if let Except.ok s := x.getStr? then out := out.insert s
  for k in kids c do
    for s in (varsOf (field c k)).toList do out := out.insert s
  return out

/-- Does this claim say anything about the trace itself? -/
meta partial def hasEvent (c : Json) : Bool :=
  (["occurs", "occursAt", "absentBetween", "opaque"].contains (kindOf c))
    || (kids c).any (fun k => hasEvent (field c k))

/-- Does it pin an event to an index? That is the event a statement is triggered
    by, and so the one a condition spanning several belongs to. -/
meta partial def triggers (c : Json) : Bool :=
  kindOf c == "occursAt" || (kids c).any (fun k => triggers (field c k))

private meta def andJson (a b : Json) : Json :=
  Json.mkObj [("kind", "and"), ("a", a), ("b", b)]

/-- `denote_and_comm` / `denote_and_assoc`: move each value premise next to the
    event it constrains.

    A value premise is not a statement about the run, so left as a conjunct of
    its own it becomes a branch reading "no trace in which this condition
    fails", which is not a set of traces. Grouped onto its event, the branch
    reads "no event of this description occurred", which is. -/
meta def regroup (c : Json) : Json := Id.run do
  if kindOf c != "imp" then return c
  let parts := (flattenAnd (field c "a") #[])
  let mut anchors := parts.filter hasEvent
  let floats := parts.filter (fun p => !hasEvent p)
  if anchors.isEmpty || floats.isEmpty then return c
  let mut loose : Array Json := #[]
  for f in floats do
    let fv := varsOf f
    -- Most shared names wins; on a tie the event the statement is triggered by,
    -- since that is what it is about. A condition touching nothing stays loose.
    let score := fun (a : Json) =>
      let shared := ((varsOf a).toList.filter fv.contains).length
      if shared == 0 then 0
      else 2 * shared + (if triggers a then 1 else 0)
    let scores := anchors.map score
    let best := scores.foldl max 0
    let winners := (List.range anchors.size).filter (fun i => scores[i]! == best)
    match winners with
    | [i] => if best > 0 then anchors := anchors.set! i (andJson anchors[i]! f)
             else loose := loose.push f
    | _ => loose := loose.push f
  let all := anchors ++ loose
  let mut p := all[all.size - 1]!
  for i in [1:all.size] do p := andJson all[all.size - 1 - i]! p
  return Json.mkObj [("kind", "imp"), ("a", p), ("b", field c "b")]

private meta def andChain (parts : Array Json) : Json := Id.run do
  if parts.size == 0 then return Json.mkObj [("kind", "check"), ("p", "True")]
  let mut p := parts[parts.size - 1]!
  for i in [1:parts.size] do p := andJson parts[parts.size - 1 - i]! p
  return p

/-- `denote_and_or`: a choice standing beside a REQUIREMENT at the same event
    cannot be drawn -- both arrive as arrows, and nothing says which is which.
    Distributing the choice over that requirement gives one complete alternative
    per branch.

    The TRIGGER is deliberately left outside: it holds on every branch, so
    distributing over it too would duplicate the event the whole statement is
    about, for nothing. That is the difference from an unbounded `∄`, which is a
    claim about the entire run and so does need separate runs. -/
meta partial def spread (c : Json) : Json :=
  let c := mapKids spread c
  if kindOf c != "and" then c else
    let parts := flattenAnd c #[]
    -- Only a choice between EVENTS. A choice between conditions is one event
    -- qualifying two ways, drawn as alternatives on that event, so distributing
    -- it would duplicate the run for nothing and split the conditions apart.
    let ors := parts.filter (fun p => kindOf p == "or" && hasEvent p)
    let extras := parts.filter (fun p => kindOf p != "or" && hasEvent p && !triggers p)
    if ors.isEmpty || extras.isEmpty then c
    else
      let o := ors[0]!
      let keep := parts.filter
        (fun p => !(kindOf p == "or" && hasEvent p) && !(hasEvent p && !triggers p))
      let ex := andChain extras
      let mk := fun (b : Json) => andJson ex b
      let newOr := Json.mkObj
        [("kind", "or"), ("a", mk (field o "a")), ("b", mk (field o "b"))]
      spread (andChain (keep ++ ors.extract 1 ors.size ++ #[newOr]))

/-- `denote_occurs_at`: give a trigger stated without a position one, so the
    conclusion can be bounded by it.

    `EventLogged` IS `∃ i, EventLoggedAt … i`, so this asserts nothing new. But
    the bound `rescope` applies is stated against the trigger's index, and a
    trigger written `EventLogged` has none -- leaving the conclusion unbounded
    and the ordering it does have undrawn. Only a lone event premise is pinned:
    with one already positioned there is nothing to gain, and with two the bound
    is the later of them and the statement need not say which. -/
meta def pin (c : Json) : Json := Id.run do
  if kindOf c != "imp" then return c
  let parts := flattenAnd (field c "a") #[]
  if parts.any triggers then return c
  let hits := (List.range parts.size).filter
    (fun i => kindOf parts[i]! == "occurs" && kindOf (field parts[i]! "region") == "whole")
  let [i] := hits | return c
  let ev := parts[i]!
  let at' := (ev.setObjVal! "kind" (Json.str "occursAt")).setObjVal! "i" (Json.str "i")
  let pinned := Json.mkObj [("kind", "ex"), ("binder", "i"), ("c", at')]
  return Json.mkObj
    [("kind", "imp"), ("a", andChain (parts.set! i pinned)), ("b", field c "b")]

/-- `denote_not_and`: "these did not all happen" becomes one branch per premise.

    Applied only where BOTH sides speak about the trace. Splitting a condition
    away from the event `regroup` put it on would give it a branch of its own --
    "no trace in which this condition fails", which is not a set of traces.
    Kept together, the branch reads "no event of this description occurred". -/
meta partial def negate (c : Json) : Json :=
  if kindOf c == "and" && hasEvent (field c "a") && hasEvent (field c "b") then
    Json.mkObj [("kind", "or"), ("a", negate (field c "a")), ("b", negate (field c "b"))]
  else Json.mkObj [("kind", "not"), ("c", c)]

/-- `denote_imp`: an implication becomes two complete runs. -/
meta partial def expand (c : Json) : Json :=
  match kindOf c with
  | "imp" =>
      let a := expand (field c "a")
      let b := expand (field c "b")
      Json.mkObj [("kind", "or"), ("a", negate a),
                  ("b", Json.mkObj [("kind", "and"), ("a", a), ("b", b)])]
  | "not" => negate (expand (field c "c"))
  -- Not under a `∀`. The two runs `denote_imp` produces are runs of the DRAWN
  -- trace, and a binder over data has none to offer -- while the implication it
  -- quantifies is exactly what `denote_all_imp` turns into a forbidden shape,
  -- so expanding it here leaves the `∀` with no reading at all.
  | "all" => c
  | _ => mapKids expand c

/-- `denote_and_ex` / `denote_ex_and`: a witness is pulled out of a conjunction.
    Not out of a negation (`¬∃` is not `∃¬`) nor out of a named box. -/
meta partial def hoist (c : Json) : Json :=
  match kindOf c with
  | "and" =>
      let a := hoist (field c "a")
      let b := hoist (field c "b")
      if kindOf a == "ex" then
        a.setObjVal! "c" (hoist (Json.mkObj [("kind", "and"), ("a", field a "c"), ("b", b)]))
      else if kindOf b == "ex" then
        b.setObjVal! "c" (hoist (Json.mkObj [("kind", "and"), ("a", a), ("b", field b "c")]))
      else Json.mkObj [("kind", "and"), ("a", a), ("b", b)]
  | _ => mapKids hoist c


/-! ### The remaining rewrites, on the term

Ported from the JSON versions above, which they replace. The DECISIONS are still
made on the exported JSON -- `hasEvent`, `triggers`, `varsOf` -- so which
rewrite fires where is unchanged and only the construction moved. What is new is
that each one hands back a proof.

These are pure propositional rearrangements of `denote`, so the proof is found
by tactic per instance rather than by naming a lemma. A step whose proof does
not go through is SKIPPED, not assumed: the picture then shows the unrewritten
shape, which is still the certified one.
-/

private meta def claimHead (c : Expr) : Name :=
  match c.getAppFn with | .const n _ => n | _ => Name.anonymous

private meta def binArgs (c : Expr) : Expr × Expr :=
  let as := c.getAppArgs
  (as[as.size - 2]!, as[as.size - 1]!)

private meta def unArg (c : Expr) : Expr := c.getAppArgs[c.getAppArgs.size - 1]!

private meta partial def mapKidsExpr (f : Expr → MetaM Expr) (c : Expr) : MetaM Expr := do
  let as := c.getAppArgs
  match claimHead c with
  | ``Claim.and => let (a, b) := binArgs c; mkClaim ``Claim.and #[← f a, ← f b]
  | ``Claim.or => let (a, b) := binArgs c; mkClaim ``Claim.or #[← f a, ← f b]
  | ``Claim.imp => let (a, b) := binArgs c; mkClaim ``Claim.imp #[← f a, ← f b]
  | ``Claim.not => mkClaim ``Claim.not #[← f (unArg c)]
  | ``Claim.named => let (n, a) := binArgs c; mkClaim ``Claim.named #[n, ← f a]
  | ``Claim.cases =>
      mkClaim ``Claim.cases #[as[as.size - 5]!, as[as.size - 4]!, as[as.size - 3]!,
                              as[as.size - 2]!, ← f as[as.size - 1]!]
  | ``Claim.ex =>
      lambdaBoundedTelescope as[as.size - 1]! 1 fun xs body => do
        mkClaim ``Claim.ex #[as[as.size - 2]!, ← mkLambdaFVars xs (← f body)]
  | ``Claim.all =>
      lambdaBoundedTelescope as[as.size - 1]! 1 fun xs body => do
        mkClaim ``Claim.all #[as[as.size - 2]!, ← mkLambdaFVars xs (← f body)]
  | _ => return c

private meta partial def flattenAndExpr (c : Expr) (acc : Array Expr) : Array Expr :=
  if claimHead c == ``Claim.and then
    let (a, b) := binArgs c
    flattenAndExpr b (flattenAndExpr a acc)
  else acc.push c

private meta def andChainExpr (parts : Array Expr) : MetaM Expr := do
  if parts.isEmpty then return ← mkClaim ``Claim.check #[mkConst ``True]
  let mut p := parts[parts.size - 1]!
  for i in [1:parts.size] do p ← mkClaim ``Claim.and #[parts[parts.size - 1 - i]!, p]
  return p

/-- `hasEvent` and `triggers`, asked of the TERM. Exporting a subtree to JSON to
    find out whether it mentions an event costs a full render of every event in
    it, and these are asked once per `∧` node. -/
private meta def hasEventExpr (c : Expr) : Bool :=
  (c.find? fun e => e.isAppOf ``Claim.occurs || e.isAppOf ``Claim.occursAt
    || e.isAppOf ``Claim.absentBetween || e.isAppOf ``Claim.opaque).isSome

private meta def triggersExpr (c : Expr) : Bool :=
  (c.find? (·.isAppOf ``Claim.occursAt)).isSome

private meta partial def negateExpr (c : Expr) : MetaM Expr := do
  if claimHead c == ``Claim.and then
    let (a, b) := binArgs c
    if hasEventExpr a && hasEventExpr b then
      return ← mkClaim ``Claim.or #[← negateExpr a, ← negateExpr b]
  mkClaim ``Claim.not #[c]

private meta partial def expandExpr (c : Expr) : MetaM Expr := do
  match claimHead c with
  | ``Claim.imp =>
      let (a0, b0) := binArgs c
      let a ← expandExpr a0
      let b ← expandExpr b0
      mkClaim ``Claim.or #[← negateExpr a, ← mkClaim ``Claim.and #[a, b]]
  | ``Claim.not => negateExpr (← expandExpr (unArg c))
  | ``Claim.all => return c
  | _ => mapKidsExpr expandExpr c

private meta partial def hoistExpr (c : Expr) : MetaM Expr := do
  match claimHead c with
  | ``Claim.and =>
      let (a0, b0) := binArgs c
      let a ← hoistExpr a0
      let b ← hoistExpr b0
      if claimHead a == ``Claim.ex then
        let as := a.getAppArgs
        lambdaBoundedTelescope as[as.size - 1]! 1 fun xs body => do
          let inner ← hoistExpr (← mkClaim ``Claim.and #[body, b])
          mkClaim ``Claim.ex #[as[as.size - 2]!, ← mkLambdaFVars xs inner]
      else if claimHead b == ``Claim.ex then
        let bs := b.getAppArgs
        lambdaBoundedTelescope bs[bs.size - 1]! 1 fun xs body => do
          let inner ← hoistExpr (← mkClaim ``Claim.and #[a, body])
          mkClaim ``Claim.ex #[bs[bs.size - 2]!, ← mkLambdaFVars xs inner]
      else mkClaim ``Claim.and #[a, b]
  | _ => mapKidsExpr hoistExpr c

private meta partial def spreadExpr (c : Expr) : MetaM Expr := do
  let c ← mapKidsExpr spreadExpr c
  if claimHead c != ``Claim.and then return c
  let parts := flattenAndExpr c #[]
  let isOr := fun i => claimHead parts[i]! == ``Claim.or && hasEventExpr parts[i]!
  let ors := (List.range parts.size).filter isOr
  let extras := (List.range parts.size).filter
    (fun i => !isOr i && hasEventExpr parts[i]! && !triggersExpr parts[i]!)
  if ors.isEmpty || extras.isEmpty then return c
  let o := parts[ors.head!]!
  let keep := (List.range parts.size).filter
    (fun i => !isOr i && !(hasEventExpr parts[i]! && !triggersExpr parts[i]!))
  let ex ← andChainExpr ((extras.map (parts[·]!)).toArray)
  let (oa, ob) := binArgs o
  let newOr ← mkClaim ``Claim.or
    #[← mkClaim ``Claim.and #[ex, oa], ← mkClaim ``Claim.and #[ex, ob]]
  spreadExpr (← andChainExpr ((keep.map (parts[·]!)).toArray
    ++ (ors.tail.map (parts[·]!)).toArray ++ #[newOr]))

private meta def regroupExpr (c : Expr) : MetaM Expr := do
  if claimHead c != ``Claim.imp then return c
  let (a, b) := binArgs c
  let parts := flattenAndExpr a #[]
  let mut js : Array Json := #[]
  for p in parts do js := js.push (← jsonOfClaim p)
  let anchorIdx := (List.range parts.size).filter (fun i => hasEvent js[i]!)
  let floatIdx := (List.range parts.size).filter (fun i => !hasEvent js[i]!)
  if anchorIdx.isEmpty || floatIdx.isEmpty then return c
  let mut anchors : Array Expr := (anchorIdx.map (parts[·]!)).toArray
  let anchorJs : Array Json := (anchorIdx.map (js[·]!)).toArray
  let mut loose : Array Expr := #[]
  for i in floatIdx do
    let fv := varsOf js[i]!
    let score := fun (a : Json) =>
      let shared := ((varsOf a).toList.filter fv.contains).length
      if shared == 0 then 0 else 2 * shared + (if triggers a then 1 else 0)
    let scores := anchorJs.map score
    let best := scores.foldl max 0
    let winners := (List.range anchors.size).filter (fun k => scores[k]! == best)
    match winners with
    | [k] => if best > 0 then anchors := anchors.set! k (← mkClaim ``Claim.and #[anchors[k]!, parts[i]!])
             else loose := loose.push parts[i]!
    | _ => loose := loose.push parts[i]!
  mkClaim ``Claim.imp #[← andChainExpr (anchors ++ loose), b]

/-- Congruence: rewrite the children, and lift their proofs to the parent. -/
private meta partial def mapKidsRw (f : Expr → TermElabM Step) (c : Expr) : TermElabM Step := do
  let as := c.getAppArgs
  match claimHead c with
  | ``Claim.and =>
      let (a, b) := binArgs c
      let (a', ha) ← f a; let (b', hb) ← f b
      return (← mkClaim ``Claim.and #[a', b'], ← mkAppM ``Rewrites.and #[ha, hb])
  | ``Claim.or =>
      let (a, b) := binArgs c
      let (a', ha) ← f a; let (b', hb) ← f b
      return (← mkClaim ``Claim.or #[a', b'], ← mkAppM ``Rewrites.or #[ha, hb])
  | ``Claim.imp =>
      let (a, b) := binArgs c
      let (a', ha) ← f a; let (b', hb) ← f b
      return (← mkClaim ``Claim.imp #[a', b'], ← mkAppM ``Rewrites.imp #[ha, hb])
  | ``Claim.not =>
      let (a', ha) ← f (unArg c)
      return (← mkClaim ``Claim.not #[a'], ← mkAppM ``Rewrites.not #[ha])
  | ``Claim.named =>
      let (n, a) := binArgs c
      let (a', ha) ← f a
      return (← mkClaim ``Claim.named #[n, a'], ← mkAppM ``Rewrites.named #[n, ha])
  | ``Claim.cases =>
      let (a', _) ← f as[as.size - 1]!
      return (← mkClaim ``Claim.cases #[as[as.size - 5]!, as[as.size - 4]!,
                as[as.size - 3]!, as[as.size - 2]!, a'],
              ← mkAppM ``Rewrites.cases #[as[as.size - 5]!, as[as.size - 4]!,
                as[as.size - 3]!, as[as.size - 2]!, as[as.size - 1]!, a'])
  | ``Claim.ex =>
      lambdaBoundedTelescope as[as.size - 1]! 1 fun xs body => do
        let (b', hb) ← f body
        return (← mkClaim ``Claim.ex #[as[as.size - 2]!, ← mkLambdaFVars xs b'],
                ← mkAppM ``Rewrites.ex #[← mkLambdaFVars xs hb])
  | ``Claim.all =>
      lambdaBoundedTelescope as[as.size - 1]! 1 fun xs body => do
        let (b', hb) ← f body
        return (← mkClaim ``Claim.all #[as[as.size - 2]!, ← mkLambdaFVars xs b'],
                ← mkAppM ``Rewrites.all #[← mkLambdaFVars xs hb])
  | _ => return (c, ← rwRfl c)

/-- `denote_not_and`: "these did not all happen" becomes one branch per premise.
    Returns `Rewrites (not c) (negate c)`. -/
private meta partial def negateRw (c : Expr) : TermElabM Step := do
  if claimHead c == ``Claim.and then
    let (a, b) := binArgs c
    if hasEventExpr a && hasEventExpr b then
      let (na, ha) ← negateRw a
      let (nb, hb) ← negateRw b
      let step ← mkAppM ``denote_not_and #[a, b]
      let cong ← mkAppM ``Rewrites.or #[ha, hb]
      return (← mkClaim ``Claim.or #[na, nb], ← rwTrans step cong)
  let n ← mkClaim ``Claim.not #[c]
  return (n, ← rwRfl n)

/-- `denote_imp`: an implication becomes two complete runs. Composed from the
    lemmas rather than proved per instance -- the tactic does not scale to the
    classical steps this needs at depth, and failed on 34 of the corpus. -/
private meta partial def expandRw (c : Expr) : TermElabM Step := do
  match claimHead c with
  | ``Claim.imp =>
      let (a0, b0) := binArgs c
      let (a, ha) ← expandRw a0
      let (b, hb) ← expandRw b0
      let cong ← mkAppM ``Rewrites.imp #[ha, hb]
      let step ← mkAppM ``denote_imp #[a, b]
      let (na, hn) ← negateRw a
      let conj ← mkClaim ``Claim.and #[a, b]
      let cong2 ← mkAppM ``Rewrites.or #[hn, ← rwRfl conj]
      return (← mkClaim ``Claim.or #[na, conj],
              ← rwTrans (← rwTrans cong step) cong2)
  | ``Claim.not =>
      let (c', hc) ← expandRw (unArg c)
      let cong ← mkAppM ``Rewrites.not #[hc]
      let (nc, hn) ← negateRw c'
      return (nc, ← rwTrans cong hn)
  -- Not under a `∀`. The two runs `denote_imp` produces are runs of the DRAWN
  -- trace, and a binder over data has none to offer.
  | ``Claim.all => return (c, ← rwRfl c)
  | _ => mapKidsRw expandRw c

/-- `denote_and_ex` / `denote_ex_and`: a witness is pulled out of a conjunction.
    Not out of a negation (`¬∃` is not `∃¬`) nor out of a named box.

    Composed rather than searched for. The extractor knows which side the `∃`
    was on, because it just looked -- so it can name the lemma instead of asking
    a tactic to rediscover it in a goal the width of the whole claim. -/
private meta partial def hoistRw (c : Expr) : TermElabM Step := do
  match claimHead c with
  | ``Claim.and =>
      let (a0, b0) := binArgs c
      let (a, ha) ← hoistRw a0
      let (b, hb) ← hoistRw b0
      let cong ← mkAppM ``Rewrites.and #[ha, hb]
      if claimHead a == ``Claim.ex then
        let as := a.getAppArgs
        let f := as[as.size - 1]!
        let step ← mkAppM ``denote_ex_and #[b, f]
        let (inner, hi) ← lambdaBoundedTelescope f 1 fun xs body => do
          let (i, hi) ← hoistRw (← mkClaim ``Claim.and #[body, b])
          return (← mkLambdaFVars xs i, ← mkLambdaFVars xs hi)
        return (← mkClaim ``Claim.ex #[as[as.size - 2]!, inner],
                ← rwTrans (← rwTrans cong step) (← mkAppM ``Rewrites.ex #[hi]))
      if claimHead b == ``Claim.ex then
        let bs := b.getAppArgs
        let f := bs[bs.size - 1]!
        let step ← mkAppM ``denote_and_ex #[a, f]
        let (inner, hi) ← lambdaBoundedTelescope f 1 fun xs body => do
          let (i, hi) ← hoistRw (← mkClaim ``Claim.and #[a, body])
          return (← mkLambdaFVars xs i, ← mkLambdaFVars xs hi)
        return (← mkClaim ``Claim.ex #[bs[bs.size - 2]!, inner],
                ← rwTrans (← rwTrans cong step) (← mkAppM ``Rewrites.ex #[hi]))
      return (← mkClaim ``Claim.and #[a, b], cong)
  | _ => mapKidsRw hoistRw c

/-- Every free variable the claim mentions, by the name it will be DRAWN under. -/
private meta partial def claimFVarNames (e : Expr) (acc : Std.HashSet String) :
    MetaM (Std.HashSet String) := do
  match e with
  | .fvar id => return acc.insert (← id.getUserName).toString
  | .app f a => claimFVarNames a (← claimFVarNames f acc)
  | .lam _ t b _ | .forallE _ t b _ => claimFVarNames b (← claimFVarNames t acc)
  | .letE _ t v b _ => claimFVarNames b (← claimFVarNames v (← claimFVarNames t acc))
  | .mdata _ b => claimFVarNames b acc
  | .proj _ _ b => claimFVarNames b acc
  | _ => return acc

/-- Names under which the claim would draw TWO different things.

    Nothing else can see this. The certificate reads the event terms, so two
    distinct variables are distinct to it however they print; and the read-back
    compares a rendering against a rendering, so it agrees with itself on the
    same wrong spelling. It is a fault in the drawing that only shows up by
    asking the drawing this question directly. -/
private meta partial def nameCollisions (outer : Std.HashSet String) (c : Expr)
    (bad : Std.HashSet String) : MetaM (Std.HashSet String) := do
  let as := c.getAppArgs
  match claimHead c with
  | ``Claim.ex | ``Claim.all =>
      lambdaBoundedTelescope as[as.size - 1]! 1 fun xs body => do
        let n := (← xs[0]!.fvarId!.getUserName).toString
        let bad := if outer.contains n then bad.insert n else bad
        nameCollisions (outer.insert n) body bad
  | ``Claim.and | ``Claim.or | ``Claim.imp =>
      let (x, y) := binArgs c
      nameCollisions outer y (← nameCollisions outer x bad)
  | ``Claim.not | ``Claim.named => nameCollisions outer (unArg c) bad
  | ``Claim.cases => nameCollisions outer (unArg c) bad
  | _ => return bad

/-- The subclaims a structural rewrite treats as opaque: everything that is not
    an `∧`, `∨`, `→` or `¬` it rearranges. -/
private meta partial def structAtoms (c : Expr) (acc : Array Expr) : Array Expr :=
  match claimHead c with
  | ``Claim.and | ``Claim.or | ``Claim.imp =>
      let (x, y) := binArgs c
      structAtoms y (structAtoms x acc)
  | ``Claim.not => structAtoms (unArg c) acc
  | _ => if acc.contains c then acc else acc.push c

/-- Prove that a rewrite said the same thing. A step that cannot be proved is
    dropped, so the failure mode is an unrewritten picture, never a false one.

    The atoms are ABSTRACTED first. These rewrites only rearrange `∧`/`∨`, so
    the fact to prove is about the structure -- but `simp [Claim.denote]` on the
    concrete claim expands every event and check underneath it, handing the
    search a goal hundreds of nodes wide to establish something with a handful
    of atoms in it. Generalised, the goal is the size of the rearrangement. -/
private meta def proveRewrite (a b : Expr) : TermElabM (Option Expr) := do
  if a == b then return some (← rwRfl a)
  let tac ← `(tactic| (intro tr; simp only [Claim.denote]; grind))
  let run : Expr → TermElabM (Option Expr) := fun goal => try
      Term.withoutErrToSorry do
        let mvar ← mkFreshExprSyntheticOpaqueMVar goal
        let (rem, _) ← runTactic mvar.mvarId! tac
        let pf ← instantiateMVars mvar
        if rem.isEmpty && !pf.hasSorry && !pf.hasExprMVar then pure (some pf) else pure none
    catch _ => pure none
  let atoms := structAtoms b (structAtoms a #[])
  let ty ← inferType a
  let abstracted ←
    withLocalDeclsD (atoms.mapIdx fun i _ => (Name.mkSimple s!"c{i}", fun _ => pure ty))
      fun xs => do
        -- One pass with a lookup, not one pass per atom: a claim wide enough to
        -- need this has enough atoms for the difference to be the whole cost.
        let table : Std.HashMap Expr Expr :=
          (Array.range atoms.size).foldl (fun m i => m.insert atoms[i]! xs[i]!) {}
        let sub := fun (e : Expr) => e.replace fun s => table[s]?
        match ← run (← mkAppM ``Rewrites #[sub a, sub b]) with
        | some pf => return some (mkAppN (← mkLambdaFVars xs pf) atoms)
        | none => return none
  match abstracted with
  | some pf => return some pf
  -- An atom the two sides do not share leaves the general form unprovable.
  | none => run (← mkAppM ``Rewrites #[a, b])

/-- `denote_and_or`: a choice standing beside a REQUIREMENT at the same event
    cannot be drawn -- both arrive as arrows, and nothing says which is which.
    Distributing the choice over that requirement gives one complete alternative
    per branch.

    One distribution at a time, each proved as it is made. Done in one go the
    fact to prove is a propositional equivalence over every atom at once, and
    the search for it is exponential in their number -- 25 of DANE's 37 seconds.
    Step by step each goal is the size of the one move. -/
private meta partial def spreadRw (c0 : Expr) : TermElabM Step := do
  let (c, hk) ← mapKidsRw spreadRw c0
  if claimHead c != ``Claim.and then return (c, hk)
  let parts := flattenAndExpr c #[]
  let isOr := fun i => claimHead parts[i]! == ``Claim.or && hasEventExpr parts[i]!
  let ors := (List.range parts.size).filter isOr
  let extras := (List.range parts.size).filter
    (fun i => !isOr i && hasEventExpr parts[i]! && !triggersExpr parts[i]!)
  if ors.isEmpty || extras.isEmpty then return (c, hk)
  let o := parts[ors.head!]!
  let keep := (List.range parts.size).filter
    (fun i => !isOr i && !(hasEventExpr parts[i]! && !triggersExpr parts[i]!))
  let ex ← andChainExpr ((extras.map (parts[·]!)).toArray)
  let (oa, ob) := binArgs o
  let newOr ← mkClaim ``Claim.or
    #[← mkClaim ``Claim.and #[ex, oa], ← mkClaim ``Claim.and #[ex, ob]]
  let c' ← andChainExpr ((keep.map (parts[·]!)).toArray
    ++ (ors.tail.map (parts[·]!)).toArray ++ #[newOr])
  match ← proveRewrite c c' with
  | none =>
      logWarning "DYVis: could not prove a `spread` step; drawing the shape without it"
      return (c, hk)
  | some h₁ =>
      let (c'', h₂) ← spreadRw c'
      return (c'', ← rwTrans (← rwTrans hk h₁) h₂)

private meta def rwStep (what : String) (f : Expr → MetaM Expr) (c : Expr) :
    TermElabM Step := do
  let c' ← f c
  match ← proveRewrite c c' with
  | some h => return (c', h)
  | none =>
      logWarning s!"DYVis: could not prove the `{what}` rewrite; drawing the \
        shape without it"
      return (c, ← rwRfl c)

/-- Every rewrite that has been moved onto the term, composed. What is left in
    the JSON chain is what has not been moved yet. -/
public meta def normaliseClaim (c0 : Expr) : TermElabM Step := do
  let (c1, ha) ← uncurryExpr c0
  let (c2, hb) ← pinExpr c1
  let mut c := c2
  let mut h ← rwTrans ha hb
  let (c3, hr) ← rwStep "regroup" regroupExpr c
  c := c3; h ← rwTrans h hr
  let (c4, he) ← expandRw c
  c := c4; h ← rwTrans h he
  let (c5, hh) ← hoistRw c
  c := c5; h ← rwTrans h hh
  let (c6, hsp) ← spreadRw c
  c := c6; h ← rwTrans h hsp
  return (c, h)

/-- How much of the statement the translation did NOT understand. Certification
    cannot see this: `denote (opaque p) tr` is `p`, so giving up is faithful and
    certifies happily. Informativeness is this number being zero. -/
meta partial def opaqueCount (c : Json) : Nat :=
  (if kindOf c == "opaque" then 1 else 0) +
    ((kids c).map (fun k => opaqueCount (field c k))).foldl (· + ·) 0

meta partial def hasNot (c : Json) : Bool :=
  kindOf c == "not" || (kids c).any (fun k => hasNot (field c k))

meta partial def eventPremises (c : Json) : List Json :=
  (if kindOf c == "occursAt" then [field c "i"] else []) ++
    (kids c).flatMap (fun k => eventPremises (field c k))

meta partial def flattenOr (c : Json) (acc : Array Json) : Array Json :=
  if kindOf c == "or" then flattenOr (field c "b") (flattenOr (field c "a") acc)
  else acc.push c

/-- Narrow every whole-run region to the trigger.

    Every leaf that CARRIES a region is narrowed, which is exactly the set
    `denote_bound` has a case for. Restricting this to `occurs` left a whole-run
    `stored` unplaced, and an unplaced member dissolves the box around its
    conjunction -- so the state entry ended up drawn on no run at all, present
    in the picture and reachable from nothing. -/
meta partial def narrow (i : Json) (c : Json) : Json :=
  let c := if ["occurs", "stored", "knows"].contains (kindOf c)
              && kindOf (field c "region") == "whole" then
      c.setObjVal! "region"
        (Json.mkObj [("kind", "before"), ("i", i), ("weak", Json.bool true)])
    else c
  mapKids (narrow i) c

/-- A claim that the truncation cannot cost us: no `¬`, and every event it
    speaks of is pinned to the index the bound is taken against, so it is inside
    the prefix by construction (`Trace.EventLoggedAt_prefix`). An unpositioned
    `occurs` is not, its witness being anywhere in the run. -/
meta partial def survivesTruncation (i : Json) (c : Json) : Bool :=
  match kindOf c with
  | "occursAt" | "storedAt" => field c "i" == i && kindOf (field c "region") == "whole"
  | "check" => true
  | "not" | "opaque" | "occurs" | "stored" | "absentBetween" => false
  | _ => !(kids c).isEmpty && (kids c).all (fun k => survivesTruncation i (field c k))

/-- `conclusion_bounded_by_trigger`: a conclusion stated over the whole run is
    bounded by its trigger, since the theorem also holds of the run truncated
    just after it.

    Three side conditions, which is why this belongs here and not in the
    renderer. An absence would be WEAKENED by narrowing. Every event premise
    must survive the truncation, so with more than one the bound is the last of
    them and the statement need not say which.

    And the third, which the other two hide: the lemma bounds the WHOLE claim
    against ONE `n`, so a disjunction cannot have some branches narrowed and
    others not unless the others are ruled out at the truncation. Otherwise the
    branch that holds at the prefix and the branch that holds at the full run
    are different ones, and neither of the two DRAWN branches follows. What
    rules a branch out is the trigger: `¬(the premise the bound is taken
    against)` is false on a prefix that contains it. So every branch left alone
    has to be exactly that -- a denial of something pinned to `i` -- and a
    branch merely carrying a `∄` is not, which is what the `¬`-anywhere test
    used to accept by accident. -/
meta partial def rescope (c : Json) : Json := Id.run do
  let ds := flattenOr c #[]
  let idx := fun (d : Json) =>
    if hasNot d then none else match eventPremises d with | [i] => some i | _ => none
  let is := (ds.toList.filterMap idx).eraseDups
  let [i] := is | return c
  if !(ds.all (fun d => (idx d).isSome ||
                        (kindOf d == "not" && survivesTruncation i (field d "c")))) then
    return c
  let out := ds.map (fun d => if (idx d).isSome then narrow i d else d)
  let mut p := out[out.size - 1]!
  for k in [1:out.size] do
    p := Json.mkObj [("kind", "or"), ("a", out[out.size - 1 - k]!), ("b", p)]
  return p

section RescopeProbe

private meta def whole : Json := Json.mkObj [("kind", "whole")]
private meta def trig : Json :=
  Json.mkObj [("kind", "occursAt"), ("ev", "T"), ("i", "i"), ("region", whole)]
private meta def occ (ev : String) : Json :=
  Json.mkObj [("kind", "occurs"), ("ev", ev), ("region", whole)]

/-- `trigger ∧ occurs X` beside whatever branch is given, run through `rescope`.
    The corpus only ever offers the vacuous branch here; the second probe is the
    shape that would make the mixture unsound, and no theorem produces it today.
    That is exactly why it needs pinning: the guard has nothing else holding it. -/
private meta def rescopeProbe (other : Json) : String :=
  let d := Json.mkObj [("kind", "and"), ("a", trig), ("b", occ "X")]
  let c := Json.mkObj [("kind", "or"), ("a", other), ("b", d)]
  if (rescope c).compress == c.compress then "left alone" else "narrowed"

/-- info: "narrowed" -/
#guard_msgs in
#eval rescopeProbe (Json.mkObj [("kind", "not"), ("c", trig)])

/-- info: "left alone" -/
#guard_msgs in
#eval rescopeProbe (Json.mkObj [("kind", "and"), ("a", trig),
                                ("b", Json.mkObj [("kind", "not"), ("c", occ "Y")])])

end RescopeProbe

/-- Open a theorem's binders down to its first premise, so that what remains is
    the statement itself: premises implying conclusion, in the theorem's own
    curried shape.

    Both the JSON and the certified term are built from THIS body, so there is
    one object rather than two. They were once built separately, and the
    certificate silently covered only the conclusion while the premises -- and
    every branch drawn from them -- went unchecked.

    `Reachable` is opened rather than kept: the claim is about runs the attacker
    can schedule, so the certificate may assume it. -/
private meta partial def openStatement {α : Type}
    (type : Expr) (fvars : Array Expr) (k : Array Expr → Expr → TermElabM α) : TermElabM α := do
  match type with
  | .forallE n d b bi =>
      let ambient := match d.getAppFnArgs with
        | (``DY.Trace.Reachable, _) => true
        | _ => false
      if !b.hasLooseBVars && !ambient && (← isProp d) then k fvars type
      else withLocalDecl n bi d fun x => openStatement (b.instantiate1 x) (fvars.push x) k
  | _ => k fvars type

/-- The `ExecTrace` the statement is about. An abbrev, so match the head
    constant rather than the printed name. -/
private meta def traceArg? (args : Array Expr) : MetaM (Option Expr) := do
  let mut tr := none
  for a in args do
    if let .const ``DY.Trace _ := (← whnfR (← inferType a)).getAppFn then tr := some a
  return tr

/-! ## Where an event can be emitted

An event node names a constructor, and the model the theorem quantifies over is
a `ReachabilityConfig`; the only code that can run under it is the transitive
closure of that config. Intersecting the two gives the sites a reader can be
sent to, and rules out the emitters of protocols this theorem says nothing
about.

The closure is an OVER-approximation -- a branch a guard never takes still
counts -- so the list can name a site no run reaches, but it cannot MISS one.
That is the safe direction: a reader who is shown a site can check it, whereas
one who is shown none concludes there are none. -/

/-- A module's source file, relative to the workspace root. Right for modules of
    the root package; a dependency's modules live under its own directory. -/
private meta def modulePath (m : Name) : String :=
  String.intercalate "/" (m.components.map toString) ++ ".lean"

/-- The file a declaration is in. A theorem being traced is usually in the
    module doing the tracing, and `getModuleIdxFor?` answers only for IMPORTED
    declarations, so the module being elaborated is the fallback. -/
private meta def declFile (name : Name) : CoreM String := do
  return modulePath ((moduleOf (← getEnv) name).getD (← getMainModule))

/-- Every declaration of the model (see `dyvis.model`) the config can reach. -/
private meta def modelClosure (root : Name) : CoreM NameSet := do
  let env ← getEnv
  let opts ← getOptions
  let mut seen : NameSet := {}
  let mut work := [root]
  while !work.isEmpty do
    let n :: rest := work | break
    work := rest
    if seen.contains n then continue
    seen := seen.insert n
    if let some v := (env.find? n).bind (·.value?) then
      for c in v.getUsedConstants do
        if !seen.contains c && ownModule env opts c then work := c :: work
  return seen

/-- `ctor ↦ the declarations under `root` whose body mentions it`. Sorted, since
    a set that reordered between runs would churn the approval baselines.

    The declaration is named, not located: a line number recorded here is one
    the source can move out from under, so the reader would be sent confidently
    to the wrong place. The name is resolved against the file as it is now. -/
private meta def emittersFor (root : Name) (wanted : Array String) : CoreM Json := do
  let env ← getEnv
  let closure ← modelClosure root
  let want : NameSet := wanted.foldl (fun s c => s.insert c.toName) {}
  let mut hits : NameMap NameSet := {}
  for n in closure.toList do
    if let some v := (env.find? n).bind (·.value?) then
      for c in v.getUsedConstants do
        if want.contains c then
          hits := hits.insert c (((hits.find? c).getD {}).insert n)
  let mut out := #[]
  for c in want.toList do
    let mut locs := #[]
    for d in ((hits.find? c).getD {}).toList do
      if let some m := moduleOf env d then
        locs := locs.push (Json.mkObj
          [("decl", Json.str d.toString), ("file", Json.str (modulePath m))])
    if !locs.isEmpty then out := out.push (c.toString, Json.arr locs)
  return Json.mkObj out.toList

/-- Every string stored under `key`, anywhere in a claim. -/
private meta partial def stringsAt (key : String) (j : Json) : Array String :=
  match j with
  | .arr xs => xs.foldl (fun acc x => acc ++ stringsAt key x) #[]
  | .obj kvs => kvs.foldl (fun acc k v =>
      if k == key then (match v with | .str s => acc.push s | _ => acc)
      else acc ++ stringsAt key v) #[]
  | _ => #[]

/-- The constructors the claim's event nodes name. -/
private meta def ctorsIn (j : Json) : Array String := stringsAt "ctor" j

/-- The model the theorem quantifies over: the config argument of its own
    `Trace.Reachable` premise, so a proof-side theorem with no such premise
    simply has no sites rather than borrowing another theorem's. -/
private meta def reachabilityRoot (name : Name) : MetaM (Option Name) := do
  let info ← getConstInfo name
  match info.type.find? (·.isAppOf ``DY.Trace.Reachable) with
  | some e =>
      let args := e.getAppArgs
      if args.size < 2 then return none
      match args[args.size - 2]!.getAppFn with
      | .const c _ => return some c
      | _ => return none
  | none => return none

/-- A theorem becomes ONE claim: its premises implying its conclusion. The
    diagram then shows both ways a trace can satisfy it -- by failing a premise,
    or by meeting the conclusion -- rather than presenting the premises as
    something that simply happened. -/

-- Traced-but-not-yet-written claims. A file is elaborated in one process, so
-- this collects whatever the file traced before it asks for a write.
public meta initialize traced : IO.Ref (Array Json) ← IO.mkRef #[]

/-- Emit `<thm>.claim`, the shape proposed for the theorem, and `<thm>.isClaim`,
    a proof that the theorem IS that shape.

    The proof is `Iff.rfl`, so it holds only when the claim is the theorem's own
    proposition -- not merely equivalent to it. Where that fails the declaration
    is still emitted, proved by `sorry`, and the caller is told: a gap that is
    recorded is worth more than one that is silently skipped. -/
meta def emitCertificate (name : Name) : TermElabM (Except String (Bool × Json)) := do
  let info ← getConstInfo name
  openStatement info.type #[] fun args body => do
    let some tr ← traceArg? args
      | return .error s!"{name}: no ExecTrace argument -- not a trace property"
    -- The claim CERTIFIED is the normalised one, so `isClaim` is about the shape
    -- that gets drawn. `raw` is defeq to the statement, and each rewrite carries
    -- its own proof, so the composition is the whole certificate.
    -- Seeded with the theorem's OWN parameter names. Freshening only knew about
    -- binders the claim introduces, so an `∃ connId` inside collided with the
    -- `connId` in the signature and two different values drew as one name.
    let mut taken : Std.HashSet String := {}
    for a in args do
      if a.isFVar then taken := taken.insert (← a.fvarId!.getUserName).toString
    let raw := (← toClaimExpr tr body taken {} false taken).1
    let collisions ← nameCollisions (← claimFVarNames raw {}) raw {}
    unless collisions.isEmpty do
      logWarning s!"{name}: {String.intercalate ", " collisions.toList} names two \
        different things in this drawing"
    let (claim, h) ← normaliseClaim raw
    let rawDenoted ← mkAppM ``Claim.denote #[raw, tr]
    let ok ← isDefEq body rawDenoted
    let claimTy ← mkForallFVars args (← inferType claim)
    let claimVal ← mkLambdaFVars args claim
    let dv : DefinitionVal :=
      { name := name ++ `claim, levelParams := info.levelParams,
        type := claimTy, value := claimVal, hints := .abbrev, safety := .safe }
    addDecl (.defnDecl dv)
    -- `isClaim` cites `<thm>.claim` by NAME rather than inlining the tree, so a
    -- reader sees the two things being equated instead of a wall of term. It is
    -- an `abbrev`, so this is defeq to the inlined form and the proof already
    -- built still checks. The left side cannot be named the same way: it is the
    -- TYPE of the theorem, and nothing denotes that but the type itself.
    let claimRef := mkAppN (mkConst (name ++ `claim)
      (info.levelParams.map Level.param)) args
    let denoted ← mkAppM ``Claim.denote #[claimRef, tr]
    let iff ← mkAppM ``Iff #[body, denoted]
    let proof ← if ok then mkAppM' h #[tr]
                else mkAppOptM ``sorryAx #[iff, some (.const ``Bool.false [])]
    let certTy ← mkForallFVars args iff
    let certVal ← mkLambdaFVars args proof
    let tv : TheoremVal :=
      { name := name ++ `isClaim, levelParams := info.levelParams,
        type := certTy, value := certVal }
    addDecl (.thmDecl tv)
    return .ok (ok, rescope (← jsonOfClaim claim))

@[command_elab traceClaimCmd]
public meta def elabTraceClaim : CommandElab := fun stx => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload stx[1]!
  -- One pass: the JSON comes back from the same walk that built and proved the
  -- claim. Asking for them separately did every rewrite, and every proof, twice.
  match ← liftTermElabM (emitCertificate name) with
  | .error m => logError m
  | .ok (certified, claim) => do
      unless certified do
        logWarning s!"{name}: claim is NOT the theorem -- {name}.isClaim is sorry"
      let holes := opaqueCount claim
      if holes > 0 then
        logWarning s!"{name}: {holes} part(s) of the statement not understood; \
          the certificate covers them as opaque"
      -- An inductive predicate's box is tied to its name by a theorem rather
      -- than by defeq, so `isClaim` does not reach it. These are generated, so
      -- no reader has seen them: the axiom check is done here rather than left
      -- to a `#print axioms` line nobody can write for a name that does not
      -- exist until the trace runs.
      let ties := (stringsAt "tie" claim).toList.eraseDups
      for t in ties do
        let ax ← liftCoreM (collectAxioms t.toName)
        if ax.contains ``sorryAx then
          logError s!"{name}: characterisation {t} rests on sorryAx -- the \
            drawing is not evidence about this theorem"
        else
          logInfo s!"{name}: drawn via proved characterisation {t}; \
            depends on axioms: [{String.intercalate ", " (ax.toList.map toString)}]"
      let emitters ← match ← liftTermElabM (reachabilityRoot name) with
        | some root => liftCoreM (emittersFor root (ctorsIn claim))
        | none => pure (Json.mkObj [])
      traced.modify (·.push (Json.mkObj
        [("name", name.toString), ("certified", Json.bool certified),
         ("opaque", Json.num holes), ("claim", claim),
         ("file", Json.str (← liftCoreM (declFile name))),
         ("emitters", emitters)]))
      logInfo s!"traced {name}{if certified then " (certified" else " (SORRY"}\
        {if holes > 0 then s!", {holes} opaque)" else ")"}"

/-- `path` under the root of the package the current module belongs to: the
    file name minus the module's own path. So a dependency's module writes into
    its own package even when `lake build` runs in the project that requires it.
    Falls back to the working directory when the two do not line up. -/
private meta def underPackageRoot (path : String) : CommandElabM System.FilePath := do
  let rel := modulePath (← getMainModule)
  let file ← getFileName
  let root := (file.dropEnd rel.length).copy
  if file.endsWith rel && !root.isEmpty then
    return System.FilePath.mk root / path
  return path

@[command_elab traceClaimsToFileCmd]
public meta def elabTraceClaimsToFile : CommandElab := fun stx => do
  let path := stx[1]!.isStrLit?.getD "claims.json"
  let out ← traced.get
  if out.isEmpty then
    logWarning s!"nothing traced -- {path} not written"
  else
    let file ← underPackageRoot path
    if let some dir := file.parent then
      IO.FS.createDirAll dir
    IO.FS.writeFile file (Json.arr out).pretty
    traced.set #[]
    logInfo s!"wrote {out.size} claims to {path}"

end DYVis.Theorem.Extract
