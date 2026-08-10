/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.AppBuilder
public import Lean.Meta.Transform
import Lean.Meta.WHNF
import Lean.Meta.KAbstract
import Lean.AddDecl
import Init.Tactics

/-!
# Certificates for nested inductive declarations

A nested inductive declaration is compiled by eliminating the nesting into a mutual *model* and
rewriting the model's declarations back into the nested presentation. The rewrite is untrusted:
this module produces the model, the four bridge components relating each auxiliary copy to the type
it stands for, the surrogate constructors and recursors presenting the nested declaration as
definitions over the model, and a proof of every computation rule the declaration states. The
proofs are ordinary terms, so checking them is ordinary type checking and adds nothing to the
trusted code base.

There are two ways to run this. `tests/elab/nested_inductive_certificate.lean` certifies every
nested inductive reachable from `import Lean` after the fact, which covers all of core.
`environment::add_inductive` certifies each declaration as it makes it, so the check also covers
whatever is being compiled, `Init.Prelude` included. There is no way to turn it off: the recursors
the kernel declares come from the certificate, so a nested inductive without one cannot be declared.

Occurrence discovery is purely syntactic, with no `whnf`, and matches an already-created auxiliary
type by structural equality. It is also what decides which declarations are routed here rather than
checked by the kernel itself, so there is one definition of what counts as an occurrence rather than
two that have to agree.
-/

namespace Lean.Meta

namespace NestedGen

/-- The auxiliary types created so far, keyed by the nested application with parameters abstracted. -/
structure State where
  /-- The declaration being built: the original types, then auxiliary copies appended. -/
  types : Array InductiveType
  /-- `(I Ds, auxName)` pairs; `I Ds` mentions the canonical parameter fvars. -/
  aux   : Array (Expr × Name) := #[]
  /-- Counter for `mk_unique_name`. -/
  next  : Nat := 1

abbrev M := StateRefT State MetaM

/-- Fresh name of the form `_nested.<J>_<i>` not already used. -/
def mkUniqueName (base : Name) : M Name := do
  let env ← getEnv
  repeat
    let s ← get
    let r := base.appendAfter (toString s.next)
    set { s with next := s.next + 1 }
    if !(env.contains r) && !((← get).types.any (·.name == r)) then
      return r
  unreachable!

/--
Is `e` a nested occurrence, i.e. `I args` with `I` an inductive not being declared here and one
of its first `nparams` arguments mentioning a type that is being declared? This is the same test
`decl_has_nested` applies in the kernel to route the declaration here in the first place.
-/
def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  unless e.isApp do return none
  let .const n _ := e.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? n | return none
  let args := e.getAppArgs
  if iv.numParams > args.size then return none
  let declared := (← get).types.map (·.name)
  let mut nested := false
  for i in [0 : iv.numParams] do
    if args[i]!.hasLooseBVars then
      throwError "invalid nested inductive datatype '{n}', parameters cannot contain local variables"
    if args[i]!.find? (fun t => match t with
        | .const m _ => declared.contains m
        | _ => false) |>.isSome then
      nested := true
  return if nested then some iv else none

/-- Replace the canonical parameters in `e` by `As`. -/
def replaceParams (e : Expr) (params As : Array Expr) : Expr :=
  e.replace fun t => match t with
    | .fvar _ => match As.idxOf? t with
                 | some i => some params[i]!
                 | none => none
    | _ => none

/--
Strip the leading `∀` binders of `e` and substitute `args` for them. Mirrors
`instantiate_pi_params`, which is purely syntactic; `instantiateForall` would `whnf` its way to each
binder instead, and the certificate has to be about the declaration the kernel actually builds.
-/
def instantiatePiParams (e : Expr) (args : Array Expr) : MetaM Expr := do
  let mut body := e
  for _ in args do
    let .forallE _ _ b _ := body
      | throwError "expected {args.size} leading binders in {e}"
    body := b
  return body.instantiateRev args

/--
Replace one nested occurrence, creating auxiliary copies of every type in the occurrence's
mutual block if they do not exist yet.
-/
def replaceIfNested (params As : Array Expr) (lvls : List Level) (e : Expr) :
    M (Option Expr) := do
  let some iv ← isNestedInductiveApp? e | return none
  let args := e.getAppArgs
  let .const iName ilvls := e.getAppFn | return none
  let np := iv.numParams
  let iAs := mkAppN (mkConst iName ilvls) args[0:np]
  let key := replaceParams iAs params As
  -- already created?
  if let some (_, auxName) := (← get).aux.find? (fun (k, _) => k == key) then
    return some (mkAppN (mkAppN (mkConst auxName lvls) As) args[np:])
  -- otherwise copy every type of the occurrence's mutual block
  let mut result := none
  for jName in iv.all do
    let some (.inductInfo jv) := (← getEnv).find? jName | throwError "not an inductive: {jName}"
    let jAs := mkAppN (mkConst jName ilvls) args[0:np]
    let auxJ ← mkUniqueName (`_nested ++ jName)
    let jType := jv.type.instantiateLevelParams jv.levelParams ilvls
    let auxJType ← mkForallFVars As (← instantiatePiParams jType args[0:np])
    modify fun s => { s with aux := s.aux.push (replaceParams jAs params As, auxJ) }
    if jName == iName then
      result := some (mkAppN (mkAppN (mkConst auxJ lvls) As) args[np:])
    let mut ctors := #[]
    for cName in jv.ctors do
      let some ci := (← getEnv).find? cName | throwError "missing constructor {cName}"
      let cType := ci.type.instantiateLevelParams ci.levelParams ilvls
      let cType ← mkForallFVars As (← instantiatePiParams cType args[0:np])
      ctors := ctors.push { name := cName.replacePrefix jName auxJ, type := cType }
    modify fun s => { s with
      types := s.types.push { name := auxJ, type := auxJType, ctors := ctors.toList } }
  return result

/-- Replace every nested occurrence in `e`. Mirrors `replace_all_nested`. -/
def replaceAllNested (params As : Array Expr) (lvls : List Level) (e : Expr) : M Expr :=
  transform e (pre := fun t => do
    match ← replaceIfNested params As lvls t with
    | some r => return .done r
    | none   => return .continue)

/--
Eliminate nested occurrences from `d`, returning the model declaration and the
`(I Ds, auxName)` correspondence. Mirrors `elim_nested_inductive_fn::operator()`.
-/
def withElimNested {α} (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (k : Array InductiveType → Array (Expr × Name) → Array Expr → MetaM α) : MetaM α := do
  let lvls := lparams.map Level.param
  let types := types.toArray
  if types.isEmpty then throwError "empty inductive declaration"
  forallBoundedTelescope types[0]!.type nparams fun params _ => do
    if params.size != nparams then throwError "not enough parameters"
    let go : M Unit := do
      let mut qhead := 0
      repeat
        if qhead ≥ (← get).types.size then break
        let it := (← get).types[qhead]!
        let mut newCtors := #[]
        for c in it.ctors do
          -- re-create the parameters per constructor, as the kernel does
          let t ← forallBoundedTelescope c.type nparams fun As body => do
            mkForallFVars As (← replaceAllNested params As lvls body)
          newCtors := newCtors.push { c with type := t }
        modify fun s => { s with
          types := s.types.set! qhead { it with ctors := newCtors.toList } }
        qhead := qhead + 1
    let (_, st) ← go.run { types }
    k st.types st.aux params

end NestedGen


/-! ## Bridges: `pack` (PACK layer), generated from the model -/

namespace NestedGen

/-- Rename every declaration of a model so it can be added alongside the original. -/
def renameModel (types : Array InductiveType) (aux : Array (Expr × Name)) (pre : Name) :
    Array InductiveType × Array (Expr × Name) :=
  let ren : Name → Name := (pre ++ ·)
  let names := types.map (·.name)
  let fix (e : Expr) : Expr := e.replace fun t => match t with
    | .const n us => if names.contains n then some (.const (ren n) us) else none
    | _ => none
  let types := types.map fun t =>
    { name := ren t.name, type := fix t.type,
      ctors := t.ctors.map fun c => { name := ren c.name, type := fix c.type } }
  (types, aux.map fun (k, n) => (fix k, ren n))

/--
Beta-reduce everywhere, without a monad.

Occurrences are matched structurally, and whether a redex survives depends on how a term was built:
the elimination opens and recloses binders, which reduces, while the declaration a key came from did
not. Normalising both sides is what keeps a field type recognisable as the occurrence it is regardless
of which route produced it.
-/
partial def betaAll (e : Expr) : Expr :=
  match e.headBeta with
  | .app f a         => (Expr.app (betaAll f) (betaAll a)).headBeta
  | .lam n t b i     => .lam n (betaAll t) (betaAll b) i
  | .forallE n t b i => .forallE n (betaAll t) (betaAll b) i
  | .letE n t v b nd => .letE n (betaAll t) (betaAll v) (betaAll b) nd
  | .mdata d b       => .mdata d (betaAll b)
  | .proj s i b      => .proj s i (betaAll b)
  | e                => e

/-- The aux name registered for the nested occurrence `e`, if any. -/
def auxFor? (aux : Array (Expr × Name)) (params As : Array Expr) (e : Expr) : Option (Name × Nat) := do
  let iv ← match e.getAppFn with
    | .const _ _ => some ()
    | _ => none
  let _ := iv
  let args := e.getAppArgs
  for (k, n) in aux do
    -- keys are `I Ds` with canonical params; rebuild the same prefix from `e`
    let kArgs := k.getAppArgs
    if k.getAppFn == e.getAppFn && kArgs.size ≤ args.size then
      if betaAll (replaceParams (mkAppN e.getAppFn args[0:kArgs.size]) params As) == betaAll k then
        return (n, kArgs.size)
  none

end NestedGen

namespace NestedGen

/-- Strip leading binders; used to see through reflexive occurrences. -/
def stripBinders : Expr → Expr
  | .forallE _ _ b _ => stripBinders b
  | e => e

/--
The universe the instances of a possibly index-taking type former live in: for `Fam α` this is
the level of `Fam α is`, not of `Nat → Type`.
-/
def familyLevel (e : Expr) : MetaM Level := do
  forallTelescope (← inferType e) fun _ b => do
    match ← whnf b with
    | .sort u => return u
    | b => throwError "expected a sort codomain for {e}, got {b}"

/--
Open the index telescope of the model type `t` at parameters `As`, running `k` with the index
binders and the applied type `t As is`. Both mention the fresh index fvars, so anything derived
from them has to be abstracted before leaving `k`.
-/
def withModelIndices (t : InductiveType) (As : Array Expr) (lvls : List Level)
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  forallTelescope (← instantiateForall t.type As) fun is _ =>
    k is (mkAppN (mkAppN (mkConst t.name lvls) As) is)

/--
Extend a congruence by one constructor argument. `mkCongr` needs the partially applied
constructor to be a non-dependent function, which an index-determining field is not; where the
argument is unchanged `congrFun` does the same job and tolerates the dependency.
-/
def congrStep (acc arg p : Expr) : MetaM Expr :=
  if p.isAppOf ``Eq.refl then mkCongrFun acc arg else mkCongr acc p

/-- The indices `cApp`'s type carries, i.e. the ones this constructor application determines. -/
def ctorIndices (nparams : Nat) (cApp : Expr) : MetaM (Array Expr) := do
  let ty ← whnf (← inferType cApp)
  return ty.getAppArgs.extract nparams ty.getAppArgs.size

/-- Name of the `pack` function for the auxiliary type `auxName`. -/
def packName (auxName : Name) : Name := auxName ++ `pack

/--
Functorial action of the elimination's rewriting: given a field of type `origTy` and a term `x`
of that type, produce the corresponding term at the rewritten type. This is the PI/NESTED
dispatch: nested occurrences are packed, binders are mapped pointwise, anything else passes
through unchanged.
-/
partial def packField (aux : Array (Expr × Name)) (params As : Array Expr)
    (lvls : List Level) (origTy x : Expr) : MetaM Expr := do
  if let some (auxName, np) := auxFor? aux params As origTy then
    -- the arguments past the key's parameters are the occurrence's indices
    let idxs := origTy.getAppArgs.extract np origTy.getAppArgs.size
    return mkApp (mkAppN (mkAppN (mkConst (packName auxName) lvls) As) idxs) x
  match origTy with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun y => do
      let body ← packField aux params As lvls (b.instantiate1 y) (mkApp x y)
      mkLambdaFVars #[y] body
  | _ => return x

/--
Shape of a recursor as the generator needs it: for each motive, the type it eliminates and the
auxiliary copy it maps to; and for each minor, which motive it belongs to and which constructor
it is for. Read off the recursor's own telescope rather than the block structure, because when
the type being nested under is *itself* a nested inductive its recursor carries extra motives
whose constructors live on its auxiliary recursors.
-/
structure RecShape where
  /-- Per motive, its own type `∀ is, I Ds is → Sort u`; open it with `withMotiveTy`. -/
  motiveTys : Array Expr
  auxNames  : Array Name
  motives   : Array Expr

/--
Open a motive's telescope, running `k` with the index binders and the type of the major premise.
For an indexed family the motive is `∀ is, I Ds is → Sort u`, so the major premise is the *last*
binder and its type mentions the index fvars. Everything derived from them has to be abstracted
before leaving `k`; the motive type itself mentions only `Ds` and so is safe to keep.
-/
def withMotiveTy (mTy : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  forallTelescope mTy fun xs _ => do k xs.pop (← inferType xs.back!)

/-- Compute `RecShape` and run `k` with the minor binders in scope. -/
def withRecShape (aux : Array (Expr × Name)) (params As : Array Expr)
    (jName : Name) (jlvls : List Level) (ds : Array Expr) (u : Level)
    (mkMotive : Array Expr → Expr → Name → MetaM Expr)
    (k : RecShape → Array Expr → Array Expr → MetaM α) : MetaM α := do
  let rv ← getConstInfoRec (mkRecName jName)
  let jv ← getConstInfoInduct jName
  let recLvls := if rv.levelParams.length == jv.levelParams.length + 1 then u :: jlvls else jlvls
  let recTy ← instantiateForall (rv.type.instantiateLevelParams rv.levelParams recLvls) ds
  forallBoundedTelescope recTy rv.numMotives fun ms rest => do
    let mut motiveTys := #[]
    let mut auxNames := #[]
    let mut motives := #[]
    for m in ms do
      let mTy ← inferType m
      let (a, mv) ← withMotiveTy mTy fun is dom => do
        let some (a, _) := auxFor? aux params As dom
          | throwError "no auxiliary copy for motive domain {dom}"
        return (a, ← mkMotive is dom a)
      motiveTys := motiveTys.push mTy
      auxNames := auxNames.push a
      motives := motives.push mv
    forallBoundedTelescope rest rv.numMinors fun mins _ =>
      k { motiveTys, auxNames, motives } ms mins

/--
Strip a field type down to the application a recursor would match a motive against: `whnf` at every
binder, as `add_inductive_fn::is_rec_argument` does, so a field declared `Unit → id T` is recognised
even though its head is `id`.
-/
partial def whnfStripBinders (fTy : Expr) : MetaM Expr := do
  match ← whnf fTy with
  | .forallE n d b bi => withLocalDecl n bi d fun x => whnfStripBinders (b.instantiate1 x)
  | t => return t

/--
Pair each of a minor premise's induction hypotheses with the field it belongs to, keyed by that
field's `FVarId`. `bs` is the premise opened as `fields ++ hypotheses`, and `targets` the `(head,
parameters)` of the domain of every motive of the recursor in hand, which is exactly what a field
has to be an application of to get a hypothesis.

Two reasons not to take the positions from `RecShape.isRecField`, which asks the narrower question of
whether the generator *wants* the hypothesis. A field at one of the types being declared has one that
is useless here, because the motive for those is trivial; and a field the generator does want can be
missed when its head is a reducible definition. Either way every later hypothesis shifts, and the
minors get hypotheses belonging to earlier fields. The pairing also cannot be read back off the
premise, since the motives have been replaced by concrete functions by this point and a hypothesis at
a constant motive no longer mentions its field. So it is predicted here and checked against the
number of hypotheses the premise actually has, which turns a wrong prediction into an error rather
than into a mismatch in whatever gets built from it.
-/
def ihsByField (targets : Array (Name × Array Expr)) (bs : Array Expr) (numFields : Nat) :
    MetaM (Std.HashMap FVarId Expr) := do
  let mut res := {}
  let mut next := numFields
  for fv in bs[0:numFields] do
    let t ← whnfStripBinders (← inferType fv)
    let args := t.getAppArgs
    let isRec := targets.any fun (c, ps) =>
      t.getAppFn.constName? == some c && ps.size <= args.size &&
        (List.range ps.size).all fun i => args[i]! == ps[i]!
    if isRec then
      let some ih := bs[next]?
        | throwError "more recursive fields than induction hypotheses in a minor premise"
      res := res.insert fv.fvarId! ih
      next := next + 1
  unless next == bs.size do
    throwError "paired {next - numFields} of {bs.size - numFields} induction hypotheses\n\
      motive domains {targets}, fields {← bs[0:numFields].toArray.mapM (inferType ·)}"
  return res

/-- The `(head, parameters)` of the domain of each of `sh`'s motives. -/
def motiveTargets (sh : RecShape) : MetaM (Array (Name × Array Expr)) :=
  sh.motiveTys.mapM fun mTy => withMotiveTy mTy fun is dom => do
    let some c := dom.getAppFn.constName?
      | throwError "motive domain is not an inductive application: {dom}"
    let args := dom.getAppArgs
    return (c, args[0 : args.size - is.size])

/-- Is `fTy` a constructor field at one of `sh`'s motive domains, i.e. covered by an IH? -/
def RecShape.isRecField (sh : RecShape) (aux : Array (Expr × Name)) (params As : Array Expr)
    (fTy : Expr) : Bool :=
  match auxFor? aux params As (stripBinders fTy) with
  | some (a, _) => sh.auxNames.contains a
  | none        => false

/-- Which motive a minor belongs to, and the constructor it is for. -/
def minorTarget (ms : Array Expr) (concl : Expr) : MetaM (Nat × Name × Expr) := do
  let some i := ms.idxOf? concl.getAppFn
    | throwError "minor conclusion is not a motive application: {concl}"
  let ctorApp := concl.getAppArgs.back!
  let .const cName _ := ctorApp.getAppFn | throwError "expected a constructor application: {ctorApp}"
  let ci ← getConstInfoCtor cName
  -- the constructor applied to its parameters only; those come from the motive's domain, so
  -- they are free of the minor's own binders and safe to use outside this telescope
  return (i, cName, mkAppN ctorApp.getAppFn ctorApp.getAppArgs[0:ci.numParams])

/--
The recursor family of `jName`'s declaration, in motive order: one recursor per type of the
mutual block, then one per nested occurrence of that declaration. Packs for a whole family are
mutually recursive, so they must all come from this family sharing one set of minors.
-/
def recFamily (jName : Name) : MetaM (Array Name) := do
  let jv ← getConstInfoInduct jName
  let main := jv.all.head!
  let mut rs := (jv.all.map mkRecName).toArray
  for i in [1 : jv.numNested + 1] do
    rs := rs.push ((mkRecName main).appendAfter s!"_{i}")
  return rs

/--
Which auxiliary copies a recursor family covers. An auxiliary type must be packed by the
family that also covers everything its pack is mutually recursive with, so each one is owned by
the *largest* family covering it: `List (Y α)` belongs to `Y`'s family, not to `List`'s.
-/
def familyCoverage (aux : Array (Expr × Name)) (params As : Array Expr) (lvls : List Level) :
    MetaM (Array (Name × Expr × Array Name)) := do
  let mut out := #[]
  for (key, auxName) in aux do
    let .const jName jlvls := key.getAppFn | throwError "bad key {key}"
    let u ← familyLevel (mkAppN (mkConst auxName lvls) As)
    let covered ← withRecShape aux params As jName jlvls key.getAppArgs u
      (fun is dom _ => withLocalDeclD `x dom fun x => mkLambdaFVars (is ++ #[x]) (mkSort .zero))
      (fun sh _ _ => return sh.auxNames)
    out := out.push (auxName, key, covered)
  return out

/-- Auxiliary types a family needs packs for beyond the ones it covers itself. -/
def familyDeps (model : Array InductiveType) (auxNames : Array Name) (covered : Array Name) :
    Array Name := Id.run do
  let mut deps : Array Name := #[]
  for a in covered do
    let some t := model.find? (·.name == a) | continue
    for c in t.ctors do
      for n in c.type.getUsedConstants do
        if auxNames.contains n && !covered.contains n && !deps.contains n then
          deps := deps.push n
  return deps

/-- Generate and add every `pack` function, one recursor family at a time. -/
def mkPacks (model : Array InductiveType) (aux : Array (Expr × Name))
    (params As : Array Expr) (lparams : List Name) : MetaM Unit := do
  let lvls := lparams.map Level.param
  let auxNames := aux.map (·.2)
  let cov ← familyCoverage aux params As lvls
  let mut owner : NameMap Name := {}
  for (rep, _, covered) in cov.qsort (fun a b => a.2.2.size > b.2.2.size) do
    for c in covered do
      unless owner.contains c do owner := owner.insert c rep
  -- families to emit, each with the auxes it owns and the auxes it depends on
  let mut fams := #[]
  for (rep, key, covered) in cov do
    let mine := covered.filter (fun c => owner.find? c == some rep)
    if mine.isEmpty then continue
    if fams.any (fun (r, _, _, _) => r == rep) then continue
    fams := fams.push (rep, key, mine, familyDeps model auxNames covered)
  -- worklist: emit a family once every auxiliary type it depends on exists
  let mut ready : NameSet := {}
  let mut left := fams
  while !left.isEmpty do
    let (now, later) := left.partition fun (_, _, _, deps) => deps.all ready.contains
    if now.isEmpty then
      throwError "cyclic pack dependency among {left.map (·.1)}"
    for (rep, key, mine, _) in now do
      let .const jName jlvls := key.getAppFn | throwError "bad key {key}"
      let ds := key.getAppArgs
      let u ← familyLevel (mkAppN (mkConst rep lvls) As)
      let mkMotive := fun is dom a => withLocalDeclD `x dom fun x =>
        mkLambdaFVars (is ++ #[x]) (mkAppN (mkConst a lvls) (As ++ is))
      let fam ← recFamily jName
      let (sh, minorVals) ← withRecShape aux params As jName jlvls ds u mkMotive
          fun sh ms mins => do
        let mut minorVals := #[]
        for mi in mins do
          let miTy ← inferType mi
          let (idx, cName, _) ← forallTelescope miTy fun _ concl => minorTarget ms concl
          let v ← forallTelescope (miTy.replaceFVars ms sh.motives) fun bs _ => do
            let ci ← getConstInfoCtor cName
            let auxCtor := cName.replacePrefix ci.induct sh.auxNames[idx]!
            -- `pack` recurses over the nesting host's own mutual block, not the model
            let ihOf ← ihsByField (← motiveTargets sh) bs ci.numFields
            let mut args := #[]
            for fv in bs[0:ci.numFields] do
              let fTy ← whnf (← inferType fv)
              match ihOf[fv.fvarId!]? with
              | some ih => if sh.isRecField aux params As fTy then
                             args := args.push ih
                           else
                             args := args.push (← packField aux params As lvls fTy fv)
              | none    => args := args.push (← packField aux params As lvls fTy fv)
            mkLambdaFVars bs (mkAppN (mkAppN (mkConst auxCtor lvls) As) args)
          minorVals := minorVals.push v
        return (sh, minorVals)
      unless fam.size == sh.motiveTys.size do
        throwError "recursor family size {fam.size} vs {sh.motiveTys.size} motives for {jName}"
      let jv ← getConstInfoInduct jName
      for i in [0 : sh.motiveTys.size] do
        let a := sh.auxNames[i]!
        unless mine.contains a do continue
        let rv ← getConstInfoRec fam[i]!
        let recLvls := if rv.levelParams.length == jv.levelParams.length + 1 then u :: jlvls else jlvls
        let recFn := mkAppN (mkAppN (mkAppN (mkConst fam[i]! recLvls) ds) sh.motives) minorVals
        let (typ, val) ← withMotiveTy sh.motiveTys[i]! fun is dom =>
          withLocalDeclD `x dom fun x => do
            return (← mkForallFVars (As ++ is ++ #[x]) (mkAppN (mkConst a lvls) (As ++ is)),
                    ← mkLambdaFVars (As ++ is ++ #[x]) (mkAppN recFn (is ++ #[x])))
        addDecl (.defnDecl { name := packName a, levelParams := lparams, type := typ,
                             value := val, hints := .abbrev, safety := .safe })
        ready := ready.insert a
    left := later

end NestedGen

namespace NestedGen

/-- Name of the `unpack` function for the auxiliary type `auxName`. -/
def unpackName (auxName : Name) : Name := auxName ++ `unpack

/--
Generate and add every `unpack` function. Unlike `pack`, each one is a single application of
the *model's* recursor with all motives instantiated: aux types map to their originals, the
types being declared map to `PUnit` since they are the same in both worlds.
-/
def mkUnpacks (model : Array InductiveType) (aux : Array (Expr × Name))
    (As : Array Expr) (lparams : List Name) : MetaM Unit := do
  let lvls := lparams.map Level.param
  let auxOf : Name → Option Expr := fun n => (aux.find? (fun (_, m) => m == n)).map (·.1)
  for (key, auxName) in aux do
    let u ← familyLevel key
    -- motives, in model order
    let mut motives := #[]
    for t in model do
      motives := motives.push (← withModelIndices t As lvls fun is tApp => do
        let target := match auxOf t.name with
          | some k => mkAppN k is             -- an auxiliary copy: unpack to its original
          | none   => mkConst ``PUnit [u]     -- a type being declared: same in both worlds
        withLocalDeclD `x tApp fun x => mkLambdaFVars (is ++ #[x]) target)
    let recName := mkRecName auxName
    let rv ← getConstInfoRec recName
    let recLvls := if rv.levelParams.length == lparams.length + 1 then u :: lvls else lvls
    let recFn := mkAppN (mkAppN (mkConst recName recLvls) As) motives
    -- minors, read off the recursor's telescope
    let mut minors := #[]
    let mut ty ← inferType recFn
    for t in model do
      for c in t.ctors do
        let ci ← getConstInfoCtor c.name
        let .forallE _ minorTy body _ := ty | throwError "expected minor binder, got {ty}"
        let minor ← forallTelescope minorTy fun bs _ => do
          match auxOf t.name with
          | none => mkLambdaFVars bs (mkConst ``PUnit.unit [u])
          | some k =>
            let .const kName klvls := k.getAppFn | throwError "bad key {k}"
            let ihOf ← ihsByField (model.map fun t => (t.name, As)) bs ci.numFields
            let mut args := #[]
            for fv in bs[0:ci.numFields] do
              let fTy := stripBinders (← whnf (← inferType fv))
              -- for an auxiliary copy the induction hypothesis already carries the unpacked value,
              -- at the right type and under the same binders; for a type being declared the motive
              -- is `PUnit`, so the field itself is what we want
              let ih? := do
                let n ← fTy.getAppFn.constName?
                guard (auxOf n).isSome
                ihOf[fv.fvarId!]?
              args := args.push (ih?.getD fv)
            let origCtor := c.name.replacePrefix t.name kName
            mkLambdaFVars bs (mkAppN (mkAppN (mkConst origCtor klvls) k.getAppArgs) args)
        minors := minors.push minor
        ty := body.instantiate1 minor
    let some mt := model.find? (·.name == auxName) | throwError "no model type {auxName}"
    let (typ, val) ← withModelIndices mt As lvls fun is auxApp =>
      withLocalDeclD `x auxApp fun x => do
        return (← mkForallFVars (As ++ is ++ #[x]) (mkAppN key is),
                ← mkLambdaFVars (As ++ is ++ #[x]) (mkAppN (mkAppN recFn minors) (is ++ #[x])))
    addDecl (.defnDecl { name := unpackName auxName, levelParams := lparams, type := typ,
                         value := val, hints := .abbrev, safety := .safe })

end NestedGen

namespace NestedGen

/-- `unpack (pack x) = x`, the UNPACK_PACK layer in Lean 3's naming. -/
def unpackPackName (auxName : Name) : Name := auxName ++ `unpack_pack

/-- Close a pointwise equation under all its leading binders with `funext`. -/
partial def funextAll (h : Expr) : MetaM Expr := do
  match ← whnf (← inferType h) with
  | .forallE n d _ bi =>
    withLocalDecl n bi d fun y => do
      let inner ← funextAll (mkApp h y)
      mkFunExt (← mkLambdaFVars #[y] inner)
  | _ => return h

/--
Proof that a constructor field survives the round trip. Nested occurrences appeal to the deeper
round trip; binders are handled pointwise and closed with `funext`, which is the only place the
certificate needs it; anything else is unchanged, so `rfl`.
-/
partial def fieldRoundTrip (aux : Array (Expr × Name)) (params As : Array Expr)
    (lvls : List Level) (fTy fv : Expr) : MetaM Expr := do
  if let some (lAux, np) := auxFor? aux params As fTy then
    let idxs := fTy.getAppArgs.extract np fTy.getAppArgs.size
    return mkApp (mkAppN (mkAppN (mkConst (unpackPackName lAux) lvls) As) idxs) fv
  match fTy with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun y => do
      let p ← fieldRoundTrip aux params As lvls (b.instantiate1 y) (mkApp fv y)
      mkFunExt (← mkLambdaFVars #[y] p)
  | _ => mkEqRefl fv

/--
Round trip in the original world, family by family, mirroring `mkPacks`: the induction
hypothesis for a field at a motive domain, the deeper round trip (through binders, closed with
`funext`) otherwise, and the `congr` chain over the constructor's arguments.
-/
def mkUnpackPacks (model : Array InductiveType) (aux : Array (Expr × Name))
    (params As : Array Expr) (lparams : List Name) : MetaM Unit := do
  let lvls := lparams.map Level.param
  let auxNames := aux.map (·.2)
  let cov ← familyCoverage aux params As lvls
  let mut owner : NameMap Name := {}
  for (rep, _, covered) in cov.qsort (fun a b => a.2.2.size > b.2.2.size) do
    for c in covered do
      unless owner.contains c do owner := owner.insert c rep
  let mut fams := #[]
  for (rep, key, covered) in cov do
    let mine := covered.filter (fun c => owner.find? c == some rep)
    if mine.isEmpty then continue
    if fams.any (fun (r, _, _, _) => r == rep) then continue
    fams := fams.push (rep, key, mine, familyDeps model auxNames covered)
  let mut ready : NameSet := {}
  let mut left := fams
  while !left.isEmpty do
    let (now, later) := left.partition fun (_, _, _, deps) => deps.all ready.contains
    if now.isEmpty then throwError "cyclic round-trip dependency among {left.map (·.1)}"
    for (_, key, mine, _) in now do
      let .const jName jlvls := key.getAppFn | throwError "bad key {key}"
      let ds := key.getAppArgs
      let mkMotive := fun is dom a => withLocalDeclD `x dom fun x => do
        mkLambdaFVars (is ++ #[x]) (← mkEq
          (mkApp (mkAppN (mkAppN (mkConst (unpackName a) lvls) As) is)
            (mkApp (mkAppN (mkAppN (mkConst (packName a) lvls) As) is) x)) x)
      let fam ← recFamily jName
      let (sh, minorVals) ← withRecShape aux params As jName jlvls ds .zero mkMotive
          fun sh ms mins => do
        let mut minorVals := #[]
        for mi in mins do
          let miTy ← inferType mi
          let (_, cName, cFn) ← forallTelescope miTy fun _ concl => minorTarget ms concl
          let v ← forallTelescope (miTy.replaceFVars ms sh.motives) fun bs _ => do
            let ci ← getConstInfoCtor cName
            -- like `pack`, this recurses over the nesting host's own mutual block
            let ihOf ← ihsByField (← motiveTargets sh) bs ci.numFields
            let mut acc ← mkEqRefl cFn
            for fv in bs[0:ci.numFields] do
              let fTy ← whnf (← inferType fv)
              let p ← match ihOf[fv.fvarId!]? with
                | some ih =>
                  if sh.isRecField aux params As fTy then funextAll ih
                  else fieldRoundTrip aux params As lvls fTy fv
                | none => fieldRoundTrip aux params As lvls fTy fv
              acc ← congrStep acc fv p
            mkLambdaFVars bs acc
          minorVals := minorVals.push v
        return (sh, minorVals)
      unless fam.size == sh.motiveTys.size do
        throwError "recursor family size {fam.size} vs {sh.motiveTys.size} motives for {jName}"
      let jv ← getConstInfoInduct jName
      for i in [0 : sh.motiveTys.size] do
        let a := sh.auxNames[i]!
        unless mine.contains a do continue
        let rv ← getConstInfoRec fam[i]!
        let recLvls := if rv.levelParams.length == jv.levelParams.length + 1
          then .zero :: jlvls else jlvls
        let recFn := mkAppN (mkAppN (mkAppN (mkConst fam[i]! recLvls) ds) sh.motives) minorVals
        let (typ, val) ← withMotiveTy sh.motiveTys[i]! fun is dom =>
          withLocalDeclD `x dom fun x => do
            let lhs := mkApp (mkAppN (mkAppN (mkConst (unpackName a) lvls) As) is)
              (mkApp (mkAppN (mkAppN (mkConst (packName a) lvls) As) is) x)
            return (← mkForallFVars (As ++ is ++ #[x]) (← mkEq lhs x),
                    ← mkLambdaFVars (As ++ is ++ #[x]) (mkAppN recFn (is ++ #[x])))
        addDecl (.thmDecl { name := unpackPackName a, levelParams := lparams,
                            type := typ, value := val })
        ready := ready.insert a
    left := later

end NestedGen

namespace NestedGen

/-- `pack (unpack y) = y`, the PACK_UNPACK layer. -/
def packUnpackName (auxName : Name) : Name := auxName ++ `pack_unpack

/--
Round trip in the model, by recursion on the model's recursor. Mirrors `mkUnpacks`: the
induction hypothesis for a field at an auxiliary type is exactly its round trip, fields at a
type being declared are unchanged, and binders are closed with `funext`.
-/
def mkPackUnpacks (model : Array InductiveType) (aux : Array (Expr × Name))
    (As : Array Expr) (lparams : List Name) : MetaM Unit := do
  let lvls := lparams.map Level.param
  let auxOf : Name → Option Expr := fun n => (aux.find? (fun (_, m) => m == n)).map (·.1)
  for (_, auxName) in aux do
    let mut motives := #[]
    for t in model do
      motives := motives.push (← withModelIndices t As lvls fun is tApp =>
        withLocalDeclD `y tApp fun y => do
          match auxOf t.name with
          | none   => mkLambdaFVars (is ++ #[y]) (mkConst ``True)
          | some _ =>
            mkLambdaFVars (is ++ #[y]) (← mkEq
              (mkApp (mkAppN (mkAppN (mkConst (packName t.name) lvls) As) is)
                (mkApp (mkAppN (mkAppN (mkConst (unpackName t.name) lvls) As) is) y)) y))
    let recName := mkRecName auxName
    let rv ← getConstInfoRec recName
    let recLvls := if rv.levelParams.length == lparams.length + 1 then Level.zero :: lvls else lvls
    let recFn := mkAppN (mkAppN (mkConst recName recLvls) As) motives
    let mut minors := #[]
    let mut ty ← inferType recFn
    for t in model do
      for c in t.ctors do
        let ci ← getConstInfoCtor c.name
        let .forallE _ minorTy body _ := ty | throwError "expected minor binder, got {ty}"
        let minor ← forallTelescope minorTy fun bs _ => do
          if (auxOf t.name).isNone then
            mkLambdaFVars bs (mkConst ``True.intro)
          else
            let ihOf ← ihsByField (model.map fun t => (t.name, As)) bs ci.numFields
            let mut acc ← mkEqRefl (mkAppN (mkConst c.name lvls) As)
            for fv in bs[0:ci.numFields] do
              let fTy := stripBinders (← whnf (← inferType fv))
              let ih? := do
                let n ← fTy.getAppFn.constName?
                guard (auxOf n).isSome
                ihOf[fv.fvarId!]?
              let p ← match ih? with
                | some ih => funextAll ih
                | none    => mkEqRefl fv
              acc ← congrStep acc fv p
            mkLambdaFVars bs acc
        minors := minors.push minor
        ty := body.instantiate1 minor
    let some mt := model.find? (·.name == auxName) | throwError "no model type {auxName}"
    let (typ, val) ← withModelIndices mt As lvls fun is auxApp =>
      withLocalDeclD `y auxApp fun y => do
        let lhs := mkApp (mkAppN (mkAppN (mkConst (packName auxName) lvls) As) is)
          (mkApp (mkAppN (mkAppN (mkConst (unpackName auxName) lvls) As) is) y)
        return (← mkForallFVars (As ++ is ++ #[y]) (← mkEq lhs y),
                ← mkLambdaFVars (As ++ is ++ #[y]) (mkAppN (mkAppN recFn minors) (is ++ #[y])))
    addDecl (.thmDecl { name := packUnpackName auxName, levelParams := lparams,
                        type := typ, value := val })

end NestedGen

namespace NestedGen

/-- Mirror of `packField`: unpack a field of the model back to the original world. -/
partial def unpackField (aux : Array (Expr × Name)) (params As : Array Expr)
    (lvls : List Level) (auxTy x : Expr) : MetaM Expr := do
  if let some a := (aux.find? (fun (_, m) => auxTy.getAppFn == mkConst m lvls)).map (·.2) then
    -- a model type's arguments are the parameters followed by the occurrence's indices
    let idxs := auxTy.getAppArgs.extract As.size auxTy.getAppArgs.size
    return mkApp (mkAppN (mkAppN (mkConst (unpackName a) lvls) As) idxs) x
  match auxTy with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun y => do
      mkLambdaFVars #[y] (← unpackField aux params As lvls (b.instantiate1 y) (mkApp x y))
  | _ => return x

/-- Mirror of `fieldRoundTrip` for the other direction: `pack (unpack fv) = fv`. -/
partial def fieldPackUnpack (aux : Array (Expr × Name)) (params As : Array Expr)
    (lvls : List Level) (auxTy fv : Expr) : MetaM Expr := do
  if let some a := (aux.find? (fun (_, m) => auxTy.getAppFn == mkConst m lvls)).map (·.2) then
    let idxs := auxTy.getAppArgs.extract As.size auxTy.getAppArgs.size
    return mkApp (mkAppN (mkAppN (mkConst (packUnpackName a) lvls) As) idxs) fv
  match auxTy with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun y => do
      mkFunExt (← mkLambdaFVars #[y]
        (← fieldPackUnpack aux params As lvls (b.instantiate1 y) (mkApp fv y)))
  | _ => mkEqRefl fv

/--
Lean 3's `spec_lemma`s: how `pack` and `unpack` compute on each constructor. They all hold by
`rfl`, but `simp` still needs them as rewrite rules, since it will not unfold the bridges and
fire the recursors on its own.
-/
def mkSpecLemmas (model : Array InductiveType) (aux : Array (Expr × Name))
    (As : Array Expr) (lparams : List Name) : MetaM (Array Name) := do
  let lvls := lparams.map Level.param
  let mut out := #[]
  for (key, a) in aux do
    let .const jName jlvls := key.getAppFn | throwError "bad key {key}"
    let ds := key.getAppArgs
    let jv ← getConstInfoInduct jName
    -- how `pack` computes on each of the original constructors
    for c in jv.ctors do
      let ci ← getConstInfoCtor c
      let cTy ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams jlvls) ds
      let nm := a ++ `pack_spec ++ Name.mkSimple c.getString!
      let (ty, val) ← forallTelescope cTy fun fields concl => do
        -- the bridge is applied at the indices this constructor determines
        let cIdxs := concl.getAppArgs.extract ds.size concl.getAppArgs.size
        let lhs := mkApp (mkAppN (mkAppN (mkConst (packName a) lvls) As) cIdxs)
          (mkAppN (mkAppN (mkConst c jlvls) ds) fields)
        let mut args := #[]
        for fv in fields do
          args := args.push (← packField aux As As lvls (← whnf (← inferType fv)) fv)
        let rhs := mkAppN (mkAppN (mkConst (c.replacePrefix jName a) lvls) As) args
        return (← mkForallFVars (As ++ fields) (← mkEq lhs rhs),
                ← mkLambdaFVars (As ++ fields) (← mkEqRefl lhs))
      addDecl (.thmDecl { name := nm, levelParams := lparams, type := ty, value := val })
      out := out.push nm
    -- and how `unpack` computes on each of the model's copies
    let some t := model.find? (·.name == a) | continue
    for c in t.ctors do
      let ci ← getConstInfoCtor c.name
      let cTy ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls) As
      let nm := a ++ `unpack_spec ++ Name.mkSimple c.name.getString!
      let (ty, val) ← forallTelescope cTy fun fields concl => do
        let cIdxs := concl.getAppArgs.extract As.size concl.getAppArgs.size
        let lhs := mkApp (mkAppN (mkAppN (mkConst (unpackName a) lvls) As) cIdxs)
          (mkAppN (mkAppN (mkConst c.name lvls) As) fields)
        let mut args := #[]
        for fv in fields do
          args := args.push (← unpackField aux As As lvls (← whnf (← inferType fv)) fv)
        let rhs := mkAppN (mkAppN (mkConst (c.name.replacePrefix a jName) jlvls) ds) args
        return (← mkForallFVars (As ++ fields) (← mkEq lhs rhs),
                ← mkLambdaFVars (As ++ fields) (← mkEqRefl lhs))
      addDecl (.thmDecl { name := nm, levelParams := lparams, type := ty, value := val })
      out := out.push nm
  return out

/--
Rewrite a term over the model back into the nested presentation: the inverse of the elimination.

An auxiliary copy applied to its parameters and indices becomes the occurrence it stands for, at those
parameters; a constructor of one becomes the original constructor, whose own parameters come from that
restored occurrence rather than from where it stood; anything else the model renamed becomes the
declaration's own constant.

The kernel does this today and declares the result, so a mistake here would be the original bug.
`checkRestore` is what keeps it honest.
-/
def restoreNested (auxOcc : NameMap Expr) (back : NameMap Name) (auxCtorOf : NameMap Name)
    (params As : Array Expr) (np : Nat) (e : Expr) : Expr :=
  -- `Expr.replace`, not `Meta.transform`: the latter reopens and recloses every binder it passes,
  -- which beta-reduces. Not because the kernel's form is worth reproducing, it is not: where the two
  -- differ the reduced one reads better, and `checkRestore` compares up to definitional equality for
  -- that reason. Only because reducing nothing perturbs nothing, which is worth something on the day
  -- this derivation replaces what the kernel declares.
  e.replace fun t =>
      match t.getAppFn.constName? with
      | none => none
      | some c =>
        let args := t.getAppArgs
        if let some occ := auxOcc.find? c then
          -- with no parameters the copy stands alone, so this fires on the bare constant too
          if args.size ≥ np then some (mkAppN (occ.replaceFVars params As) args[np:]) else none
        else if (auxCtorOf.find? c).isNone then
          -- a plain rename belongs on the constant, so that `replace` still descends into the
          -- arguments; returning a rebuilt application here would leave them untouched
          match t with
          | .const _ lvls => (back.find? c).map (mkConst · lvls)
          | _ => none
        else match auxCtorOf.find? c with
          | none => none
          | some auxName =>
            match auxOcc.find? auxName with
            | none => none
            | some occ =>
              if args.size < np then none else
                let occ := occ.replaceFVars params As
                match occ.getAppFn.constName? with
                | none => none
                | some head =>
                  some (mkAppN (mkAppN (mkConst (c.replacePrefix auxName head)
                    occ.getAppFn.constLevels!) occ.getAppArgs) args[np:])

/--
The parameter count of an inductive the model mentions, which for one of the declaration's own types
cannot come from the environment: the kernel asks for the certificate before declaring them.
-/
def lastBinderDomain : Expr → Expr
  | .forallE _ d b _ => if b.isForall then lastBinderDomain b else d
  | e => e

def numParamsOf (types : Array InductiveType) (nparams : Nat) (n : Name) : MetaM Nat := do
  if types.any (·.name == n) then return nparams
  return (← getConstInfoInduct n).numParams

/-- A recursor of the nested declaration, as derived from the model rather than read back. -/
public structure RestoredRec where
  name        : Name
  levelParams : List Name
  type        : Expr
  numIndices  : Nat
  /-- Constructor, field count and right-hand side, in the order the recursor states them. -/
  rules       : Array (Name × Nat × Expr)
  /-- The theorem discharging each rule, aligned with `rules`; `none` where it holds definitionally. -/
  proofs      : Array (Option Name) := #[]
  deriving Inhabited

/--
Derive every recursor the declaration introduces from the model, by restoring the nesting in the
model's own recursors.

These are the recursors the kernel declares; `checkRestore` measures them against the ones a caller
already has, for the tests and for anything certifying a declaration after the fact.

`numIndices` comes off the major premise, as the arguments to the type being eliminated beyond that
type's own parameters. It cannot come from the recursor's telescope: for an auxiliary recursor the
nesting fixed those parameters, so they are neither indices nor parameters of the recursor.
-/
public def restoreRecursors (iv : InductiveVal) (types : Array InductiveType)
    (model : Array InductiveType) (origRecs : Array Name)
    (aux : Array (Expr × Name)) (params : Array Expr) (ren : Name → Name) :
    MetaM (Array RestoredRec) := do
  let mut back : NameMap Name := {}
  for t in types do
    back := back.insert (ren t.name) t.name
    for c in t.ctors do
      back := back.insert (ren c.name) c.name
  -- `renameModel` renamed the occurrences too, and nothing descends into a substituted one, so put
  -- the declaration's own names back into them here rather than hoping to reach them later
  let renameBack (e : Expr) : Expr :=
    e.replace fun t => match t with
      | .const c lvls => (back.find? c).map (mkConst · lvls)
      | _ => none
  let mut auxOcc : NameMap Expr := {}
  for (occ, a) in aux do
    auxOcc := auxOcc.insert a (renameBack occ)
  let mut auxCtorOf : NameMap Name := {}
  for t in model do
    if auxOcc.contains t.name then
      for c in t.ctors do
        auxCtorOf := auxCtorOf.insert c.name t.name
  for i in [0 : origRecs.size] do
    back := back.insert (mkRecName model[i]!.name) origRecs[i]!
  -- a rule names its constructor, and an auxiliary copy's is named after the occurrence it stands for
  let mut ctorBack : NameMap Name := back
  for (occ, a) in aux do
    if let some head := occ.getAppFn.constName? then
      if let some t := model.find? (·.name == a) then
        for c in t.ctors do
          ctorBack := ctorBack.insert c.name (c.name.replacePrefix a head)
  let restore (e : Expr) (isType : Bool) : MetaM Expr :=
    if isType then
      forallBoundedTelescope e iv.numParams fun As body => do
        mkForallFVars As (restoreNested auxOcc back auxCtorOf params As iv.numParams body)
    else
      lambdaBoundedTelescope e iv.numParams fun As body => do
        mkLambdaFVars As (restoreNested auxOcc back auxCtorOf params As iv.numParams body)
  let mut res := #[]
  for i in [0 : origRecs.size] do
    let modelRec ← getConstInfoRec (mkRecName model[i]!.name)
    let type ← restore modelRec.type true
    -- The major premise is the last binder, and its domain is where the indices are visible. Read
    -- syntactically: the type talks about a declaration that need not exist yet, so it cannot be
    -- put through `inferType`.
    let majorTy := betaAll (lastBinderDomain type)
    let some head := majorTy.getAppFn.constName? | throwError "no head for {majorTy}"
    let numIndices := majorTy.getAppArgs.size - (← numParamsOf types iv.numParams head)
    let mut rules := #[]
    for r in modelRec.rules do
      rules := rules.push ((ctorBack.find? r.ctor).getD r.ctor, r.nfields, ← restore r.rhs false)
    res := res.push { name := origRecs[i]!, levelParams := modelRec.levelParams, type,
                      numIndices, rules }
  return res

/--
Surrogate constants: the nested declaration presented as definitions over the model. The
constructor packs its arguments; the recursors go through the model's recursors, with the
motive at an auxiliary type composed with `unpack`.

The target types are the ones the kernel actually produced for this declaration, renamed onto
the model, so a successful build is checked against ground truth rather than against our own
idea of what the recursor should look like.
-/
def mkSurrogates (types : Array InductiveType) (nparams : Nat)
    (model : Array InductiveType) (aux : Array (Expr × Name))
    (As : Array Expr) (lparams : List Name) (fix : Expr → Expr)
    (origAll : List Name) (restored : Array RestoredRec) :
    MetaM (Array Name × Nat × Nat × Array Name × Array Name × Array (Name × Name × Name)) := do
  let lvls := lparams.map Level.param
  let mut origCtorTy : NameMap Expr := {}
  for t in types do
    for c in t.ctors do
      origCtorTy := origCtorTy.insert c.name c.type
  let proofNames ← IO.mkRef #[]
  -- which rule each accepted proof discharges, so the kernel need not search for it
  let ruleProofs ← IO.mkRef (#[] : Array (Name × Name × Name))
  let _specs ← mkSpecLemmas model aux As lparams
  let auxOf : Name → Option Expr := fun n => (aux.find? (fun (_, m) => m == n)).map (·.1)
  let declared := model.filter (fun t => (auxOf t.name).isNone)
  -- surrogate constructors: pack the arguments, then use the model's constructor
  -- `declared` is in declaration order, so it lines up with `origAll`
  for (t, origName) in declared.zip origAll.toArray do
    for c in t.ctors do
      let some cty := origCtorTy.find? (c.name.replacePrefix t.name origName)
        | throwError "no constructor {c.name.replacePrefix t.name origName} in the declaration"
      let origTy := fix (cty.instantiateLevelParams lparams lvls)
      let val ← forallTelescope (← instantiateForall origTy As) fun fields _ => do
          let mut args := #[]
          for fv in fields do
            args := args.push (← packField aux As As lvls (← whnf (← inferType fv)) fv)
          mkLambdaFVars (As ++ fields) (mkAppN (mkAppN (mkConst c.name lvls) As) args)
      addDecl (.defnDecl { name := c.name ++ `surr, levelParams := lparams, type := origTy,
                           value := val, hints := .abbrev, safety := .safe })
  -- surrogate recursors: the model's recursor with the motive at an auxiliary type composed
  -- with `unpack`. Minors for auxiliary constructors need no transport because `unpack`
  -- computes on constructors; minors for a declared type's constructors do, since there the
  -- model motive is used unchanged and `pack (unpack _) = _` is only propositional.
  let modelNames := model.map (·.name)
  -- derived from the model rather than read back, so nothing here depends on the kernel having
  -- already declared them
  let origRecs1 := restored.map (·.name)
  for i in [0 : model.size] do
    let orv := restored[i]!
    let elimPoly := orv.levelParams.length == lparams.length + 1
    let recLps := if elimPoly then `u_elim :: lparams else lparams
    let useLvls := if elimPoly then Level.param `u_elim :: lvls else lvls
    let target := fix (orv.type.instantiateLevelParams orv.levelParams useLvls)
    -- the original recursor's telescope is motives, minors, indices, major
    let nIdx := orv.numIndices
    let val ← forallTelescope (← instantiateForall target As) fun bs _ => do
      let motives := bs.extract 0 model.size
      let minors := bs.extract model.size (bs.size - 1 - nIdx)
      let majorIdxs := bs.extract (bs.size - 1 - nIdx) (bs.size - 1)
      let major := bs.back!
      let mut mms := #[]
      for j in [0 : model.size] do
        let mName := modelNames[j]!
        mms := mms.push (← withModelIndices model[j]! As lvls fun is mApp =>
          withLocalDeclD `y mApp fun y => do
            let arg := match auxOf mName with
              | none   => y
              | some _ => mkApp (mkAppN (mkAppN (mkConst (unpackName mName) lvls) As) is) y
            mkLambdaFVars (is ++ #[y]) (mkApp (mkAppN motives[j]! is) arg))
      let modelRec := mkRecName modelNames[i]!
      let mrv ← getConstInfoRec modelRec
      let mRecLvls := if mrv.levelParams.length == lparams.length + 1
        then Level.param `u_elim :: lvls else lvls
      let base := mkAppN (mkAppN (mkConst modelRec mRecLvls) As) mms
      let mut ty ← inferType base
      let mut mins := #[]
      let mut k := 0
      for tIdx in [0 : model.size] do
        let t := model[tIdx]!
        for c in t.ctors do
          let ci ← getConstInfoCtor c.name
          let .forallE _ minorTy body _ := ty | throwError "expected minor binder, got {ty}"
          let v ← forallTelescope minorTy fun cs _ => do
            let fields := cs.extract 0 ci.numFields
            let ihs := cs.extract ci.numFields cs.size
            let mut args := #[]
            for fv in fields do
              args := args.push (← unpackField aux As As lvls (← whnf (← inferType fv)) fv)
            let applied := mkAppN (mkAppN minors[k]! args) ihs
            match auxOf t.name with
            | some _ => mkLambdaFVars cs applied
            | none =>
              let mut acc ← mkEqRefl (mkAppN (mkConst c.name lvls) As)
              for fv in fields do
                acc ← congrStep acc fv
                  (← fieldPackUnpack aux As As lvls (← whnf (← inferType fv)) fv)
              -- the indices this constructor determines, in terms of the minor's own fields
              let cIdxs ← ctorIndices ci.numParams (mkAppN (mkAppN (mkConst c.name lvls) As) fields)
              let mot ← withLocalDeclD `z (mkAppN (mkAppN (mkConst t.name lvls) As) cIdxs) fun z =>
                mkLambdaFVars #[z] (mkApp (mkAppN motives[tIdx]! cIdxs) z)
              mkLambdaFVars cs (← mkEqNDRec mot applied acc)
          mins := mins.push v
          ty := body.instantiate1 v
          k := k + 1
      -- an auxiliary recursor's major premise is in the original world, so pack it and
      -- transport the result back along `unpack (pack _) = _`
      let mName := modelNames[i]!
      match auxOf mName with
      | none => mkLambdaFVars (As ++ bs) (mkAppN (mkAppN base mins) (majorIdxs ++ #[major]))
      | some key =>
        let packed := mkApp (mkAppN (mkAppN (mkConst (packName mName) lvls) As) majorIdxs) major
        let applied := mkAppN (mkAppN base mins) (majorIdxs ++ #[packed])
        let mot ← withLocalDeclD `z (mkAppN key majorIdxs) fun z =>
          mkLambdaFVars #[z] (mkApp (mkAppN motives[i]! majorIdxs) z)
        let h := mkApp (mkAppN (mkAppN (mkConst (unpackPackName mName) lvls) As) majorIdxs) major
        mkLambdaFVars (As ++ bs) (← mkEqNDRec mot applied h)
    addDecl (.defnDecl { name := modelNames[0]! ++ Name.mkSimple s!"rec_surr{i}",
                         levelParams := recLps, type := target, value := val,
                         hints := .abbrev, safety := .safe })
  -- certificate equations: for each rule the kernel declared, state it about the surrogates
  -- and see whether it already holds definitionally
  let mut byRfl := 0
  let mut byProof := 0
  let mut openRules : Array Name := #[]
  for i in [0 : model.size] do
    let orv := restored[i]!
    let surrRecName := modelNames[0]! ++ Name.mkSimple s!"rec_surr{i}"
    let srv ← getConstInfo surrRecName
    let elimPoly := orv.levelParams.length == lparams.length + 1
    let useLvls := if elimPoly then Level.param `u_elim :: lvls else lvls
    let nIdx := orv.numIndices
    let (r, q, o) ← forallTelescope (← instantiateForall srv.type As) fun bs _ => do
      let motives := bs.extract 0 model.size
      let minors := bs.extract model.size (bs.size - 1 - nIdx)
      let majorTy ← whnf (← inferType bs.back!)
      let cLvls := majorTy.getAppFn.constLevels!
      let mut r := 0
      let mut q := 0
      let mut openRules : Array Name := #[]
      for (rCtor, _, rRhs) in orv.rules do
        let cnp ← numParamsOf types nparams majorTy.getAppFn.constName!
        let cparams := majorTy.getAppArgs.extract 0 cnp
        let cFn := fix (mkConst rCtor cLvls)
        let eq? ← forallTelescope (← instantiateForall (← inferType cFn) cparams) fun fields _ => do
          let cApp := mkAppN (mkAppN cFn cparams) fields
          let cIdxs ← ctorIndices cnp cApp
          let lhs := mkApp (mkAppN (mkAppN (mkAppN (mkAppN (mkConst surrRecName useLvls) As)
            motives) minors) cIdxs) cApp
          let rhs := mkAppN (fix (rRhs.instantiateLevelParams orv.levelParams useLvls))
            (As ++ motives ++ minors ++ fields)
          isDefEq lhs rhs
        if eq? then r := r + 1 else
          let proved ← forallTelescope (← instantiateForall (← inferType cFn) cparams)
            fun fields _ => do
              let cApp := mkAppN (mkAppN cFn cparams) fields
              let cIdxs ← ctorIndices cnp cApp
              let lhs := mkApp (mkAppN (mkAppN (mkAppN (mkAppN (mkConst surrRecName useLvls) As)
                motives) minors) cIdxs) cApp
              let rhs := mkAppN (fix (rRhs.instantiateLevelParams orv.levelParams useLvls))
                (As ++ motives ++ minors ++ fields)
              let goal ← mkEq lhs rhs
              -- `addDecl` reports kernel failures rather than throwing, so `<|>` never sees them.
              -- Asking whether the name landed is not enough either: on a rejected proof
              -- `addDeclCore` falls back to adding it as an axiom of the same type. Only a theorem
              -- means the kernel accepted the term.
              let emit (suffix : Name) (pf : Expr) : MetaM Bool := do
                -- the kernel finds the proofs by name, so record the ones it accepted
                let ctxFVars := As ++ motives ++ minors ++ fields
                let nm := surrRecName ++ suffix ++ Name.mkSimple rCtor.getString!
                let ty ← instantiateMVars (← mkForallFVars ctxFVars goal)
                let vl ← instantiateMVars (← mkLambdaFVars ctxFVars pf)
                -- the goal mentions the elimination universe when the recursor is polymorphic
                let certLps := if elimPoly then `u_elim :: lparams else lparams
                (do addDecl (.thmDecl { name := nm, levelParams := certLps,
                                        type := ty, value := vl })) <|> pure ()
                match (← getEnv).find? nm with
                | some (.thmInfo _) =>
                  proofNames.modify (·.push nm)
                  ruleProofs.modify (·.push (orv.name, rCtor, nm))
                  return true
                | _                 => return false
              -- Unification cannot guess `k` and `F` when the transported field is not in a
              -- pattern position, but every argument of the law is derivable, so build the
              -- application outright.
              let explicit : MetaM Bool := do
                -- Same care as on the right: never `whnf`, which would turn `Eq.ndrec` into
                -- `Eq.rec` and hand us a two-argument motive. But for the *main* recursor the
                -- transport is inside the minor rather than at the head, so step: unfold a
                -- surrogate constant when one is at the head, otherwise iota/beta-reduce, until
                -- the transport surfaces.
                let mut lhsW := lhs
                for _ in [0 : 8] do
                  if lhsW.getAppFn.constName? == some ``Eq.ndrec then break
                  let stepped ←
                    match ← unfoldDefinition? lhsW with
                    | some e => pure e.headBeta
                    | none   => whnfCore lhsW
                  if stepped == lhsW then break
                  lhsW := stepped
                let la := lhsW.getAppArgs
                let .const ln _ := lhsW.getAppFn | return false
                unless (ln == ``Eq.ndrec || ln == ``Eq.rec) && la.size ≥ 6 do return false
                -- an `Eq.rec` motive takes the proof as a second argument, but never uses it;
                -- drop that binder so the motive fits `N : C → Sort w`
                let dropProofBinder : Expr → Expr := fun m =>
                  match m with
                  | .lam n1 t1 (.lam _ _ b _) bi =>
                    if b.hasLooseBVar 0 then m else .lam n1 t1 (b.lowerLooseBVars 1 1) bi
                  | _ => m
                let N := dropProofBinder la[2]!
                -- Compare the core against the target instead of looking for a transport in the
                -- target's arguments. A transported field is a field slot whose term differs while
                -- its type does not; the hypothesis slots after the fields are the ones whose type
                -- differs, by exactly the round trip on their field. Reading the law's arguments off
                -- an `Eq.ndrec` in the target only works when that hypothesis is itself a visible
                -- transport, and it is not once the field is function-valued: there the hypothesis is
                -- `fun y => rec_surr … (f y)`, and the surrogate recursor cannot iota-reduce on a
                -- variable.
                let byFields : MetaM Bool := do
                  let rFn := rhs.headBeta.getAppFn
                  -- the transport can wrap a recursor application that still has to iota-reduce
                  -- before the minor surfaces, as it does for an auxiliary recursor's own rules
                  let mut core := la[3]!
                  for _ in [0 : 8] do
                    if core.getAppFn == rFn then break
                    let stepped ← whnfCore core
                    if stepped == core then break
                    core := stepped
                  let cFn := core.getAppFn
                  let cArgs := core.getAppArgs
                  let rArgs := rhs.headBeta.getAppArgs
                  let nf := fields.size
                  unless cArgs.size == rArgs.size && nf + 1 ≤ cArgs.size do return false
                  -- Up to definitional equality, not syntactic: `packField` recurses through a
                  -- function type even when nothing under it is nested, so a field like
                  -- `MessageData → MessageData` comes back eta-expanded and would otherwise look
                  -- transported when it is untouched.
                  let mut tf : Array Nat := #[]
                  for j in [0 : nf] do
                    unless ← isDefEq cArgs[j]! rArgs[j]! do tf := tf.push j
                  unless tf.size ≥ 1 && nf + tf.size ≤ cArgs.size do return false
                  let as := tf.map fun j => rArgs[j]!
                  let bs := tf.map fun j => cArgs[j]!
                  -- A hypothesis belongs to the field it is about, which is not the same as the
                  -- position of that field among the transported ones: a field can have a hypothesis
                  -- without being transported, as `List.cons`'s head does, and every slot after it
                  -- shifts. Pair them by which field the target's hypothesis mentions; the fields are
                  -- locals, so a syntactic occurrence settles it.
                  let mut Xs := #[]
                  let mut taken : Array Nat := #[]
                  for i in [0 : tf.size] do
                    let mut found := none
                    for kk in [nf : cArgs.size] do
                      if !taken.contains kk && (rArgs[kk]!.find? (· == as[i]!)).isSome then
                        found := some kk
                        break
                    let some kk := found | return false
                    taken := taken.push kk
                    Xs := Xs.push cArgs[kk]!
                  let tys ← as.mapM inferType
                  -- the round trip on each field is the equation the transport is along, at any arity
                  let hs ← as.mapM fun a => do
                    let some i := fields.idxOf? a | throwError "not a field"
                    fieldRoundTrip aux As As lvls (← whnf (← inferType fields[i]!)) a
                  -- A hypothesis for a field of function type mentions the field only pointwise, as
                  -- `∀ ys, motive (b ys)`, so abstracting `b` itself finds nothing and leaves a
                  -- motive constant in its argument. Take both: the motive over the field, which the
                  -- statement binds the hypothesis at, and the one over its codomain, which the
                  -- pointwise transport is along.
                  let motivesOf (b X A : Expr) : MetaM (Expr × Option Expr) := do
                    let ty ← inferType X
                    let whole ← withLocalDeclD `z A fun z => do
                      let m ← forallTelescope ty fun ys body => do
                        let abs ← kabstract body (mkAppN b ys).headBeta
                        mkForallFVars ys (abs.instantiate1 (mkAppN z ys))
                      mkLambdaFVars #[z] m
                    unless A.isForall do return (whole, none)
                    let pointwise ← forallTelescope A fun _ cod =>
                      forallTelescope ty fun ys body => do
                        let abs ← kabstract body (mkAppN b ys).headBeta
                        withLocalDeclD `z cod fun z => mkLambdaFVars #[z] (abs.instantiate1 z)
                    return (whole, some pointwise)
                  let ms ← (Array.range tf.size).mapM fun i => motivesOf bs[i]! Xs[i]! tys[i]!
                  let Ms := ms.map (·.1)
                  let hkTy ← whnf (← inferType la[5]!)
                  let hka := hkTy.getAppArgs
                  unless hka.size ≥ 3 do return false
                  -- the fields are locals here, so abstracting them directly gives `k`
                  let k ← mkLambdaFVars as hka[2]!
                  -- `F` is the core with the transported fields and their hypotheses abstracted
                  let F ← withLocalDeclsD (tys.map fun ty => (`z, fun _ => pure ty)) fun zs =>
                    withLocalDeclsD ((Array.range tf.size).map fun i =>
                        (`Y, fun _ => pure (mkApp Ms[i]! zs[i]!).headBeta)) fun ys => do
                      let mut cur := cArgs
                      for i in [0 : tf.size] do
                        cur := (cur.set! tf[i]! zs[i]!).set! taken[i]! ys[i]!
                      mkLambdaFVars (zs ++ ys) (mkAppN cFn cur)
                  -- how the rule states the hypothesis for field `i`: transported whole when the
                  -- field is plain, and pointwise, under as many `congrFun`s as the field has
                  -- binders, when it is a function
                  let slot (i : Nat) (e Y : Expr) : MetaM Expr := do
                    match ms[i]!.2 with
                    | none    => mkEqNDRec Ms[i]! Y e
                    | some Mp => forallTelescope tys[i]! fun ys _ => do
                      let mut he := e
                      for y in ys do
                        he ← mkCongrFun he y
                      mkLambdaFVars ys (← mkEqNDRec Mp (mkAppN Y ys) he)
                  -- The statement with the transported fields abstracted. Generating it, rather than
                  -- instantiating a law stated for a fixed number of fields, is what leaves both the
                  -- number of transported fields and the arity of each unbounded.
                  let stmtAt (zs : Array Expr) : MetaM Expr := do
                    let hkTy ← mkEq (mkAppN k zs) (mkAppN k as)
                    withLocalDeclD `hk hkTy fun hk =>
                      withLocalDeclsD ((Array.range tf.size).map fun i =>
                          (`e, fun _ => mkEq zs[i]! as[i]!)) fun es =>
                        withLocalDeclsD ((Array.range tf.size).map fun i =>
                            (`Y, fun _ => pure (mkApp Ms[i]! zs[i]!).headBeta)) fun Ys => do
                          let lhs ← mkEqNDRec N (mkAppN F (zs ++ Ys)) hk
                          let rs ← (Array.range tf.size).mapM fun i => slot i es[i]! Ys[i]!
                          mkForallFVars (#[hk] ++ es ++ Ys)
                            (← mkEq lhs (mkAppN F (as ++ rs)))
                  -- At the target fields every transport in the statement is along a reflexive
                  -- equation, and `Eq.rec` reduces on any proof of one, so it holds by reflexivity.
                  let reflHkTy ← mkEq (mkAppN k as) (mkAppN k as)
                  let mut pf ← withLocalDeclD `hk reflHkTy fun hk =>
                    withLocalDeclsD ((Array.range tf.size).map fun i =>
                        (`e, fun _ => mkEq as[i]! as[i]!)) fun es =>
                      withLocalDeclsD ((Array.range tf.size).map fun i =>
                          (`Y, fun _ => pure (mkApp Ms[i]! as[i]!).headBeta)) fun Ys => do
                        mkLambdaFVars (#[hk] ++ es ++ Ys) (← mkEqRefl (mkAppN F (as ++ Ys)))
                  -- transport the statement back one field at a time
                  let mut cur := as
                  for i in [0 : tf.size] do
                    let motive ← withLocalDeclD `z tys[i]! fun z => do
                      mkLambdaFVars #[z] (← stmtAt (cur.set! i z))
                    pf ← mkEqNDRec motive pf (← mkEqSymm hs[i]!)
                    cur := cur.set! i bs[i]!
                  let pfApplied := mkAppN pf (#[la[5]!] ++ hs ++ Xs)
                  -- run unification purely for its side effect on the level metavariables
                  let _ ← withTransparency .all (isDefEq (← inferType pfApplied) goal)
                  emit `ruleFields pfApplied
                byFields
              -- Lean 3 discharged the corresponding goals by rewriting with a simp set built from
              -- the pack/unpack specification lemmas. That does not transfer: the term to rewrite
              -- sits inside a dependent transport, so no motive is type correct and simp cannot
              -- enter it. Nothing is needed either, since the construction above is complete over
              -- the whole test suite, so there is no fallback here at all.
              explicit
          if proved then q := q + 1 else
            -- name every rule that is still open, so a change can be attributed to an
            -- individual goal instead of only to the aggregate
            openRules := openRules.push (origRecs1[i]! ++ rCtor)
      return (r, q, openRules)
    byRfl := byRfl + r
    byProof := byProof + q
    openRules := openRules ++ o
  return (origRecs1, byRfl, byProof, openRules, ← proofNames.get, ← ruleProofs.get)

/--
Derive each recursor the declaration introduces from the model, and check it against the one the
kernel declared.

Up to definitional equality, not syntactically. The two differ by beta for `Lean.Json` and
`Lean.PrefixTreeNode`, where the kernel keeps a redex, `(v : (fun x => PrefixTreeNode ..) k)`, that
opening and reclosing the binders here reduces away. Were the elimination to move out of the kernel
this derivation would be the declaration, and the reduced form is the better one to declare, so the
difference is not something to preserve.

Nothing depends on the result. It is here so that a derivation the kernel would come to rely on is
measured against the kernel's own answer for every nested inductive that gets compiled.
-/
def checkRestore (iv : InductiveVal) (types : Array InductiveType) (model : Array InductiveType)
    (origRecs : Array Name)
    (aux : Array (Expr × Name)) (params : Array Expr) (ren : Name → Name) : MetaM Unit := do
  for r in ← restoreRecursors iv types model origRecs aux params ren do
    let declared ← getConstInfoRec r.name
    -- Up to definitional equality, which is the criterion that matters: this derivation is meant to
    -- be right, not to reproduce the kernel term for term. Where they differ it is by beta, and the
    -- redex is lost in the elimination rather than here, since `withElimNested` opens and recloses
    -- binders and the model's own constructor fields arrive already reduced.
    unless ← isDefEq r.type declared.type do
      throwError "restoring {r.name} from the model gives{indentExpr r.type}\n\
        but the kernel declared{indentExpr declared.type}"
    unless r.numIndices == declared.numIndices do
      throwError "{r.name}: {r.numIndices} indices derived, {declared.numIndices} declared"
    unless r.rules.size == declared.rules.length do
      throwError "{r.name}: {r.rules.size} rules derived, {declared.rules.length} declared"
    for ((c, nf, rhs), rd) in r.rules.zip declared.rules.toArray do
      unless c == rd.ctor && nf == rd.nfields do
        throwError "{r.name}: rule derived as {c}/{nf}, declared {rd.ctor}/{rd.nfields}"
      unless ← isDefEq rhs rd.rhs do
        throwError "{r.name}: the rule for {rd.ctor} restores to{indentExpr rhs}\n\
          but the kernel declared{indentExpr rd.rhs}"

/--
Check that this model lines up with the kernel's, position by position: recursor family index
against model type, rule order, and every arity and flag.

The certificates do not subsume this. They pin down what the rules say, and say nothing about the
arities the recursors are declared with, from which `major_idx` is derived: get those wrong and iota
takes the wrong argument for the major premise. Since the kernel copies them off its own auxiliary
declaration, the only handle on them is that a second, independent elimination reconstructed the same
shape, which is what this compares.

`k` is in the list but cannot fire. `init_K_target` wants a non-mutual, single-constructor,
zero-field `Prop`, and an auxiliary block is mutual as soon as there is a nested occurrence, so it is
false on both sides for every nested inductive; measured as false for all 170 in core. It is checked
because it is cheap and because a change to either elimination that made it differ would be worth
hearing about.

`isRec` and `isReflexive` are also invisible to a rule, but they drive `brecOn` and `below`
generation rather than reduction, so getting them wrong loses a construction rather than soundness.
`isReflexive` is compared in one direction only, for the reason given at that line.
-/
def checkMetadata (iv : InductiveVal) (model : Array InductiveType) (origRecs : Array Name) :
    MetaM Unit := do
  unless model.size == origRecs.size do
    throwError "model has {model.size} types but the recursor family has {origRecs.size}"
  unless iv.numNested == model.size - iv.all.length do
    throwError "numNested is {iv.numNested} but the elimination created \
      {model.size - iv.all.length} auxiliary copies"
  for i in [0 : origRecs.size] do
    let o ← getConstInfoRec origRecs[i]!
    let m ← getConstInfoRec (mkRecName model[i]!.name)
    let chk (what a b : String) : MetaM Unit :=
      unless a == b do throwError "{origRecs[i]!}: {what} is {a}, the model implies {b}"
    chk "numParams" s!"{o.numParams}" s!"{m.numParams}"
    chk "numIndices" s!"{o.numIndices}" s!"{m.numIndices}"
    chk "numMotives" s!"{o.numMotives}" s!"{m.numMotives}"
    chk "numMinors" s!"{o.numMinors}" s!"{m.numMinors}"
    chk "k" s!"{o.k}" s!"{m.k}"
    chk "universe parameters" s!"{o.levelParams.length}" s!"{m.levelParams.length}"
    chk "rule count" s!"{o.rules.length}" s!"{m.rules.length}"
    for (ro, rm) in o.rules.zip m.rules do
      chk s!"nfields of {ro.ctor}" s!"{ro.nfields}" s!"{rm.nfields}"
  -- only the types the declaration actually introduces; the auxiliary copies are discarded
  for i in [0 : iv.all.length] do
    let o ← getConstInfoInduct iv.all[i]!
    let m ← getConstInfoInduct model[i]!.name
    let chk (what a b : String) : MetaM Unit :=
      unless a == b do throwError "{iv.all[i]!}: {what} is {a}, the model implies {b}"
    chk "numParams" s!"{o.numParams}" s!"{m.numParams}"
    chk "numIndices" s!"{o.numIndices}" s!"{m.numIndices}"
    chk "constructor count" s!"{o.ctors.length}" s!"{m.ctors.length}"
    chk "isRec" s!"{o.isRec}" s!"{m.isRec}"
    -- `add_inductive_fn::is_reflexive` asks `is_pi` of each field type, so it sees a field declared
    -- as `β fst` only once something has beta-reduced it to `fst → T`. Every telescope the generator
    -- opens and closes does, while the kernel's aux declaration keeps the redex, so the model can be
    -- reflexive where the declaration is not. Beta only ever exposes more `∀`, never fewer, so the
    -- other direction would mean the model really has lost a field.
    if o.isReflexive && !m.isReflexive then
      throwError "{iv.all[i]!}: isReflexive is true but the model is not reflexive"

end NestedGen

/-! ## End-to-end: model + packs for an existing nested inductive -/

namespace NestedGen

/--
What a certificate consists of, in the form the kernel needs in order to check it: the environment the
generator built, and the model constant standing for each constant of the declaration being certified.

The kernel looks the proofs up in `env` rather than being handed them, and states the propositions it
requires itself; `subst` is what lets it restate them over the model, where they have content, rather
than over the declaration, where they hold by construction and so say nothing. Looking a proof up is
not trusting it, since the kernel checks the term it finds. What the kernel does take on faith is that
the declarations in `env` were checked when they were added, which is the same thing it already
assumes of any environment the elaborator hands it.
-/
public structure Certificate where
  env    : Kernel.Environment
  /--
  The recursors this declaration introduces, derived from the model rather than read back, for the
  kernel to declare.
  -/
  recs   : Array RestoredRec
  /--
  Whether the model makes each declared type reflexive, in the order the declaration lists them.
  The kernel cannot read this off the presentation it was given: an occurrence under a redex hides
  the binder that makes the type reflexive, and the model has already reduced it away.
  -/
  reflexive : Array Bool

/--
What `buildModel` found: how many rules already held definitionally, how many it proved, which it left
open, and the correspondence between the declaration's constants and the model's.
-/
public structure Result where
  byRfl      : Nat
  byProof    : Nat
  openRules  : Array Name
  subst      : Array (Name × Name)
  proofNames : Array Name
  recs       : Array RestoredRec
  /-- Whether the model makes each declared type reflexive, in the order the declaration lists them. -/
  reflexive  : Array Bool

/--
Rebuild the model for the nested inductive `n` under the fresh prefix `pre`, add it, and generate
the bridges, surrogates and rule certificates over it. Returns the number of computation rules
that already held definitionally, the number discharged by a kernel-checked certificate, and the
number left open.
-/
public def buildModelFor (iv : InductiveVal) (types : Array InductiveType) (pre : Name)
    (sur : Name → Name) : MetaM (Option Result) :=
  -- Pin unification so the outcome does not depend on the caller's configuration: the transport laws
  -- are instantiated by higher-order unification, which needs the approximations the elaborator turns
  -- on but a bare `MetaM` does not. Approximation can only widen the search; a wrong instantiation
  -- still has to pass the kernel.
  withConfig (fun _ => { foApprox := true, ctxApprox := true }) do
  -- A rule counts as certified only once the kernel has accepted its proof, so the check cannot be
  -- deferred to a task nobody waits on. Under `Elab.async` every `addDecl` reports its constant
  -- immediately and checks it later, which would count rejected proofs as certified.
  withOptions (Elab.async.set · false) do
  withElimNested iv.levelParams iv.numParams types.toList fun model aux params => do
    -- no occurrence to unfold, so there is no model to build and nothing for the kernel to check
    -- against: this is the answer that routes the declaration back to `add_inductive_fn`
    if aux.isEmpty then return none
    let (model, aux) := renameModel model aux pre
    addDecl (.inductDecl iv.levelParams iv.numParams model.toList iv.isUnsafe)
    let numNested := model.size - types.size
    let reflexive ← types.mapIdxM fun i _ => do
      return (← getConstInfoInduct model[i]!.name).isReflexive
    let ren : Name → Name := (pre ++ ·)
    let names := (← withElimNested iv.levelParams iv.numParams types.toList
      (fun m _ _ => return m.map (·.name)))
    let mut origRecNames := types.map (mkRecName ·.name)
    for j in [1 : numNested + 1] do
      origRecNames := origRecNames.push ((mkRecName types[0]!.name).appendAfter s!"_{j}")
    let restored ← restoreRecursors iv types model origRecNames aux params ren
    -- An unsafe declaration gets its recursors derived but not certified. Nothing here could
    -- certify them: the bridges and the rule proofs are ordinary definitions and theorems, and
    -- neither may mention an unsafe constant. Such a declaration is outside the kernel's
    -- guarantees to begin with.
    if iv.isUnsafe then
      return some { byRfl := 0, byProof := 0, openRules := #[], subst := #[], proofNames := #[],
                    recs := restored, reflexive }
    mkPacks model aux params params iv.levelParams
    mkUnpacks model aux params iv.levelParams
    mkUnpackPacks model aux params params iv.levelParams
    mkPackUnpacks model aux params iv.levelParams
    -- the kernel's recursor types mention the original constructors, which in the surrogate
    -- world are the packing definitions, not the model's own constructors
    let ctorNames := (types.map (·.ctors.map (·.name) |>.toArray)).flatten.toList
    let mut recMap : NameMap Name := {}
    for j in [0 : origRecNames.size] do
      recMap := recMap.insert origRecNames[j]!
        ((ren names[0]!) ++ Name.mkSimple s!"rec_surr{j}")
    let fix := fun (e : Expr) => e.replace fun t => match t with
      | .const n us =>
        if names.contains n then some (.const (ren n) us)
        else if ctorNames.contains n then some (.const (ren n ++ `surr) us)
        else if let some r := recMap.find? n then some (.const r us)
        else none
      | _ => none
    let (origRecs, byRfl, byProof, openRules, proofNames, ruleProofs) ←
      mkSurrogates types iv.numParams model aux params iv.levelParams fix iv.all restored
    -- pair each rule with the theorem that discharges it; `none` means it holds definitionally
    let restored := restored.map fun r =>
      { r with proofs := r.rules.map fun (c, _, _) =>
          (ruleProofs.find? fun (rn, rc, _) => rn == r.name && rc == c).map (·.2.2) }
    -- when the kernel declares the derived recursors it calls this before adding them, so there is
    -- nothing to compare against; the comparison is what the tests and the older path rely on
    if (← getEnv).contains origRecs[0]! then
      checkMetadata iv model origRecs
      checkRestore iv types model origRecs aux params ren
    -- A layer of definitions carrying the declaration's own names, over the realisation built in
    -- the model's. Under the naming the kernel uses these are the declaration's names exactly, so
    -- what the certificate proves is stated in the vocabulary the kernel states its goals in.
    let surFix := fun (e : Expr) => e.replace fun t => match t with
      | .const n us =>
        if names.contains n || ctorNames.contains n || recMap.contains n then some (.const (sur n) us)
        else none
      | _ => none
    let alias (n : Name) (lps : List Name) (ty : Expr) (target : Name) : MetaM Unit := do
      unless sur n == target do
        addDecl (.defnDecl { name := sur n, levelParams := lps, type := surFix ty
                             value := mkConst target (lps.map Level.param)
                             hints := .abbrev, safety := .safe })
    for t in types do
      alias t.name iv.levelParams t.type (ren t.name)
    for t in types do
      for c in t.ctors do
        alias c.name iv.levelParams c.type (ren c.name ++ `surr)
    for r in restored do
      let some target := recMap.find? r.name | throwError "no surrogate for {r.name}"
      alias r.name r.levelParams r.type target
    let mut subst := names.map fun m => (m, sur m)
    for c in ctorNames do
      subst := subst.push (c, sur c)
    for r in origRecNames do
      subst := subst.push (r, sur r)
    return some { byRfl, byProof, openRules, subst, proofNames, recs := restored, reflexive }

/-- `buildModelFor`, reading the declaration out of the environment. Throws if `n` is not nested. -/
public def buildModel (n : Name) (pre : Name) : MetaM Result := do
  let iv ← getConstInfoInduct n
  let types ← iv.all.mapM fun m => do
    let jv ← getConstInfoInduct m
    let ctors ← jv.ctors.mapM fun c => do
      return { name := c, type := (← getConstInfo c).type : Constructor }
    return { name := m, type := jv.type, ctors }
  -- the declaration is already present, so here the realisation has to be named out of its way
  let some res ← buildModelFor iv types.toArray pre (`_surr ++ pre ++ ·)
    | throwError "{n} has no nested occurrence"
  return res

/-! ## Kernel entry point -/

/--
The constants the generator needs whatever the declaration looks like. The kernel certifies a
declaration at the point it is made, so before these exist there is nothing to reason with and
`certify` succeeds vacuously rather than rejecting a declaration it cannot reason about.

Only what the construction always uses, all declared in the first few hundred lines of
`Init.Prelude` and so in scope for every nested inductive there is, `Lean.Syntax` included. `funext`
is deliberately absent: it is reached only for a field of function type, of which nothing declared
before `Init.Core` has one, and listing it would skip every declaration before that point.
-/
def ingredients : Array Name :=
  #[``Eq, ``Eq.refl, ``Eq.ndrec, ``Eq.symm, ``congrArg, ``congr, ``congrFun, ``PUnit, ``PUnit.unit,
    ``True, ``True.intro]

/--
Certify every computation rule of the nested inductive `declName`, which must already be present in
`kenv` along with its constructors and recursors. Returns a message describing the failure, or
`none` if every rule was certified.

`environment::add_inductive` calls this once it has rewritten the checked mutual model back into the
nested presentation, which is the step the kernel does not otherwise check. Nothing here can license
a declaration: the model, the bridges and the rule proofs all go into a scratch environment that is
discarded, so the only possible effect is to reject.
-/
public def certifyCore (env : Environment) (iv : InductiveVal) (types : Array InductiveType)
    (sur : Name → Name) : IO (Except String (Option Certificate)) := do
  let ctx : Core.Context := {
    fileName := "<nested inductive certificate>"
    fileMap := default
    -- the certificate has to be decided here, not deferred to a task nobody waits on
    options := Elab.async.set {} false
    -- a heartbeat exception would reject a declaration for being slow to certify
    maxHeartbeats := 0
  }
  let act : MetaM (Option Result) := do
    -- The realisation carries the declaration's own names, so the kernel's goals need no
    -- translation. Its model sits under a prefix, since one of its types would otherwise claim
    -- the recursor name the realisation needs.
    let some res ← buildModelFor iv types (`_certify ++ iv.name) sur | return none
    unless res.openRules.isEmpty do
      throwError "{res.openRules.size} computation rule(s) left uncertified: {res.openRules}"
    return some res
  -- keep the environment rather than discarding it: it is what the kernel looks the proofs up in
  let core : CoreM (Option Result) := MetaM.run' act
  match ← (core.run ctx { env }).toIO' with
  | .ok (none, _) => return .ok none
  | .ok (some res, s) =>
    return .ok (some { env := s.env.toKernelEnv, recs := res.recs, reflexive := res.reflexive })
  | .error ex => return .error (← ex.toMessageData.toString)

/-- `certifyCore`, reading the declaration out of the kernel environment. -/
public def certify (kenv : Kernel.Environment) (declName : Name) :
    IO (Except String (Option Certificate)) := do
  let env ← Environment.ofKernelEnvForElab kenv {}
  if ingredients.any fun n => !env.contains n then
    return .ok none
  let some (.inductInfo iv) := env.find? declName | return .ok none
  -- unsafe declarations are outside the kernel's guarantees anyway
  if iv.isUnsafe then return .ok none
  let some types ← (do
      let ts ← iv.all.mapM fun m => do
        let some (.inductInfo jv) := env.find? m | return none
        let mut ctors := #[]
        for c in jv.ctors do
          let some ci := env.find? c | return none
          ctors := ctors.push { name := c, type := ci.type : Constructor }
        return some ({ name := m, type := jv.type, ctors := ctors.toList } : InductiveType)
      return ts.foldr (fun t acc => do return (← t) :: (← acc)) (some []))
    | return .ok none
  -- the declaration is already present, so the realisation has to be named out of its way
  certifyCore env iv types.toArray (`_surr ++ ·)

/--
`certifyCore`, working from the declaration the kernel was handed rather than from the environment,
which is how `add_inductive` reaches it: the certificate has to be in hand before anything is
declared, since the kernel takes the recursors and the reflexivity flags from it.

`ok none` means the declaration has no nested occurrence, which is how the kernel learns to declare
it itself. Deciding that here rather than in the kernel keeps one definition of what counts as an
occurrence instead of two that have to agree.
-/
@[export lean_certify_nested_inductive]
public def certifyDecl (kenv : Kernel.Environment) (d : Declaration) :
    IO (Except String (Option Certificate)) := do
  let .inductDecl lparams nparams types isUnsafe := d | return .ok none
  let types := types.toArray
  let some first := types[0]? | return .ok none
  let env ← Environment.ofKernelEnvForElab kenv {}
  -- Whether there is an occurrence to unfold, asked of the code that would unfold it. Purely
  -- syntactic and nothing is declared, so this is what every inductive pays to be routed.
  let detect : MetaM Bool :=
    withElimNested lparams nparams types.toList fun _ aux _ => return !aux.isEmpty
  let ctx : Core.Context := {
    fileName := "<nested inductive certificate>", fileMap := default
    options := Elab.async.set {} false, maxHeartbeats := 0
  }
  let nested ← match ← ((MetaM.run' detect : CoreM Bool).run ctx { env }).toIO' with
    | .error ex => return .error (← ex.toMessageData.toString)
    | .ok (b, _) => pure b
  if !nested then return .ok none
  -- an unsafe declaration is not certified, so it needs none of the ingredients
  if !isUnsafe && ingredients.any fun n => !env.contains n then
    return .error "a nested inductive was declared before the certificate's ingredients exist"
  -- the fields the generator reads; the rest are only meaningful once the type exists
  let iv : InductiveVal := {
    name := first.name, levelParams := lparams, type := first.type, numParams := nparams
    numIndices := 0, all := types.toList.map (·.name), ctors := first.ctors.map (·.name)
    numNested := 0, isRec := true, isUnsafe, isReflexive := false }
  certifyCore env iv types id

end NestedGen

end Lean.Meta
