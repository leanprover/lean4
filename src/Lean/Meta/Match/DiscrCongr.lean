/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Lean.Meta.AbstractNestedProofs

namespace Lean.Meta.Match

/--
The kind of discriminant congruence lemma. Determines whether the lemma will use `HEq` in parameters
and/or in the result.
-/
inductive DiscrCongrKind where
  /--
  Use a nondependent motive and only use `Eq` in parameters and as a result.
  Equalities may be omitted for some discriminants due to dependence.
  -/
  | nondep
  /--
  Use a dependent motive, `Eq` for parameters and `HEq` as a result.
  Equalities may be omitted for some discriminants due to dependence.
  -/
  | dep
  -- TODO: `complete` variant for `HEq` parameters
deriving Inhabited, Hashable, DecidableEq

def discrCongrPrefix := "discr_congr"
def discrCongrNondep := discrCongrPrefix ++ "_nd"
def discrCongrDep := discrCongrPrefix ++ "_dep"

def DiscrCongrKind.nameSuffix : DiscrCongrKind → String
  | .nondep => discrCongrNondep
  | .dep => discrCongrDep

/-
We generate the discriminant congruence lemmas on demand (like splitter and equation lemmas),
and do not save them on .olean files.
-/
builtin_initialize discrCongrExt : EnvExtension (PHashMap (Name × DiscrCongrKind) (Name × Array Bool)) ←
  -- Using `local` allows us to use the extension in `realizeConst` without specifying `replay?`.
  -- The resulting state can still be accessed on the generated declarations using `findStateAsync`;
  -- see below
  registerEnvExtension (pure {}) (asyncMode := .local)

def registerDiscrCongr (matchDeclName : Name) (kind : DiscrCongrKind)
    (congrName : Name) (mask : Array Bool) : CoreM Unit := do
  modifyEnv fun env => discrCongrExt.modifyState env fun map =>
    map.insert (matchDeclName, kind) (congrName, mask)

/--
Returns an expression of type `goal` if `goal` is of the form `∀ (b : α) (h : a = b) ..., P b ...`
and `hyp : P a ...`. `neqs` represents the amount of equalities to substitute.
-/
private def solveBySubstitution (neqs : Nat) (goal hyp : Expr) : Expr := Id.run do
  match neqs with
  | 0 => return hyp
  | neqs + 1 =>
    let .forallE _ _ (.forallE _ eq@(mkApp3 (.const _ us) α v _) b _) _ := goal | unreachable!
    let motive := .lam `x α (.lam `h eq b .default) .default
    let newGoal := b.instantiateRev #[v, mkApp2 (.const ``rfl us) α v]
    let inner := solveBySubstitution neqs newGoal hyp
    return mkApp4 (.const ``Eq.rec (levelZero :: us)) α v motive inner

/--
Make an equality hypothesis for every discriminant where `mask` is `true`.
-/
private def withDiscrCongrEqs (discrBody : Expr) (ndiscrs : Nat)
    (discrs : Array Expr) (mask : Array Bool)
    (k : Array (Option (Expr × Expr)) → MetaM α) : MetaM α :=
  go discrBody 0 #[]
where
  go (body : Expr) (i : Nat) (acc : Array (Option (Expr × Expr))) : MetaM α := do
    if i < ndiscrs then
      let .forallE nm t b bi := body | unreachable!
      if mask[i]! = false then
        go (b.instantiate1 discrs[i]!) (i + 1) (acc.push none)
      else
        withLocalDecl nm bi t fun var => do
          let eqT := mkApp3 (.const ``Eq [← getLevel t]) t discrs[i]! var
          withLocalDeclD `heq eqT fun eq => do
            go b (i + 1) (acc.push (var, eq))
    else
      k acc
  termination_by ndiscrs - i

/--
Compute right-hand side discriminants. Rewritten proofs are put into auxiliary theorems.
-/
private def mkDiscrParams
    (discrs : Array Expr) (cvars : Array (Option (Expr × Expr)))
    (info : FunInfo) : MetaM (Array Expr) :=
  go 0 #[]
where
  go (i : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
    if hi : i < cvars.size then
      match cvars[i] with
      | some (var, _eq) => go (i + 1) (acc.push var)
      | none =>
        let info := info.paramInfo[i]!
        if info.isProp && info.backDeps.any (cvars[·]!.isSome) then
          go (i + 1) (acc.push (← writeProof i info acc))
        else
          go (i + 1) (acc.push discrs[i]!)
    else
      return acc
  termination_by cvars.size - i

  writeProof (i : Nat) (info : ParamInfo) (acc : Array Expr) : MetaM Expr := do
    let hyp := discrs[i]!
    let prevVars := info.backDeps.map (discrs[·]!)
    let newVars := info.backDeps.map (acc[·]!)
    let prevType ← inferType hyp
    let newType := prevType.replaceFVars prevVars newVars
    let depCVars := info.backDeps.flatMap (match cvars[·]! with | none => #[] | some (a, b) => #[a, b])
    let newType ← mkForallFVars depCVars newType
    let proof := solveBySubstitution (depCVars.size / 2) newType hyp
    return mkAppN proof depCVars

/--
Compute right-hand side alternatives.
-/
private def mkAltParam (dInfos : Array DiscrInfo)
    (newDiscrs : Array Expr)
    (cvars : Array (Option (Expr × Expr)))
    (alt : Expr) : MetaM Expr := do
  let altType ← inferType alt
  forallTelescope altType fun params _ => do
    go params.size dInfos.size params params
where
  go (i j : Nat) (params : Array Expr) (fvars : Array Expr) : MetaM Expr := do
    let j + 1 := j | mkLambdaFVars fvars (mkAppN alt params)
    let some nm := dInfos[j]!.hName? | go i j params fvars
    let i := i - 1
    let heq := params[i]!
    let type ← inferType heq
    let v' := newDiscrs[j]!
    if cvars[j]!.isNone ∧ v'.isFVar then
      -- unchanged
      go i j params fvars
    else if let mkApp3 (.const ``Eq us) α v r := type then
      let α' ← inferType v'
      withLocalDeclD nm (mkApp3 (.const ``Eq us) α' v' r) fun heq' =>
        let prf :=
          match cvars[j]! with
          | some (_, eq) => mkApp6 (.const ``Eq.trans us) α v v' r eq heq'
          | none =>
            -- apply proof irrelevance
            mkApp3 (.const ``rfl us) α v r
        let params := params.set! i prf
        let fvars := fvars.set! i heq'
        go i j params fvars
    else
      let mkApp4 (.const ``HEq us) α v β r := type |
        throwError "unexpected hypothesis type {type}"
      let α' ← inferType v'
      withLocalDeclD nm (mkApp4 (.const ``HEq us) α' v' β r) fun heq' =>
        let prf :=
          match cvars[j]! with
          | some (_, eq) => mkApp7 (.const ``heq_of_eq_of_heq us) α β v v' r eq heq'
          | none =>
            -- apply proof irrelevance
            mkApp4 (mkConst ``proof_irrel_heq) α β v r
        let params := params.set! i prf
        let fvars := fvars.set! i heq'
        go i j params fvars

private def getForallBody : Expr → Expr
  | .forallE _ _ b _ => getForallBody b
  | e => e

private def reduceMotiveApps (e : Expr) (ndiscrs : Nat) : Expr :=
  match e, ndiscrs with
  | .forallE _ t b _, ndiscrs + 1 => e.updateForallE! t (reduceMotiveApps b ndiscrs)
  | .forallE _ t b _, 0 => e.updateForallE! (reduceArm t) (reduceMotiveApps b 0)
  | e, _ => e.headBeta
where
  reduceArm (e : Expr) : Expr :=
    match e with
    | .forallE _ t b _ => e.updateForallE! t (reduceArm b)
    | e => e.headBeta

private def withMotive (type : Expr) (kind : DiscrCongrKind) (ndiscrs : Nat)
    (k : Expr → Expr → Expr → MetaM α) : MetaM α := do
  let .forallE nm t b bi := type | unreachable!
  match kind with
  | .nondep =>
    let t' := getForallBody t
    withLocalDecl nm bi t' fun motive => do
      let expr ← forallTelescope t fun vars _ => mkLambdaFVars vars motive
      k motive expr (reduceMotiveApps (b.instantiate1 expr) ndiscrs)
  | .dep => withLocalDecl nm bi t fun motive => k motive motive (b.instantiate1 motive)

/--
Generates the discriminant congruence principle for a matcher and returns its name and a mask.

The first arguments of the congruence principle are exactly the same as the parameters of the
`match` application. The remaining arguments are (alternating) right-hand side discriminants and
equalities relating them with left-hand side discriminants (i.e. `(a' : α) (ha : a = a') ...`).
The result is a heterogenous equality of the match applications.

However, not all discriminants have equalities associated to them, in particular proofs and values
with (non-proof) forward dependencies. Which of the discriminants that is, is recorded in the
returned mask -- there is an equality associated to the `i`th discriminant (from 0) exactly if
`mask[i]` is `true`.

This congruence principle is used by `simp` to implement discriminant congruence on `match`
applications.
-/
def getDiscrCongr (matchDeclName : Name) (kind : DiscrCongrKind) : MetaM (Name × Array Bool) := do
  let baseName := mkPrivateName (← getEnv) matchDeclName
  let discrCongrName := .str baseName kind.nameSuffix
  realizeConst matchDeclName discrCongrName (go discrCongrName)
  return discrCongrExt.findStateAsync (← getEnv) discrCongrName |>.find! (matchDeclName, kind)
where go discrCongrName := withConfig (fun c => { c with etaStruct := .none }) do
  let some matcher ← getMatcherInfo? matchDeclName | throwError "'{matchDeclName}' is not a matcher function"
  let cval ← getConstVal matchDeclName
  let uelim :=
    match matcher.uElimPos? with
    | none => levelZero
    | some idx => .param cval.levelParams[idx]!
  forallBoundedTelescope cval.type matcher.numParams fun params body =>
  withMotive body kind matcher.numDiscrs fun motiveVar motive discrBody =>
  forallTelescope discrBody fun fvars lhsType => do -- discrs + alts
    let discrs := fvars.extract 0 matcher.numDiscrs
    let alts := fvars.extract matcher.numDiscrs
    let matchBase := mkAppN (.const matchDeclName (cval.levelParams.map Level.param)) params
    let matchBase := .app matchBase motive
    let info ← getFunInfoNArgs matchBase matcher.numDiscrs
    let mut mask : Array Bool := #[]
    for paramInfo in info.paramInfo do
      if paramInfo.isProp then
        mask := mask.push false
      else
        for dep in paramInfo.backDeps do
          mask := mask.set! dep false
        mask := mask.push true
    withDiscrCongrEqs discrBody matcher.numDiscrs discrs mask fun cvars => do -- congruence vars
      let lhs := mkAppN matchBase fvars
      let rhsDiscrs ← mkDiscrParams discrs cvars info
      let rhsType := (mkAppN motive rhsDiscrs).headBeta -- motive
      let rhsAlts ←
        if matcher.getNumDiscrEqs = 0 then
          -- plain `match` without equations, most common, just forward alternatives
          pure alts
        else
          -- special handling for equations
          alts.mapM (mkAltParam matcher.discrInfos rhsDiscrs cvars)
      let rhs := mkAppN (mkAppN matchBase rhsDiscrs) rhsAlts
      let rhs ← withDeclNameForAuxNaming discrCongrName (abstractNestedProofs rhs)
      let (eq, refl) :=
        match kind with
        | .nondep =>
          (mkApp3 (.const ``Eq [uelim]) lhsType lhs rhs,
            mkApp2 (.const ``rfl [uelim]) lhsType.headBeta lhs)
        | .dep =>
          (mkApp4 (.const ``HEq [uelim]) lhsType lhs rhsType rhs,
            mkApp2 (.const ``HEq.rfl [uelim]) lhsType.headBeta lhs)
      let allCVars := cvars.flatMap fun | none => #[] | some (a, b) => #[a, b]
      let goal ← mkForallFVars allCVars eq
      let proof := solveBySubstitution (allCVars.size / 2) goal refl
      let type ← mkForallFVars (params.push motiveVar ++ fvars) goal
      let proof ← mkLambdaFVars (params.push motiveVar ++ fvars) proof
      addDecl <| Declaration.thmDecl {
        name := discrCongrName
        levelParams := cval.levelParams
        type
        value := proof
      }
      registerDiscrCongr matchDeclName kind discrCongrName mask

private def isDiscrCongrName? (env : Environment) (n : Name) : Option (Name × DiscrCongrKind) := do
  let .str n s := n | none
  let mut n := n; let mut s := s
  if "_proof_".isPrefixOf s then -- nested proofs
    let .str n' s' := n | none
    n := n'; s := s'
  n ← privateToUserName? n
  let kind ←
    if s == discrCongrNondep then some .nondep
    else if s == discrCongrDep then some .dep
    else none
  guard <| isMatcherCore env n
  return (n, kind)

builtin_initialize registerReservedNamePredicate (isDiscrCongrName? · · |>.isSome)

builtin_initialize registerReservedNameAction fun name => do
  let some (p, kind) := isDiscrCongrName? (← getEnv) name | return false
  let _ ← MetaM.run' <| getDiscrCongr p kind
  return true

end Lean.Meta.Match
