/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Refl

namespace Lean.Meta.Match

/- We generate the equations and splitter on demand, and do not save them on .olean files. -/
builtin_initialize discrCongrExt : EnvExtension (PHashMap Name (Name × Array Bool)) ←
  -- Using `local` allows us to use the extension in `realizeConst` without specifying `replay?`.
  -- The resulting state can still be accessed on the generated declarations using `findStateAsync`;
  -- see below
  registerEnvExtension (pure {}) (asyncMode := .local)

def registerDiscrCongr (matchDeclName : Name) (congrName : Name) (mask : Array Bool) : CoreM Unit := do
  modifyEnv fun env => discrCongrExt.modifyState env fun map =>
    map.insert matchDeclName (congrName, mask)

/--
Returns an expression of type `goal` if `goal` is of the form `∀ (b : α) (h : a = b) ..., P b ...`
and `hyp : P a ...`. `neqs` represents the number of equalities to substitute.
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
private def mkDiscrParams (decl : Name) (lparams : List Name) (params : Array Expr)
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

    let allVars := params ++ info.backDeps.map (discrs[·]!) |>.push hyp
    let auxThmName := decl ++ `_aux |>.appendIndexAfter (i + 1)
    let type ← mkForallFVars allVars newType
    let value ← mkLambdaFVars allVars proof
    addDecl <| Declaration.thmDecl {
      name := auxThmName
      levelParams := lparams
      type, value
    }
    return mkAppN (mkAppN (.const auxThmName (lparams.map Level.param)) allVars) depCVars

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
def getDiscrCongr (matchDeclName : Name) : MetaM (Name × Array Bool) := do
  let baseName := mkPrivateName (← getEnv) matchDeclName
  let discrCongrName := .str baseName "discr_congr"
  realizeConst matchDeclName discrCongrName (go discrCongrName)
  return discrCongrExt.findStateAsync (← getEnv) discrCongrName |>.find! matchDeclName
where go discrCongrName := withConfig (fun c => { c with etaStruct := .none }) do
  let some matcher ← getMatcherInfo? matchDeclName | throwError "'{matchDeclName}' is not a matcher function"
  let cval ← getConstVal matchDeclName
  let uelim :=
    match matcher.uElimPos? with
    | none => levelZero
    | some idx => .param cval.levelParams[idx]!
  forallBoundedTelescope cval.type matcher.getFirstDiscrPos fun params discrBody => -- params + motive
  forallTelescope discrBody fun fvars lhsType => do -- discrs + alts
    let discrs := fvars.extract 0 matcher.numDiscrs
    let alts := fvars.extract matcher.numDiscrs
    let matchBase := mkAppN (.const matchDeclName (cval.levelParams.map Level.param)) params
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
      let rhsDiscrs ← mkDiscrParams discrCongrName cval.levelParams params.pop discrs cvars info
      let rhsType := mkAppN params.back! rhsDiscrs -- motive
      let rhsAlts ←
        if matcher.getNumDiscrEqs = 0 then
          -- plain `match` without equations, most common, just forward alternatives
          pure alts
        else
          -- special handling for equations
          alts.mapM (mkAltParam matcher.discrInfos rhsDiscrs cvars)
      let rhs := mkAppN (mkAppN matchBase rhsDiscrs) rhsAlts
      let heq := mkApp4 (.const ``HEq [uelim]) lhsType lhs rhsType rhs
      let allCVars := cvars.flatMap fun | none => #[] | some (a, b) => #[a, b]
      let goal ← mkForallFVars allCVars heq
      let refl := mkApp2 (.const ``HEq.rfl [uelim]) lhsType lhs
      let proof := solveBySubstitution (allCVars.size / 2) goal refl
      let type ← mkForallFVars (params ++ fvars) goal
      let proof ← mkLambdaFVars (params ++ fvars) proof
      addDecl <| Declaration.thmDecl {
        name := discrCongrName
        levelParams := cval.levelParams
        type
        value := proof
      }
      registerDiscrCongr matchDeclName discrCongrName mask

private def isDiscrCongrName? (env : Environment) (n : Name) : Option Name := do
  let .str n s := n | none
  let mut n := n; let mut s := s
  if "_aux_".isPrefixOf s && (s.drop "_aux_".length).isNat then
    let .str n' s' := n | none
    n := n'; s := s'
  n ← privateToUserName? n
  guard <| s == "discr_congr" && isMatcherCore env n
  return n

builtin_initialize registerReservedNamePredicate (isDiscrCongrName? · · |>.isSome)

builtin_initialize registerReservedNameAction fun name => do
  let some p := isDiscrCongrName? (← getEnv) name | return false
  let _ ← MetaM.run' <| getDiscrCongr p
  return true

end Lean.Meta.Match
