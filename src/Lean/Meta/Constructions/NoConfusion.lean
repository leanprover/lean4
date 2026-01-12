/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
module

prelude
public import Lean.Meta.Basic
import Lean.AddDecl
import Lean.Meta.AppBuilder
import Lean.Meta.CompletionName
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim
import Lean.Meta.Tactic.Subst

namespace Lean

open Meta

/--
Constructs a lambda expression that returns the argument to the `noConfusion` principle for a given
constructor. In particular, returns
```
fun params x1 x2 x3 x1' x2' x3' => (x1 = x1' → x2 = x2' → x3 = x3' → P)
```
where `x1 x2 x3` and `x1' x2' x3'` are the parameters and  fields of a constructor application of
`ctorName`, omitting equalities between propositions and using `HEq` where needed.
-/
def mkNoConfusionCtorArg (ctorName : Name) (P : Expr) : MetaM Expr := do
  let ctorInfo ← getConstInfoCtor ctorName
  -- We bring the constructor's parameters into scope abstractly, this way
  -- we can check if we need to use HEq. (The concrete fields could allow Eq)
  forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs1 t1 => do
  forallTelescopeReducing t1 fun fields1 _ => do
  forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs2 t2 => do
  withPrimedNames xs2 do
  forallTelescopeReducing t2 fun fields2 _ => do
  withPrimedNames fields2 do
    let mut t := P
    for f1 in fields1.reverse, f2 in fields2.reverse do
      if (← isProof f1) then
        continue
      let name := (← f1.fvarId!.getUserName).appendAfter "_eq"
      let eq ← mkEqHEq f1 f2
      t := mkForall name .default eq t
    mkLambdaFVars (xs1 ++ fields1 ++ xs2 ++ fields2) t

register_builtin_option backward.linearNoConfusionType : Bool := {
  defValue := true
  descr    := "use the linear-size construction for the `noConfusionType` declaration of an inductive type. Set to false to use the previous, simpler but quadratic-size construction. "
}

def mkNoConfusionTypeName (indName : Name) : Name :=
  Name.str indName "noConfusionType"

def canUseLinear (indName : Name) : MetaM Bool := do
  unless backward.linearNoConfusionType.get (← getOptions) do return false
  -- Check if the prelude is loaded
  unless (← hasConst ``Eq.propIntro) do return false
  -- Check if we have the constructor elim helpers
  unless (← hasConst (mkCtorElimName indName)) do return false
  return true

def mkIfNatEq (P : Expr) (e1 e2 : Expr) («then» : Expr → MetaM Expr) («else» : Expr → MetaM Expr) : MetaM Expr := do
  let heq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) e1 e2
  let u ← getLevel P
  let e := mkApp3 (mkConst ``dite [u]) P heq (mkApp2 (mkConst ``Nat.decEq) e1 e2)
  let e := mkApp e (← withLocalDeclD `h heq (fun h => do mkLambdaFVars #[h] (← «then» h)))
  let e := mkApp e (← withLocalDeclD `h (mkNot heq) (fun h => do mkLambdaFVars #[h] (← «else» h)))
  pure e

def mkNoConfusionType (indName : Name) : MetaM Unit := do
  let declName := mkNoConfusionTypeName indName
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let useLinearConstruction :=
    (info.numCtors > 2) &&
    backward.linearNoConfusionType.get (← getOptions) &&
    (← hasConst (mkCtorElimName indName))
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let e := mkConst casesOnName (v.succ::us)
  let t ← inferType e
  let PType := mkSort v
  let e ← withLocalDeclD `P PType fun P => do
    forallBoundedTelescope t info.numParams fun xs1 t1 => do
    forallBoundedTelescope t info.numParams fun xs2 t2 => do
    withPrimedNames xs2 do
      let e := mkAppN e xs1
      let motive1 ← forallTelescope (← whnfD t1).bindingDomain! fun ys _ => mkLambdaFVars ys PType
      let t1 ← instantiateForall t1 #[motive1]
      let e := mkApp e motive1
      let motive2 ← forallTelescope (← whnfD t2).bindingDomain! fun ys _ => mkLambdaFVars ys PType
      let t2 ← instantiateForall t2 #[motive2]
      forallBoundedTelescope t1 (some (info.numIndices + 1)) fun ysx1 t1 => do -- indices and major
      forallBoundedTelescope t2 (some (info.numIndices + 1)) fun ysx2 _t2 => do -- indices and major
      withPrimedNames ysx2 do
        let e := mkAppN e ysx1
        let altTypes ← arrowDomainsN info.numCtors t1
        let alts ← altTypes.mapIdxM fun i altType => do
          forallTelescope altType fun zs1 _ => do
            if useLinearConstruction then
              let ctorIdxApp := mkAppN (mkConst (mkCtorIdxName indName) us) (xs2 ++ ysx2)
              let alt ← mkIfNatEq PType (ctorIdxApp) (mkRawNatLit i)
                («else» := fun _ => pure P) fun h => do
                let conName := info.ctors[i]!
                let withName := mkConstructorElimName indName conName
                let e := mkConst withName (v.succ :: us)
                let e := mkAppN e (xs2 ++ #[motive2] ++ ysx2 ++ #[h])
                let e := mkApp e <|
                  ← forallTelescopeReducing ((← whnf (← inferType e)).bindingDomain!) fun zs2 _ => do
                    let k := (← mkNoConfusionCtorArg conName P).beta (xs1 ++ zs1 ++ xs2 ++ zs2)
                    let t ← mkArrow k P
                    mkLambdaFVars zs2 t
                pure e
              mkLambdaFVars zs1 alt
            else
              let conName := info.ctors[i]!
              let alt := mkConst casesOnName (v.succ :: us)
              let alt := mkAppN alt (xs2 ++ #[motive2] ++ ysx2)
              let t2 ← inferType alt
              let altTypes2 ← arrowDomainsN info.numCtors t2
              let alts2 ← altTypes2.mapIdxM fun j altType2 => do
                forallTelescope altType2 fun zs2 _ => do
                  if i = j then
                    let k := (← mkNoConfusionCtorArg conName P).beta (xs1 ++ zs1 ++ xs2 ++ zs2)
                    let t ← mkArrow k P
                    mkLambdaFVars zs2 t
                  else
                    mkLambdaFVars zs2 P
              let alt := mkAppN alt alts2
              mkLambdaFVars zs1 alt
        let e := mkAppN e alts
        mkLambdaFVars (#[P] ++ xs1 ++ ysx1 ++ xs2 ++ ysx2) e

  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)
  ))
  modifyEnv fun env => addToCompletionBlackList env declName
  modifyEnv fun env => addProtected env declName
  setReducibleAttribute declName

/--
Given arrays `x1,x2,..,xn` and `y1,y2,..,yn`, bring fresh variables and expressions of types `x1 = y1`, `x2 = y2`,
.., `xn = yn` (using `HEq` where necessary) into scope.
-/
def withEqTelescope [Inhabited α] (xs ys : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  go xs.toList ys.toList #[]
where
  go | x::xs', y::ys', eqs => do
      let eq ← mkEqHEq x y
      let name := if xs.size > 1 then (`eq).appendIndexAfter (eqs.size + 1) else `eq
      withLocalDeclD name eq fun v =>
        go xs' ys' (eqs.push v)
      | _, _, eqs => k eqs


/-
Variant of `withEqTelescope`, but when `xi = yi`, no variable is introduced, and `Eq.refl` is used
for the expression, unless this is the last one. (This special case could be dropped if we do not
generate no-confusion principles for constructors with only prop-valued fields.)
-/
def withNeededEqTelescope [Inhabited α] (xs ys : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  go xs.toList ys.toList #[] #[]
where
  go | x::xs', y::ys', vs, eqs => do
      if !xs'.isEmpty && (← isDefEq x y) then
        let eq ← mkEqRefl x
        go xs' ys' vs (eqs.push eq)
      else
        let eq ← mkEqHEq x y
        let name := if xs.size > 1 then (`eq).appendIndexAfter (eqs.size + 1) else `eq
        withLocalDeclD name eq fun v =>
          go xs' ys' (vs.push v) (eqs.push v)
      | _, _, vs, eqs => k vs eqs

/--
Telescoping `mkEqNDRec`: given
* motive `∀ y1 .. yn, P y1 .. yn`
* expression of type `P x1 .. xn`
* produces an expression of type (x1 = y1) → .. → (xn = yn) → P y1 .. yn
  (possibly using `HEq`)
produce an expression of type `motive y1 … yn`
by repeatedly applying `Eq.ndRec` (and `eq_of_heq` if needed).
-/
def mkEqNDRecTelescope (motive : Expr) (e : Expr) (xs ys : Array Expr) : MetaM Expr := do
  trace[Meta.mkNoConfusion] m!"mkEqNDRecTelescope: {e}, xs = {xs}, ys = {ys}"
  assert! xs.size == ys.size
  withEqTelescope xs ys fun eqs => do
    let result ← mkFreshExprMVar (motive.beta ys)
    let mut mvarId := result.mvarId!
    let mut subst := {}
    for eq in eqs do
      -- TODO: Can we build this easily and directly tactic-free?
      let eq := subst.get eq.fvarId!
      mvarId.withContext do trace[Meta.mkNoConfusion] m!"substituting {eq}"
      let (subst', mvarId') ← Meta.substEq mvarId eq.fvarId! (fvarSubst := subst)
      subst := subst'
      mvarId := mvarId'
    let e := e.applyFVarSubst subst
    mvarId.withContext do trace[Meta.mkNoConfusion] m!"assigning {e} : {← inferType e} to\n{mvarId}"
    mvarId.assign e
    mkLambdaFVars eqs (← instantiateMVars result)


def mkNoConfusionCoreImp (indName : Name) : MetaM Unit := do
  let declName := Name.mkStr indName "noConfusion"
  let noConfusionTypeName := mkNoConfusionTypeName indName
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  trace[Meta.mkNoConfusion] m!"mkNoConfusionCoreImp for {declName}"
  let e ← forallBoundedTelescope (← inferType (mkConst noConfusionTypeName (v::us))) (some 1) fun xs t => do
    let P := xs[0]!
    forallBoundedTelescope t (some (info.numParams + info.numIndices + 1)) fun xs1 t => do -- params, indices and major
    forallBoundedTelescope t (some (info.numParams + info.numIndices + 1)) fun xs2 _ => do -- params, indices and major
    withImplicitBinderInfos ((xs1 ++ xs2).push P) do
      let params1 : Array Expr := xs1[:info.numParams]
      let ysx1    : Array Expr := xs1[info.numParams:]
      let target1 := mkAppN (mkConst noConfusionTypeName (v :: us)) (#[P] ++ xs1 ++ xs1)
      let motive1 ← mkLambdaFVars ysx1 target1
      let alts ← info.ctors.mapM fun ctor => do
        let ctorType ← inferType (mkAppN (mkConst ctor us) params1)
        forallTelescopeReducing ctorType fun fs1 _ => do
          let kType := (← mkNoConfusionCtorArg ctor P).beta (params1 ++ fs1 ++ params1 ++ fs1)
          withLocalDeclD `k kType fun k => do
            let mut e := k
            let eqns ← arrowDomainsN kType.getNumHeadForalls kType
            for eqn in eqns do
              if let some (_, x, _) := eqn.eq? then
                e := mkApp e (← mkEqRefl x)
              else if let some (_, x, _, _) := eqn.heq? then
                e := mkApp e (← mkHEqRefl x)
              else
                throwError "unexpected equation {eqn} in `mkNoConfusionCtorArg` for {ctor}"
            mkLambdaFVars (fs1 ++ #[k]) e
      let e := mkAppN (mkConst casesOnName (v :: us)) (params1 ++ #[motive1] ++ ysx1 ++ alts)
      let target2 := mkAppN (mkConst noConfusionTypeName (v :: us)) (#[P] ++ xs1 ++ xs2)
      let motive2 ← mkLambdaFVars xs2 target2
      let e ← mkEqNDRecTelescope motive2 e xs1 xs2
      mkLambdaFVars (#[P] ++ xs1 ++ xs2) e

  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)))
  setReducibleAttribute declName
  let arity  := 1 + 3 * (info.numParams + info.numIndices + 1)
  let lhsPos := 1 + info.numParams + info.numIndices
  let rhsPos := 1 + 2 * info.numParams + 2 * info.numIndices + 1
  modifyEnv fun env => markNoConfusion env declName (.regular arity lhsPos rhsPos)
  modifyEnv fun env => addProtected env declName

/--
Creates per-constructor no-confusion definitions. These specialize the general noConfusion
declaration to (homogeneous!) equalities between two applications of the same constructor, to
effectively cache the computation of `noConfusionType` for that constructor:

```
def L.cons.noConfusion.{u_1, u} : {α : Type u} → {P : Sort u_1} →
  {x : α} → {xs : L α} → {x' : α} → {xs' : L α} →
  L.cons x xs = L.cons x' xs' →
  (x = x' → xs = xs' → P) →
  P

def Vec.cons.noConfusion.{u_1, u} : {α : Type u} → {P : Sort u_1} →
  {n : Nat} → {x : α} → {xs : Vec α n} →
  {n' : Nat} → {x' : α} → {xs' : Vec α n'} →
  n + 1 = n' + 1 → Vec.cons x xs ≍ Vec.cons x' xs' →
  (n = n' → x = x' → xs ≍ xs' → P)
  → P
```

These are specialized to equal parameters. The main use of these theorems is `injection` through
`Meta.mkNoConfusion`, which deals with homogeneous equalities, so no need for the generality.

These still accept a heterogeneous equality between the two constructor applications: if we tried
to phrase this theroem with a homogeneous equality, this would force those constructor fields that
appear in indices to be equal, which is too strong: we can have homogenenous equalities between
two constructor applications with different fields but same indices.
-/
def mkNoConfusionCtors (declName : Name) : MetaM Unit := do
  -- Do not do anything unless can_elim_to_type.
  let .inductInfo indVal ← getConstInfo declName | return
  let recInfo ← getConstInfo (mkRecName declName)
  unless recInfo.levelParams.length > indVal.levelParams.length do return
  if (← isPropFormerType indVal.type) then return
  let noConfusionName := Name.mkStr declName "noConfusion"

  -- We take the level names from `.rec`, as that conveniently has an extra level parameter that
  -- is distinct from the ones from the inductive
  let (v::us) := recInfo.levelParams.map mkLevelParam | throwError "unexpected number of level parameters in {recInfo.name}"

  for ctor in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctor
    if ctorInfo.numFields > 0 then
      forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs t => do
      withLocalDeclD `P (.sort v) fun P =>
      forallBoundedTelescope t ctorInfo.numFields fun fields1 _ => do
      forallBoundedTelescope t ctorInfo.numFields fun fields2 _ => do
      withPrimedNames fields2 do
      withImplicitBinderInfos (xs ++ #[P] ++ fields1 ++ fields2) do
        let ctor1 := mkAppN (mkConst ctor us) (xs ++ fields1)
        let ctor2 := mkAppN (mkConst ctor us) (xs ++ fields2)
        let is1 := (← whnf (← inferType ctor1)).getAppArgsN indVal.numIndices
        let is2 := (← whnf (← inferType ctor2)).getAppArgsN indVal.numIndices
        withNeededEqTelescope (is1.push ctor1) (is2.push ctor2) fun eqvs eqs => do
          -- When the kernel checks this definition, it will perform the potentially expensive
          -- computation that `noConfusionType h` is equal to `$kType → P`
          let kType ← mkNoConfusionCtorArg ctor P
          let kType := kType.beta (xs ++ fields1 ++ xs ++ fields2)
          -- TODO: Turn HEq to Eq in kType
          withLocalDeclD `k kType fun k => do
            let mut e := mkConst noConfusionName (v :: us)
            e := mkAppN e (#[P] ++ xs ++ is1 ++ #[ctor1] ++ xs ++ is2 ++ #[ctor2])
            -- Pass rfl equalities for parameters
            for _ in [:xs.size] do
              let eq ← whnf (← whnfForall (← inferType e)).bindingDomain!
              if let some (_,i,_,_) := eq.heq? then
                e := mkApp e (← mkHEqRefl i)
              else if let some (_,i,_) := eq.eq? then
                e := mkApp e (← mkEqRefl i)
              else
                throwError "mkNoConfusion: unexpected equality `{eq}` as next argument to{inlineExpr (← inferType e)}"
            -- Equalities for indices. May require going from Eq to HEq
            for eq in eqs do
              let needsHEq := (← whnfForall (← inferType e)).bindingDomain!.isHEq
              if needsHEq && (← inferType eq).isEq then
                e := mkApp e (← mkHEqOfEq eq)
              else
                e := mkApp e eq
            e := mkApp e k
            e ← mkExpectedTypeHint e P
            e ← mkLambdaFVars (xs ++ #[P] ++ fields1 ++ fields2 ++ eqvs ++ #[k]) e

            let name := ctor.str "noConfusion"
            addDecl (.defnDecl (← mkDefinitionValInferringUnsafe
              (name        := name)
              (levelParams := recInfo.levelParams)
              (type        := (← inferType e))
              (value       := e)
              (hints       := ReducibilityHints.abbrev)
            ))
            setReducibleAttribute name
            let arity := ctorInfo.numParams + 1 + 2 * ctorInfo.numFields + eqvs.size
            let fields := kType.getNumHeadForalls
            modifyEnv fun env => markNoConfusion env name (.perCtor arity fields)

def mkNoConfusionCore (declName : Name) : MetaM Unit := do
  -- Do not do anything unless can_elim_to_type. TODO: Extract to util
  let .inductInfo indVal ← getConstInfo declName | return
  let recInfo ← getConstInfo (mkRecName declName)
  unless recInfo.levelParams.length > indVal.levelParams.length do return
  if (← isPropFormerType indVal.type) then return

  mkNoConfusionType declName
  mkNoConfusionCoreImp declName
  mkNoConfusionCtors declName

def mkNoConfusionEnum (enumName : Name) : MetaM Unit := do
  if (← getEnv).contains ``noConfusionEnum then
    mkNoConfusionType
    mkNoConfusion
  else
    -- `noConfusionEnum` was not defined yet, so we use `mkNoConfusionCore`
    mkNoConfusionCore enumName
where
  mkNoConfusionType : MetaM Unit := do
    let ConstantInfo.inductInfo info ← getConstInfo enumName | unreachable!
    let us := info.levelParams.map mkLevelParam
    let v ← mkFreshUserName `v
    let enumType := mkConst enumName us
    let sortV := mkSort (mkLevelParam v)
    withLocalDeclD `P sortV fun P =>
    withLocalDeclD `x enumType fun x =>
    withLocalDeclD `y enumType fun y => do
      let declType  ← mkForallFVars #[P, x, y] sortV
      let declValue ←
        if info.numCtors = 1 then
          mkLambdaFVars #[P, x, y] (← mkArrow P P)
        else
          let ctorIdx := mkConst (mkCtorIdxName enumName) us
          mkLambdaFVars #[P, x, y] (← mkAppM ``noConfusionTypeEnum #[ctorIdx, P, x, y])
      let declName  := Name.mkStr enumName "noConfusionType"
      addDecl <| Declaration.defnDecl {
        name        := declName
        levelParams := v :: info.levelParams
        type        := declType
        value       := declValue
        safety      := DefinitionSafety.safe
        hints       := ReducibilityHints.abbrev
      }
      setReducibleAttribute declName

  mkNoConfusion : MetaM Unit := do
    let ConstantInfo.inductInfo info ← getConstInfo enumName | unreachable!
    let us := info.levelParams.map mkLevelParam
    let v ← mkFreshUserName `v
    let enumType := mkConst enumName us
    let sortV := mkSort (mkLevelParam v)
    let ctorIdx := mkConst (mkCtorIdxName enumName) us
    let noConfusionType := mkConst (Name.mkStr enumName "noConfusionType") (mkLevelParam v :: us)
    withLocalDecl `P BinderInfo.implicit sortV fun P =>
    withLocalDecl `x BinderInfo.implicit enumType fun x =>
    withLocalDecl `y BinderInfo.implicit enumType fun y => do
    withLocalDeclD `h (← mkEq x y) fun h => do
      let declType  ← mkForallFVars #[P, x, y, h] (mkApp3 noConfusionType P x y)
      let declValue ← mkLambdaFVars #[P, x, y, h] <| ← do
        if info.numCtors = 1 then
          withLocalDeclD `p P fun p => mkLambdaFVars #[p] p
        else
          mkAppOptM ``noConfusionEnum #[none, none, none, ctorIdx, P, x, y, h]
      let declName  := Name.mkStr enumName "noConfusion"
      addDecl <| Declaration.defnDecl {
        name        := declName
        levelParams := v :: info.levelParams
        type        := declType
        value       := declValue
        safety      := DefinitionSafety.safe
        hints       := ReducibilityHints.abbrev
      }
      setReducibleAttribute declName
      modifyEnv fun env => markNoConfusion env declName (.regular 4 1 2)

public def mkNoConfusion (declName : Name) : MetaM Unit := do
  withTraceNode `Meta.mkNoConfusion (fun _ => return m!"{declName}") do
  if (← isEnumType declName) then
    mkNoConfusionEnum declName
  else
    mkNoConfusionCore declName


builtin_initialize
  registerTraceClass `Meta.mkNoConfusion

end Lean
