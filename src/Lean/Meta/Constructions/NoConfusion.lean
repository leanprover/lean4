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
import Lean.Meta.NatTable
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.SameCtorUtils
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
where `x1 x2 x3` and `x1' x2' x3'` are the fields of a constructor application of `ctorName`,
omitting equalities between propositions and using `HEq` where needed.
-/
def mkNoConfusionCtorArg (ctorName : Name) (P : Expr) : MetaM Expr := do
  let ctorInfo ← getConstInfoCtor ctorName
  -- We bring the constructor's parameters into scope abstractly, this way
  -- we can check if we need to use HEq. (The concrete fields could allow Eq)
  forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs t => do
    forallTelescopeReducing t fun fields1 _ => do
    forallTelescopeReducing t fun fields2 _ => do
    let mut t := P
    for f1 in fields1.reverse, f2 in fields2.reverse do
      if (← isProof f1) then
        continue
      let name := (← f1.fvarId!.getUserName).appendAfter "_eq"
      let eq ← mkEqHEq f1 f2
      t := mkForall name .default eq t
    mkLambdaFVars (xs ++ fields1 ++ fields2) t

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
  let e ← forallBoundedTelescope t info.numParams fun xs t => do
    let e := mkAppN e xs
    let PType := mkSort v
    withLocalDeclD `P PType fun P => do
      let motive ← forallTelescope (← whnfD t).bindingDomain! fun ys _ =>
        mkLambdaFVars ys PType
      let ti ← instantiateForall t #[motive]
      let e := mkApp e motive
      forallBoundedTelescope ti (some (info.numIndices + 1)) fun ysx1 t => do -- indices and major
      forallBoundedTelescope ti (some (info.numIndices + 1)) fun ysx2 _ => do -- indices and major
        let e := mkAppN e ysx1
        let altTypes ← arrowDomainsN info.numCtors t
        let alts ← altTypes.mapIdxM fun i altType => do
          forallTelescope altType fun zs1 _ => do
            if useLinearConstruction then
              let ctorIdxApp := mkAppN (mkConst (mkCtorIdxName indName) us) (xs ++ ysx2)
              let alt ← mkIfNatEq PType (ctorIdxApp) (mkRawNatLit i)
                («else» := fun _ => pure P) fun h => do
                let conName := info.ctors[i]!
                let withName := mkConstructorElimName indName conName
                let e := mkConst withName (v.succ :: us)
                let e := mkAppN e (xs ++ #[motive] ++ ysx2 ++ #[h])
                let e := mkApp e <|
                  ← forallTelescopeReducing ((← whnf (← inferType e)).bindingDomain!) fun zs2 _ => do
                    let k := (← mkNoConfusionCtorArg conName P).beta (xs ++ zs1 ++ zs2)
                    let t ← mkArrow k P
                    mkLambdaFVars zs2 t
                pure e
              mkLambdaFVars zs1 alt
            else
              let conName := info.ctors[i]!
              let alt := mkConst casesOnName (v.succ :: us)
              let alt := mkAppN alt (xs ++ #[motive] ++ ysx2)
              let t2 ← inferType alt
              let altTypes2 ← arrowDomainsN info.numCtors t2
              let alts2 ← altTypes2.mapIdxM fun j altType2 => do
                forallTelescope altType2 fun zs2 _ => do
                  if i = j then
                    let k := (← mkNoConfusionCtorArg conName P).beta (xs ++ zs1 ++ zs2)
                    let t ← mkArrow k P
                    mkLambdaFVars zs2 t
                  else
                    mkLambdaFVars zs2 P
              let alt := mkAppN alt alts2
              mkLambdaFVars zs1 alt
        let e := mkAppN e alts
        mkLambdaFVars (xs ++ #[P] ++ ysx1 ++ ysx2) e

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
Given arrays `x1,x2,..,xn` and `y1,y2,..,yn`, bring fresh variables of types `x1 ≍ y1`, `x2 ≍ y2`,
.., `xn ≍ yn` (`HEq` for uniformity) into scope.
-/
def withHEqTelescope [Inhabited α] (xs ys : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  assert! xs.size == ys.size
  let mut eqs : Array (Name × Expr) := #[]
  for x in xs, y in ys, i in [0:xs.size] do
    let eq ← mkHEq x y
    let n := if xs.size > 1 then (`eq).appendIndexAfter (i + 1) else `eq
    eqs := eqs.push (n, eq)
  withLocalDeclsDND eqs k

/--
Telescoping `mkEqNDRec`: given
* motive `∀ y1 .. yn, P y1 .. yn`
* expression of type `P x1 .. xn`
* produces an expression of type (x1 ≍ y1) → .. → (xn ≍ yn) → P y1 .. yn
produce an expression of type `motive y1 … yn`
by repeatedly applying `eq_of_heq` and `Eq.ndRec`
-/
def mkHEqNDRecTelescope (motive : Expr) (e : Expr) (xs ys : Array Expr) : MetaM Expr := do
  trace[Meta.mkNoConfusion] m!"mkEqNDRecTelescope: {e}, xs = {xs}, ys = {ys}"
  assert! xs.size == ys.size
  withHEqTelescope xs ys fun eqs => do
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
  let e ← forallBoundedTelescope (← inferType (mkConst noConfusionTypeName (v::us))) (some (info.numParams + 1)) fun xs t => do
    let params : Array Expr := xs[:info.numParams]
    let P := xs[info.numParams]!
    forallBoundedTelescope t (some (info.numIndices + 1)) fun ysx1 _ => do -- indices and major
    forallBoundedTelescope t (some (info.numIndices + 1)) fun ysx2 _ => do -- indices and major
      let target1 := mkAppN (mkConst noConfusionTypeName (v :: us)) (params ++ #[P] ++ ysx1 ++ ysx1)
      let motive1 ← mkLambdaFVars ysx1 target1
      let alts ← info.ctors.mapM fun ctor => do
        let ctorType ← inferType (mkAppN (mkConst ctor us) params)
        forallTelescopeReducing ctorType fun fs _ => do
          let kType := (← mkNoConfusionCtorArg ctor P).beta (params ++ fs ++ fs)
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
            mkLambdaFVars (fs ++ #[k]) e
      let e := mkAppN (mkConst casesOnName (v :: us)) (params ++ #[motive1] ++ ysx1 ++ alts)
      let target2 := mkAppN (mkConst noConfusionTypeName (v :: us)) (params ++ #[P] ++ ysx1 ++ ysx2)
      let motive2 ← mkLambdaFVars ysx2 target2
      let e ← mkHEqNDRecTelescope motive2 e ysx1 ysx2
      mkLambdaFVars (params ++ #[P] ++ ysx1 ++ ysx2) e

  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)))
  setReducibleAttribute declName
  modifyEnv fun env => markNoConfusion env declName
  modifyEnv fun env => addProtected env declName

/--
Creates per-constructor no-confusion definitions. These specialize the general noConfusion
declaration to equalities between two applications of the same constructor, to effectively cache
the computation of `noConfusionType` for that constructor:

```
def L.cons.noConfusion.{u_1, u} : {α : Type u} → (P : Sort u_1) →
  (x : α) → (xs : L α) → (x' : α) → (xs' : L α) →
  L.cons x xs = L.cons x' xs' →
  (x = x' → xs = xs' → P) →
  P
```

TODO: Update
These definitions are less expressive than the general `noConfusion` principle when there are
complicated indices. In particular they assume that all fields of the constructor that appear
in its type are equal already. The `mkNoConfusion` app builder falls back to the general principle
if the per-constructor one does not apply. Example:
```
inductive T : Nat → Type where | mk n : T (n - 2)
example (h : T.mk 1 = T.mk 2) : False := T.noConfusion h (fun h12 => by contradiction)
```

At some point I tried to be clever and remove hypotheses that are trivial (`n = n →`), but that
made it harder for, say, `injection` to know how often to `intro`. So we just keep them.
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
      let e ← withLocalDeclD `P (.sort v) fun P =>
        forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs t => do
        forallBoundedTelescope t ctorInfo.numFields fun fields1 _ => do
        forallBoundedTelescope t ctorInfo.numFields fun fields2 _ => do
          let ctor1 := mkAppN (mkConst ctor us) (xs ++ fields1)
          let ctor2 := mkAppN (mkConst ctor us) (xs ++ fields2)
          let is1 := (← whnf (← inferType ctor1)).getAppArgsN indVal.numIndices
          let is2 := (← whnf (← inferType ctor2)).getAppArgsN indVal.numIndices
          -- TODO: get indices, assert equalities
          withHEqTelescope (is1.push ctor1) (is2.push ctor2) fun eqs => do
            -- When the kernel checks this definition, it will perform the potentially expensive
            -- computation that `noConfusionType h` is equal to `$kType → P`
            let kType ← mkNoConfusionCtorArg ctor P
            let kType := kType.beta (xs ++ fields1 ++ fields2)
            withLocalDeclD `k kType fun k => do
              let e := mkConst noConfusionName (v :: us)
              let e := mkAppN e (xs ++ #[P] ++ is1 ++ #[ctor1] ++ is2 ++ #[ctor2] ++ eqs ++ #[k])
              let e ← mkExpectedTypeHint e P
              mkLambdaFVars (xs ++ #[P] ++ fields1 ++ fields2 ++ eqs ++ #[k]) e
      let name := ctor.str "noConfusion"
      addDecl (.defnDecl (← mkDefinitionValInferringUnsafe
        (name        := name)
        (levelParams := recInfo.levelParams)
        (type        := (← inferType e))
        (value       := e)
        (hints       := ReducibilityHints.abbrev)
      ))
      setReducibleAttribute name
      -- The compiler has special support for `noConfusion`. So lets mark this as
      -- macroInline to not generate code for all these extra definitions, and instead
      -- let the compiler unfold this to then put the custom code there
      setInlineAttribute name (kind := .macroInline)


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
      addAndCompile <| Declaration.defnDecl {
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
      addAndCompile <| Declaration.defnDecl {
        name        := declName
        levelParams := v :: info.levelParams
        type        := declType
        value       := declValue
        safety      := DefinitionSafety.safe
        hints       := ReducibilityHints.abbrev
      }
      setReducibleAttribute declName
      modifyEnv fun env => markNoConfusion env declName

public def mkNoConfusion (declName : Name) : MetaM Unit := do
  withTraceNode `Meta.mkNoConfusion (fun _ => return m!"{declName}") do
  if (← isEnumType declName) then
    mkNoConfusionEnum declName
  else
    mkNoConfusionCore declName


builtin_initialize
  registerTraceClass `Meta.mkNoConfusion

end Lean
