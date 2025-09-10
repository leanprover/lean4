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
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim

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
public def mkNoConfusionCtorArg (ctorName : Name) (P : Expr) : MetaM Expr := do
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

register_builtin_option backwards.linearNoConfusionType : Bool := {
  defValue := true
  descr    := "use the linear-size construction for the `noConfusionType` declaration of an inductive type. Set to false to use the previous, simpler but quadratic-size construction. "
}

def mkNoConfusionTypeName (indName : Name) : Name :=
  Name.str indName "noConfusionType"

def canUseLinear (indName : Name) : MetaM Bool := do
  unless backwards.linearNoConfusionType.get (← getOptions) do return false
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

public def mkNoConfusionType (indName : Name) : MetaM Unit := do
  let declName := mkNoConfusionTypeName indName
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let useLinearConstruction :=
    (info.numCtors > 2) &&
    backwards.linearNoConfusionType.get (← getOptions) &&
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
      let t ← instantiateForall t #[motive]
      let e := mkApp e motive
      forallBoundedTelescope t info.numIndices fun ys t => do
        let e := mkAppN e ys
        let xType := mkAppN (mkConst indName us) (xs ++ ys)
        withLocalDeclD `x1 xType fun x1 => do
        withLocalDeclD `x2 xType fun x2 => do
          let t ← instantiateForall t #[x1]
          let altTypes ← arrowDomainsN info.numCtors t
          let e := mkApp e x1
          let alts ← altTypes.mapIdxM fun i altType => do
            forallTelescope altType fun zs1 _ => do
              if useLinearConstruction then
                let ctorIdxApp := mkAppN (mkConst (mkCtorIdxName indName) us) (xs ++ ys ++ #[x2])
                let alt ← mkIfNatEq PType (ctorIdxApp) (mkRawNatLit i)
                  («else» := fun _ => pure P) fun h => do
                  let conName := info.ctors[i]!
                  let withName := mkConstructorElimName indName conName
                  let e := mkConst withName (v.succ :: us)
                  let e := mkAppN e (xs ++ #[motive] ++ ys ++ #[x2, h])
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
                let alt := mkAppN alt (xs ++ #[motive] ++ ys ++ #[x2])
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
          mkLambdaFVars (xs ++ ys ++ #[P, x1, x2]) e

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

def mkNoConfusionCoreImp (indName : Name) : MetaM Unit := do
  let declName := Name.mkStr indName "noConfusion"
  let noConfusionTypeName := Name.mkStr indName "noConfusionType"
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let e ← forallBoundedTelescope (← inferType (mkConst noConfusionTypeName (v::us))) (info.numParams + info.numIndices) fun xs _ => do
    let params : Array Expr := xs[:info.numParams]
    let is : Array Expr := xs[info.numParams:]
    let PType := mkSort v
    withLocalDecl `P .implicit PType fun P =>
    withLocalDecl `x1 .implicit (mkAppN (mkConst indName us) xs) fun x1 =>
    withLocalDecl `x2 .implicit (mkAppN (mkConst indName us) xs) fun x2 => do
    withLocalDeclD `h12 (← mkEq x1 x2) fun h12 => do
      let target1 := mkAppN (mkConst noConfusionTypeName (v :: us)) (xs ++ #[P, x1, x1])
      let motive1 ← mkLambdaFVars (is ++ #[x1]) target1
      let e ← withLocalDeclD `h11 (← mkEq x1 x1) fun h11 => do
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
        let e := mkAppN (mkConst casesOnName (v :: us)) (params ++ #[motive1] ++ is ++ #[x1] ++ alts)
        mkLambdaFVars #[h11] e
      let target2 := mkAppN (mkConst noConfusionTypeName (v :: us)) (xs ++ #[P, x1, x2])
      let motive2 ← mkLambdaFVars #[x2] (← mkArrow (← mkEq x1 x2) target2)
      let e ← mkEqNDRec motive2 e h12
      let e := mkApp e h12
      mkLambdaFVars (xs ++ #[P, x1, x2, h12]) e

  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)))
  setReducibleAttribute declName
  modifyEnv fun env => markNoConfusion env declName
  modifyEnv fun env => addProtected env declName


def mkNoConfusionCore (declName : Name) : MetaM Unit := do
  -- Do not do anything unless can_elim_to_type. TODO: Extract to util
  let .inductInfo indVal ← getConstInfo declName | return
  let recInfo ← getConstInfo (mkRecName declName)
  unless recInfo.levelParams.length > indVal.levelParams.length do return
  if (← isPropFormerType indVal.type) then return

  mkNoConfusionType declName
  mkNoConfusionCoreImp declName


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
