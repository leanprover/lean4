/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.AddDecl
public import Lean.Meta.AppBuilder
public import Lean.Meta.CompletionName
import Lean.Meta.NatTable
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim

/-!
This module produces a construction for the `noConfusionType` that is linear in size in the number of
constructors of the inductive type. This is in contrast to the previous construction (defined in
`no_confusion.cpp`), that is quadratic in size due to nested `.brecOn` applications.

We still use the old construction when processing the prelude, for the few inductives that we need
until we have the machinery for this construction (`Nat`, `Bool`, `Decidable`).

The main trick is to use the per-constructor `.elim` combinator that is like `cases` but has only
one arm, and is thus constant in size. See `Lean.Meta.Constructions.CtorLeim.lean` for that construction.

See the `linearNoConfusion.lean` test for exemplary output of this translation (checked to be
up-to-date).

This module is written in a rather manual style, constructing the `Expr` directly. It's best
read with the expected output to the side.
-/

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

(Exported from here because we also need it in `mkNoConfusionCtors`.)
-/
public def mkNoConfusionCtorArg (ctorName : Name) (P : Expr) : MetaM Expr := do
  let ctorInfo ← getConstInfoCtor ctorName
  -- We bring the constructor's parameters into scope abstractly, this way
  -- we can check if we need to use HEq. (The concrete fields could allow Eq)
  forallBoundedTelescope ctorInfo.type ctorInfo.numParams fun xs t => do
    forallTelescopeReducing t fun fields1 _ => do
    forallTelescopeReducing t fun fields2 _ => do
    let mut eqs := #[]
    for f1 in fields1, f2 in fields2 do
      if (← isProof f1) then
        continue
      eqs := eqs.push (← mkEqHEq f1 f2)
    mkLambdaFVars (xs ++ fields1 ++ fields2) (← mkArrowN eqs P)

namespace NoConfusionLinear

register_builtin_option backwards.linearNoConfusionType : Bool := {
  defValue := true
  descr    := "use the linear-size construction for the `noConfusionType` declaration of an inductive type. Set to false to use the previous, simpler but quadratic-size construction. "
}

def mkNoConfusionTypeName (indName : Name) : Name :=
  Name.str indName "noConfusionType"

public def canUse (indName : Name) : MetaM Bool := do
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

public def mkNoConfusionTypeLinear (indName : Name) : MetaM Unit := do
  let declName := mkNoConfusionTypeName indName
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
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
          let e := mkApp e x1
          forallBoundedTelescope t info.numCtors fun alts _ => do
            let alts' ← alts.mapIdxM fun i alt => do
              let altType ← inferType alt
              forallTelescope altType fun zs1 _ => do
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
            let e := mkAppN e alts'
            let e ← mkLambdaFVars (xs ++ ys ++ #[P, x1, x2]) e
            pure e

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

end Lean.NoConfusionLinear
