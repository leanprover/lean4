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

public section

/-!
This module produces a construction for the `noConfusionType` that is linear in size in the number of
constructors of the inductive type. This is in contrast to the previous construction (defined in
`no_confusion.cpp`), that is quadratic in size due to nested `.brecOn` applications.

We still use the old construction when processing the prelude, for the few inductives that we need
until below (`Nat`, `Bool`, `Decidable`).

The main trick is to use a `withCtor` helper that is like a match with one constructor pattern and
one catch-all pattern, and thus linear in size. And the helper itself is a single function
definition, rather than one for each constructor, using a `withCtorType` helper in the function.

See the `linearNoConfusion.lean` test for exemplary output of this translation (checked to be
up-to-date).

The `withCtor` functions could be generally useful, but for that they should probably eliminate into
`Sort _` rather than `Type _`, and then writing the `withCtorType` function runs into universe level
confusion, which may be solvable if the kernel had more complete univere level normalization.
Until then we put these helper in the `noConfusionType` namespace to indicate that they are not
general purpose.

This module is written in a rather manual style, constructing the `Expr` directly. It's best
read with the expected output to the side.
-/

namespace Lean.NoConfusionLinear

open Meta

/--
List of constants that the linear `noConfusionType` construction depends on.
-/
def deps : Array Lean.Name :=
  #[ ``Nat.lt, ``cond, ``Nat, ``PUnit, ``Eq, ``Not, ``dite, ``Nat.decEq, ``Nat.blt ]

def mkNatLookupTable (n : Expr) (es : Array Expr) (default : Expr) : MetaM Expr := do
  let type ← inferType default
  let u ← getLevel type
  let rec go (start stop : Nat) (hstart : start < stop := by omega) (hstop : stop ≤ es.size := by omega) : MetaM Expr := do
    if h : start + 1 = stop then
      return es[start]
    else
      let mid := (start + stop) / 2
      let low ← go start mid
      let high ← go mid stop
      return mkApp4 (mkConst ``cond [u]) type (mkApp2 (mkConst ``Nat.blt) n (mkRawNatLit mid)) low high
  if h : es.size = 0 then
    pure default
  else
    go 0 es.size

def mkWithCtorTypeName (indName : Name) : Name :=
  Name.str indName "noConfusionType" |>.str "withCtorType"

def mkWithCtorName (indName : Name) : Name :=
  Name.str indName "noConfusionType" |>.str "withCtor"

def mkNoConfusionTypeName (indName : Name) : Name :=
  Name.str indName "noConfusionType"

def mkWithCtorType (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let indTyCon := mkConst indName us
  let indTyKind ← inferType indTyCon
  let indLevel ← getLevel indTyKind
  let e ← forallBoundedTelescope indTyKind info.numParams fun xs  _ => do
    withLocalDeclD `P (mkSort v.succ) fun P => do
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
      let default ← mkArrow (mkConst ``PUnit [indLevel]) P
      let es ← info.ctors.toArray.mapM fun ctorName => do
        let ctor := mkAppN (mkConst ctorName us) xs
        let ctorType ← inferType ctor
        let argType ← forallTelescope ctorType fun ys _ =>
          mkForallFVars ys P
        mkArrow (mkConst ``PUnit [indLevel]) argType
      let e ← mkNatLookupTable ctorIdx es default
      mkLambdaFVars ((xs.push P).push ctorIdx) e

  let declName := mkWithCtorTypeName indName
  addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)
  ))
  modifyEnv fun env => addToCompletionBlackList env declName
  modifyEnv fun env => addProtected env declName
  setReducibleAttribute declName

def mkWithCtor (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let withCtorTypeName := mkWithCtorTypeName indName
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let indTyCon := mkConst indName us
  let indTyKind ← inferType indTyCon
  let indLevel ← getLevel indTyKind
  let e ← forallBoundedTelescope indTyKind info.numParams fun xs t => do
    withLocalDeclD `P (mkSort v.succ) fun P => do
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
      let withCtorTypeNameApp := mkAppN (mkConst withCtorTypeName (v :: us)) (xs.push P)
      let kType := mkApp withCtorTypeNameApp  ctorIdx
      withLocalDeclD `k kType fun k =>
      withLocalDeclD `k' P fun k' =>
      forallBoundedTelescope t info.numIndices fun ys t' => do
        let t' ← whnfD t'
        assert! t'.isSort
        withLocalDeclD `x (mkAppN indTyCon (xs ++ ys)) fun x => do
          let e := mkConst (mkCasesOnName indName) (v.succ :: us)
          let e := mkAppN e xs
          let motive ← mkLambdaFVars (ys.push x) P
          let e := mkApp e motive
          let e := mkAppN e ys
          let e := mkApp e x
          let alts ← info.ctors.toArray.mapIdxM fun i ctorName => do
            let ctor := mkAppN (mkConst ctorName us) xs
            let ctorType ← inferType ctor
            forallTelescope ctorType fun zs _ => do
              let heq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) ctorIdx (mkRawNatLit i)
              let «then» ← withLocalDeclD `h heq fun h => do
                let e ← mkEqNDRec (motive := withCtorTypeNameApp) k h
                let e := mkApp e (mkConst ``PUnit.unit [indLevel])
                let e := mkAppN e zs
                -- ``Eq.ndrec
                mkLambdaFVars #[h] e
              let «else» ← withLocalDeclD `h (mkNot heq) fun h =>
                mkLambdaFVars #[h] k'
              let alt := mkApp5 (mkConst ``dite [v.succ])
                  P heq (mkApp2 (mkConst ``Nat.decEq) ctorIdx (mkRawNatLit i))
                  «then» «else»
              mkLambdaFVars zs alt
          let e := mkAppN e alts
          mkLambdaFVars (xs ++ #[P, ctorIdx, k, k'] ++ ys ++ #[x]) e

  let declName := mkWithCtorName indName
  -- not compiled to avoid old code generator bug #1774
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

def mkNoConfusionTypeLinear (indName : Name) : MetaM Unit := do
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
                let alt := mkConst (mkWithCtorName indName) (v :: us)
                let alt := mkAppN alt xs
                let alt := mkApp alt PType
                let alt := mkApp alt (mkRawNatLit i)
                let k ← forallTelescopeReducing (← inferType alt).bindingDomain! fun zs2 _ => do
                  let eqs ← (Array.zip zs1 zs2[1...*]).filterMapM fun (z1,z2) => do
                    if (← isProof z1) then
                      return none
                    else
                      return some (← mkEqHEq z1 z2)
                  let k ← mkArrowN eqs P
                  let k ← mkArrow k P
                  mkLambdaFVars zs2 k
                let alt := mkApp alt k
                let alt := mkApp alt P
                let alt := mkAppN alt ys
                let alt := mkApp alt x2
                mkLambdaFVars zs1 alt
            let e := mkAppN e alts'
            let e ← mkLambdaFVars #[x1, x2] e
            let e ← mkLambdaFVars #[P] e
            let e ← mkLambdaFVars ys e
            let e ← mkLambdaFVars xs e
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
