/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Meta.Basic
import Lean.AddDecl
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.AppBuilder

/-!  See `mkSparseCasesOn` below.  -/

namespace Lean.Meta

def mkNatNe (n m : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.ne_of_beq_eq_false)
    (mkNatLit n) (mkNatLit m) (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))

/--
This module creates sparse variants of `casesOn` that have arms only for some of the constructors,
offering a catch-all.

The minor arguments come in the order of the given `ctors` array.

The catch-all provides `x.ctorIdx ≠ i` hypotheses for each constructor `i` that is matched.

This is (or rather will be, currently it's doing the naive thing to get off the ground) implemented
internally by branching on the constructor index.
-/
public def mkSparseCasesOn (indName : Name) (ctors : Array Name) (declName : Name) : MetaM Unit := do
  let indInfo ← getConstInfoInduct indName
  for ctor in ctors do
    unless indInfo.ctors.contains ctor do
      throwError "mkSparseCasesOn: constructor {ctor} is not a constructor of {indName}"

  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstInfo casesOnName
  let ctorIdxName := mkCtorIdxName indName
  -- TODO: may not eliminiate into sort
  let l::lps := casesOnInfo.levelParams |
    throwError "mkSparseCasesOn: unexpected number of universe parameters in `{.ofConstName casesOnName}`"
  let u := mkLevelParam l
  let us := lps.map mkLevelParam

  let (value : Expr) ← forallTelescope casesOnInfo.type fun xs _ => do
    unless xs.size = indInfo.numParams + 1 + indInfo.numIndices + 1 + indInfo.ctors.length do
      throwError "mkSparseCasesOn: unexpected number of parameters in type of `{.ofConstName casesOnName}`"
    let params := xs[:indInfo.numParams]
    let motive := xs[indInfo.numParams]!
    let indices := xs[indInfo.numParams+1:indInfo.numParams+1+indInfo.numIndices]
    let major := xs[indInfo.numParams+1+indInfo.numIndices]!
    let minors := xs[indInfo.numParams+1+indInfo.numIndices+1:]

    let minors' ← ctors.mapM fun ctor => do
      let ctorInfo ← getConstInfoCtor ctor
      let minor := minors[ctorInfo.cidx]!
      pure minor

    let catchAllType ← id do
      let overlapTypes ← ctors.mapIdxM fun i ctor => do
        let ctorInfo ← getConstInfoCtor ctor
        let lhs := mkAppN (mkConst ctorIdxName us) (params ++ indices ++ #[major])
        let rhs := mkNatLit ctorInfo.cidx
        let neq := mkApp3 (mkConst ``Ne [1]) (mkConst ``Nat) lhs rhs
        let name := (`h).appendIndexAfter i
        pure (name, neq)
      withLocalDeclsDND overlapTypes fun hs =>
        mkForallFVars (indices ++ #[major] ++ hs) (mkAppN motive (indices ++ #[major]))

    withLocalDeclD `else catchAllType fun elseMinor => do
      let e := mkConst casesOnInfo.name (u :: us)
      let e := mkAppN e params
      let e := mkApp e motive
      let e := mkAppN e indices
      let e := mkApp e major
      let e := mkAppN e <| ← indInfo.ctors.toArray.mapM fun ctor => do
        if let some idx := ctors.idxOf? ctor then
          return  minors'[idx]!
        else
          let ctorInfo ← getConstInfoCtor ctor
          let idx := ctorInfo.cidx
          forallTelescope (← inferType (minors[ctorInfo.cidx]!)) fun fields _ => do
            let ctorApp := mkAppN (mkConst ctor us) (params ++ fields)
            let ctorAppType ← whnfD (← inferType ctorApp)
            let idxs := ctorAppType.getAppArgs[indInfo.numParams:]
            let e := mkAppN elseMinor (idxs ++ #[ctorApp])
            let e := mkAppN e <| ← ctors.mapM fun ctor => do
              let ctorInfo' ← getConstInfoCtor ctor
              let otherIdx := ctorInfo'.cidx
              return mkNatNe idx otherIdx
            mkLambdaFVars fields e
      mkLambdaFVars (params ++ #[motive] ++ indices ++ #[major] ++ minors' ++ #[elseMinor]) e

  -- logInfo m!"mkSparseCasesOn {declName} : {value}"
  let decl ← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType value))
    (value       := value)
    (hints       := ReducibilityHints.abbrev)
  addAndCompile (.defnDecl decl)

end Lean.Meta
