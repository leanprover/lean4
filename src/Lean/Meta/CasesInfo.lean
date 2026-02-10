/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/

module
prelude
public import Lean.Meta.Basic
import Init.Data.Range.Polymorphic.Iterators

open Lean Meta

/-!
This modules defines the `CasesInfo` data structure and functions to obtain it.
It contains information about the structure of casesOn-like functions, namely of

* Plain `.casesOn` (one alternative per constructor)
* Per-constructor eliminations (with side condition, one alternative only)
* Sparse cases-on (only some constructors, with a catch-all)

It recognizes `.casesOn` by using `isCasesOnRecursor` (name + `isAuxDecl` env ext), and the others
via the `isSparseCasesOn` env ext.

It is used in particular by the code generator to replace calls to such functions with LCNF's
`cases` construct.

The `getSparseCasesInfo?` function calculates the `CasesInfo` from the type of the declaration, and
makes certain assumptions about their shapes. If this is too fragile, the `sparseCasesOn` env
extension could carry more information from which the shape can be calculated..
-/

public inductive CasesAltInfo where
  | ctor (ctorName : Name) (numFields : Nat) : CasesAltInfo
  | default (numHyps : Nat) : CasesAltInfo
deriving Inhabited

/--
Information about the shape of `casesOn`-like declarations.

We treat them uniformly in the code generator.
-/
public structure CasesInfo where
  declName     : Name
  indName      : Name
  arity        : Nat
  discrPos     : Nat
  altsRange    : Std.Rco Nat
  altNumParams : Array CasesAltInfo

public def CasesInfo.numAlts (c : CasesInfo) : Nat :=
  c.altNumParams.size

public def getCasesInfo? (declName : Name) : CoreM (Option CasesInfo) := do
  unless isCasesOnLike (← getEnv) declName do return none
  let info ← getConstVal declName
  MetaM.run' <|
    forallTelescope info.type fun xs r => do
      let arity := xs.size
      assert! r.isApp
      assert! r.appArg!.isFVar  -- major argument
      assert! r.getAppFn.isFVar -- motive
      let some discrPos := xs.idxOf? r.appArg! | unreachable!
      let some indName := (← inferType xs[discrPos]!).getAppFn.constName? | unreachable!
      -- We recognize the per-ctor elims side condition here
      let xsTys ← (xs.extract (discrPos+1)).mapM inferType
      let hasSideCondition : Bool := !xsTys.isEmpty && xsTys[0]!.getForallBody.getAppFn != r.getAppFn
      let altsRange := (discrPos + (if hasSideCondition then 2 else 1))...arity
      let altNumParams ← altsRange.toArray.mapM fun idx => do
        forallTelescope (xsTys[idx - discrPos - 1]!) fun ys mr => do
          assert! mr.isApp
          let motiveArg := mr.appArg!
          -- If the motive is applied to the major premise...
          if motiveArg.isFVar then
            -- Then this is the catch-all case of a sparse match
            assert! motiveArg == xs[discrPos]!
            return .default ys.size
          else
            -- Else we have a normal case
            let some ctorName := motiveArg.getAppFn.constName? | unreachable!
            let ctorVal ← getConstInfoCtor ctorName
            return .ctor ctorName ctorVal.numFields
      return some { declName, indName, arity, discrPos, altsRange, altNumParams }
