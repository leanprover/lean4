/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.NamedPatterns
import Lean.Meta.MatchUtil
import Lean.Meta.AppBuilder
import Init.Data.Nat.Order
import Init.Data.Order.Lemmas

public section

/-!
This module has telescope functions for matcher alts. They are primarily used
in `Match.MatchEqs`, but also in `MatcherApp.Transform`, hence the separate module.
-/

namespace Lean.Meta.Match
/--
  Similar to `forallTelescopeReducing`, but

  1. Eliminates arguments for named parameters and the associated equation proofs.

  2. Instantiate the `Unit` parameter of an otherwise argumentless alternative.

  It does not handle the equality parameters associated with the `h : discr` notation.

  The continuation `k` takes four arguments `ys args mask type`.
  - `ys` are variables for the hypotheses that have not been eliminated.
  - `args` are the arguments for the alternative `alt` that has type `altType`. `ys.size <= args.size`
  - `mask[i]` is true if the hypotheses has not been eliminated. `mask.size == args.size`.
  - `type` is the resulting type for `altType`.

  We use the `mask` to build the splitter proof. See `mkSplitterProof`.

  This can be used to use the alternative of a match expression in its splitter.
-/
public partial def forallAltVarsTelescope (altType : Expr) (altInfo : AltParamInfo)
  (k : (patVars : Array Expr) → (args : Array Expr) → (mask : Array Bool) → (type : Expr) → MetaM α) : MetaM α := do
  assert! altInfo.numOverlaps = 0
  if altInfo.hasUnitThunk then
    let type ← whnfForall altType
    let type ← Match.unfoldNamedPattern type
    let type ← instantiateForall type #[mkConst ``Unit.unit]
    k #[] #[mkConst ``Unit.unit] #[false] type
  else
    go #[] #[] #[] 0 altType
where
  go (ys : Array Expr) (args : Array Expr) (mask : Array Bool) (i : Nat) (type : Expr) : MetaM α := do
    let type ← whnfForall type

    if i < altInfo.numFields then
      let Expr.forallE n d b .. := type
        | throwError "expecting {altInfo.numFields} parameters, but found type{indentExpr altType}"

      let d ← Match.unfoldNamedPattern d
      withLocalDeclD n d fun y => do
        let typeNew := b.instantiate1 y
        if let some (_, lhs, rhs) ← matchEq? d then
          if lhs.isFVar && ys.contains lhs && args.contains lhs && isNamedPatternProof typeNew y then
              let some j  := ys.finIdxOf? lhs | unreachable!
              let ys      := ys.eraseIdx j
              let some k  := args.idxOf? lhs | unreachable!
              let mask    := mask.set! k false
              let args    := args.map fun arg => if arg == lhs then rhs else arg
              let arg     ← mkEqRefl rhs
              let typeNew := typeNew.replaceFVar lhs rhs
              return ← withReplaceFVarId lhs.fvarId! rhs do
              withReplaceFVarId y.fvarId! arg do
                go ys (args.push arg) (mask.push false) (i+1) typeNew
        go (ys.push y) (args.push y) (mask.push true) (i+1) typeNew
    else
      let type ← Match.unfoldNamedPattern type
      k ys args mask type

  isNamedPatternProof (type : Expr) (h : Expr) : Bool :=
    Option.isSome <| type.find? fun e =>
      if let some e := Match.isNamedPattern? e then
        e.appArg! == h
      else
        false


/--
  Extension of `forallAltTelescope` that continues further:

  Equality parameters associated with the `h : discr` notation are replaced with `rfl` proofs.
  Recall that this kind of parameter always occurs after the parameters corresponding to pattern
  variables.

  The continuation `k` takes four arguments `ys args mask type`.
  - `ys` are variables for the hypotheses that have not been eliminated.
  - `eqs` are variables for equality hypotheses associated with discriminants annotated with `h : discr`.
  - `args` are the arguments for the alternative `alt` that has type `altType`. `ys.size <= args.size`
  - `mask[i]` is true if the hypotheses has not been eliminated. `mask.size == args.size`.
  - `type` is the resulting type for `altType`.

  We use the `mask` to build the splitter proof. See `mkSplitterProof`.

  This can be used to use the alternative of a match expression in its splitter.
-/
public partial def forallAltTelescope (altType : Expr) (altInfo : AltParamInfo) (numDiscrEqs : Nat)
    (k : (ys : Array Expr) → (eqs : Array Expr) → (args : Array Expr) → (mask : Array Bool) → (type : Expr) → MetaM α)
    : MetaM α := do
  forallAltVarsTelescope altType altInfo fun ys args mask altType => do
    go ys #[] args mask 0 altType
where
  go (ys : Array Expr) (eqs : Array Expr) (args : Array Expr) (mask : Array Bool) (i : Nat) (type : Expr) : MetaM α := do
    let type ← whnfForall type
    if i < numDiscrEqs then
      let Expr.forallE n d b .. := type
        | throwError "expecting {numDiscrEqs} equalities, but found type{indentExpr altType}"
      let arg ← if let some (_, _, rhs) ← matchEq? d then
        mkEqRefl rhs
      else if let some (_, _, _, rhs) ← matchHEq? d then
        mkHEqRefl rhs
      else
        throwError "unexpected match alternative type{indentExpr altType}"
      withLocalDeclD n d fun eq => do
        let typeNew := b.instantiate1 eq
        go ys (eqs.push eq) (args.push arg) (mask.push false) (i+1) typeNew
    else
      let type ← unfoldNamedPattern type
      k ys eqs args mask type
