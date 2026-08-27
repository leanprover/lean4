/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.LitValues
import Init.CbvSimproc
import Lean.Meta.Tactic.Cbv.CbvSimproc
import Lean.Meta.Tactic.Cbv.Util

namespace Lean.Meta.Tactic.Cbv

/-- Reduce `"abc" ++ "def"` to `"abcdef"` for literal strings. -/
builtin_cbv_simproc cbv_eval simpStringAppend (@HAppend.hAppend String String String _ _ _) := fun e => do
  let some a := Sym.getStringValue? e.appFn!.appArg! | return .rfl
  let some b := Sym.getStringValue? e.appArg! | return .rfl
  let result ← Sym.share <| toExpr (a ++ b)
  return .step result (← Sym.mkEqRefl result)

/-- Reduce `String.push "abc" 'd'` to `"abcd"` for literal strings and chars. -/
builtin_cbv_simproc cbv_eval simpStringPush (String.push _ _) := fun e => do
  let some s := Sym.getStringValue? e.appFn!.appArg! | return .rfl
  let some c := Sym.getCharValue? e.appArg! | return .rfl
  let result ← Sym.share <| toExpr (s.push c)
  return .step result (← Sym.mkEqRefl result)

/-- Reduce `String.singleton 'a'` to `"a"` for literal chars. -/
builtin_cbv_simproc cbv_eval simpStringSingleton (String.singleton _) := fun e => do
  let some c := Sym.getCharValue? e.appArg! | return .rfl
  let result ← Sym.share <| toExpr (String.singleton c)
  return .step result (← Sym.mkEqRefl result)

/-- Reduce `String.ofList ['a', 'b', 'c']` to `"abc"` for literal char lists. -/
builtin_cbv_simproc cbv_eval simpStringOfList (String.ofList _) := fun e => do
  let some elems := getListLitElems e.appArg! | return .rfl
  let mut s := ""
  for elem in elems do
    let some c := Sym.getCharValue? elem | return .rfl
    s := s.push c
  let result ← Sym.share <| toExpr s
  return .step result (← Sym.mkEqRefl result)

/-- Reduce `String.toList "abc"` to `['a', 'b', 'c']` for literal strings. -/
builtin_cbv_simproc cbv_eval simpStringToList (String.toList _) := fun e => do
  let some s := Sym.getStringValue? e.appArg! | return .rfl
  let result ← Sym.share <| toExpr s.toList
  return .step result (← Sym.mkEqRefl result)

end Lean.Meta.Tactic.Cbv
