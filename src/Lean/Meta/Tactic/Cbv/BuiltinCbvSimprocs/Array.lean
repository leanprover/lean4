/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.InferType
import Init.CbvSimproc
import Lean.Meta.Tactic.Cbv.CbvSimproc
import Lean.Meta.Tactic.Cbv.Util
import Init.GetElem

namespace Lean.Meta.Tactic.Cbv

/-- Extract elements from an array literal (`Array.mk` applied to a list literal). -/
def getArrayLitElems? (e : Expr) : Option <| Array Expr :=
  match_expr e with
  | Array.mk _ as => getListLitElems as
  | _ => none

/-- Reduce `#[...][n]` for literal arrays and literal `Nat` indices. -/
builtin_cbv_simproc cbv_eval simpArrayGetElem (@GetElem.getElem (Array _) Nat _ _ _ _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs n _ := e | return .rfl
  let some elems := getArrayLitElems? xs | return .rfl
  let some idx := Sym.getNatValue? n | return .rfl
  if h : idx < elems.size then
    let result := elems[idx]
    return .step result (← Sym.mkEqRefl result)
  else
    return .rfl

/-- Reduce `#[...][n]?` for literal arrays and literal `Nat` indices. -/
builtin_cbv_simproc cbv_eval simpArrayGetElem? (@GetElem?.getElem? (Array _) Nat _ _ _ _ _) := fun e => do
  let_expr GetElem?.getElem? _ _ α _ _ xs n := e | return .rfl
  let some elems := getArrayLitElems? xs | return .rfl
  let some idx := Sym.getNatValue? n | return .rfl
  let sortLevel ← Sym.getLevel α
  let .succ u := sortLevel | return .rfl
  let result ←
    if h : idx < elems.size then
      Sym.share <| mkApp2 (mkConst ``Option.some [u]) α elems[idx]
    else
      Sym.share <| mkApp (mkConst ``Option.none [u]) α
  return .step result (← Sym.mkEqRefl result)

end Lean.Meta.Tactic.Cbv
