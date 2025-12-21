/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Simproc
import Lean.Meta.NatInstTesters
public section
namespace Lean.Meta.Grind.Arith.CommRing

/-
**Note**: It is safe to use (the more efficient) structural instances tests here because `grind` uses the canonicalizer.
-/
open Structural in
builtin_grind_propagator propagatePower ↑HPow.hPow := fun e => do
  -- **Note**: We are not checking whether the `^` instance is the expected ones.
  let_expr HPow.hPow α n α' _ a b := e | return ()
  let_expr Nat := n | return ()
  unless isSameExpr α α' do return ()
  traverseEqc b fun bENode => do
    let b' := bENode.self
    match_expr b' with
    | HAdd.hAdd n₁ n₂ n₃ inst b₁ b₂ =>
      unless isSameExpr n n₁ && isSameExpr n n₂ && isSameExpr n n₃ do return ()
      unless (← isInstHAddNat inst) do return ()
      let pwFn := e.appFn!.appFn!
      let r ← mkMul (mkApp2 pwFn a b₁) (mkApp2 pwFn a b₂)
      let r ← preprocess r
      internalize r.expr (← getGeneration e)
      let some h ← mkSemiringThm ``Grind.Semiring.pow_add_congr α | return ()
      let h := mkApp7 h a r.expr b b₁ b₂ (← mkEqProof b b') (← r.getProof)
      pushEq e r.expr h
    | _ => return ()

end Lean.Meta.Grind.Arith.CommRing
