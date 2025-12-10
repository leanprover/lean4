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
public section
namespace Lean.Meta.Grind

/-!
This file defines propagators for `Nat` operators that have simprocs associated with them, but do not
have support in satellite solvers. The goal is to workaround a nasty interaction between
E-matching and normalization. Consider the following example:
```
@[grind] def mask := 15

@[grind =] theorem foo (x : Nat) : x &&& 15 = x % 16 := by sorry

example (x : Nat) : 3 &&& mask = 3 := by
  grind only [foo, mask]
```
This is a very simple version of issue #11498.
The e-graph contains `3 &&& mask`. E-matching finds that `3 &&& mask` matches pattern `x &&& 15`
modulo the equality `mask = 15`, binding `x := 3`.
Thus is produces the theorem instance `3 &&& 15 = 3 % 16`, which simplifies to `True` using the
builtin simprocs for `&&&` and `%`. So, nothing is learned.
**Tension**: The invariant "all terms in e-graph are normalized" conflicts with congruence needing
the intermediate term `3 &&& 15` to make the connection.
This is yet another example that shows how tricky is to combine e-matching with a normalizer.
It is yet another reason for not letting users to extend the normalizer.
If we do, we should be able to mark which ones should be used not normalize theorem instances.
The following propagator ensure that `3 &&& mask` is merged with the equivalence class `3` if
`mask = 15`.
-/

def propagateNatBinOp (declName : Name) (congrThmName : Name) (op : Nat → Nat → Nat) (e : Expr) : GoalM Unit := do
  let arity := 6
  unless e.isAppOfArity declName arity do return ()
  unless e.getArg! 0 |>.isConstOf ``Nat do return ()
  unless e.getArg! 1 |>.isConstOf ``Nat do return ()
  let a := e.getArg! (arity - 2) arity
  let aRoot ← getRoot a
  let some k₁ ← getNatValue? aRoot | return ()
  let b := e.getArg! (arity - 1) arity
  let bRoot ← getRoot b
  let some k₂ ← getNatValue? bRoot | return ()
  let k := op k₁ k₂
  let r ← shareCommon (mkNatLit k)
  internalize r 0
  let h := mkApp8 (mkConst congrThmName) a b aRoot bRoot r (← mkEqProof a aRoot) (← mkEqProof b bRoot) eagerReflBoolTrue
  pushEq e r h

builtin_grind_propagator propagateNatAnd ↑HAnd.hAnd := propagateNatBinOp ``HAnd.hAnd ``Grind.Nat.and_congr (· &&& ·)
builtin_grind_propagator propagateNatOr ↑HOr.hOr := propagateNatBinOp ``HOr.hOr ``Grind.Nat.or_congr (· ||| ·)
builtin_grind_propagator propagateNatXOr ↑HXor.hXor := propagateNatBinOp ``HXor.hXor ``Grind.Nat.xor_congr (· ^^^ ·)
builtin_grind_propagator propagateNatShiftLeft ↑HShiftLeft.hShiftLeft :=
  propagateNatBinOp ``HShiftLeft.hShiftLeft ``Grind.Nat.shiftLeft_congr (· <<< ·)
builtin_grind_propagator propagateNatShiftRight ↑HShiftRight.hShiftRight :=
  propagateNatBinOp ``HShiftRight.hShiftRight ``Grind.Nat.shiftRight_congr (· >>> ·)

end Lean.Meta.Grind
