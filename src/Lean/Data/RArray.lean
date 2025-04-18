/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Init.Data.RArray
import Lean.Meta.InferType
import Lean.Meta.DecLevel
import Lean.ToExpr

/-!
Auxiliary definitions related to `Lean.RArray` that are typically only used in meta-code, in
particular the `ToExpr` instance.
-/

namespace Lean

-- This function could live in Init/Data/RArray.lean, but without omega it's tedious to implement
def RArray.ofFn {n : Nat} (f : Fin n → α) (h : 0 < n) : RArray α :=
  go 0 n h (Nat.le_refl _)
where
  go (lb ub : Nat) (h1 : lb < ub) (h2 : ub ≤ n) : RArray α :=
    if h : lb + 1 = ub then
      .leaf (f ⟨lb, Nat.lt_of_lt_of_le h1 h2⟩)
    else
      let mid := (lb + ub)/2
      .branch mid (go lb mid (by omega) (by omega)) (go mid ub (by omega) h2)

def RArray.ofArray (xs : Array α) (h : 0 < xs.size) : RArray α :=
  .ofFn (xs[·]) h

/-- The correctness theorem for `ofFn` -/
theorem RArray.get_ofFn {n : Nat} (f : Fin n → α) (h : 0 < n) (i : Fin n) :
    (ofFn f h).get i = f i :=
  go 0 n h (Nat.le_refl _) (Nat.zero_le _) i.2
where
  go lb ub h1 h2 (h3 : lb ≤ i.val) (h3 : i.val < ub) : (ofFn.go f lb ub h1 h2).get i = f i := by
    induction lb, ub, h1, h2 using RArray.ofFn.go.induct (n := n)
    case case1 =>
      simp [ofFn.go, RArray.get_eq_getImpl, RArray.getImpl]
      congr
      omega
    case case2 ih1 ih2 hiu =>
      rw [ofFn.go]; simp only [↓reduceDIte, *]
      simp [RArray.get_eq_getImpl, RArray.getImpl] at *
      split
      · rw [ih1] <;> omega
      · rw [ih2] <;> omega

@[simp]
theorem RArray.size_ofFn {n : Nat} (f : Fin n → α) (h : 0 < n) :
    (ofFn f h).size = n :=
  go 0 n h (Nat.le_refl _)
where
  go lb ub h1 h2 : (ofFn.go f lb ub h1 h2).size = ub - lb := by
    induction lb, ub, h1, h2 using RArray.ofFn.go.induct (n := n)
    case case1 => simp [ofFn.go, size]
    case case2 ih1 ih2 hiu => rw [ofFn.go]; simp +zetaDelta [size, *]; omega

open Meta
def RArray.toExpr (ty : Expr) (f : α → Expr) (a : RArray α) : MetaM Expr := do
  let k (leaf branch : Expr) : MetaM Expr :=
    let rec go (a : RArray α) : MetaM Expr := do
      match a with
      | .leaf x  =>
        return mkApp2 leaf ty (f x)
      | .branch p l r =>
        return mkApp4 branch ty (mkRawNatLit p) (← go l) (← go r)
    go a
  let info ← getConstInfo ``RArray
  -- TODO: remove after bootstrapping hell
  if info.levelParams.isEmpty then
    k (mkConst ``RArray.leaf) (mkConst ``RArray.branch)
  else
    let u ← getDecLevel ty
    k (mkConst ``RArray.leaf [u]) (mkConst ``RArray.branch [u])

end Lean
