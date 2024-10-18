/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Omega.Coeffs
import Init.Data.ToString.Macro

/-!
# Linear combinations

We use this data structure while processing hypotheses.

-/

namespace Lean.Omega

/-- Internal representation of a linear combination of atoms, and a constant term. -/
structure LinearCombo where
  /-- Constant term. -/
  const : Int := 0
  /-- Coefficients of the atoms. -/
  coeffs : Coeffs := []
deriving DecidableEq, Repr

namespace LinearCombo

instance : ToString LinearCombo where
  toString lc :=
    s!"{lc.const}{String.join <| lc.coeffs.toList.enum.map fun ⟨i, c⟩ => s!" + {c} * x{i+1}"}"

instance : Inhabited LinearCombo := ⟨{const := 1}⟩

theorem ext {a b : LinearCombo} (w₁ : a.const = b.const) (w₂ : a.coeffs = b.coeffs) :
    a = b := by
  cases a; cases b
  subst w₁; subst w₂
  congr

/-- Check if a linear combination is an atom, i.e. the constant term is zero and there is exactly one nonzero coefficient, which is one. -/
def isAtom (a : LinearCombo) : Bool :=
  a.const == 0 && (a.coeffs.filter (· == 1)).length == 1 && a.coeffs.all fun c => c == 0 || c == 1

/--
Evaluate a linear combination `⟨r, [c_1, …, c_k]⟩` at values `[v_1, …, v_k]` to obtain
`r + (c_1 * x_1 + (c_2 * x_2 + ... (c_k * x_k + 0))))`.
-/
def eval (lc : LinearCombo) (values : Coeffs) : Int :=
  lc.const + lc.coeffs.dot values

@[simp] theorem eval_nil : (lc : LinearCombo).eval .nil = lc.const := by
  simp [eval]

/-- The `i`-th coordinate function. -/
def coordinate (i : Nat) : LinearCombo where
  const := 0
  coeffs := Coeffs.set .nil i 1

@[simp] theorem coordinate_eval (i : Nat) (v : Coeffs) :
    (coordinate i).eval v = v.get i := by
  simp [eval, coordinate]

theorem coordinate_eval_0 : (coordinate 0).eval (.ofList (a0 :: t)) = a0 := by simp
theorem coordinate_eval_1 : (coordinate 1).eval (.ofList (a0 :: a1 :: t)) = a1 := by simp
theorem coordinate_eval_2 : (coordinate 2).eval (.ofList (a0 :: a1 :: a2 :: t)) = a2 := by simp
theorem coordinate_eval_3 :
    (coordinate 3).eval (.ofList (a0 :: a1 :: a2 :: a3 :: t)) = a3 := by simp
theorem coordinate_eval_4 :
    (coordinate 4).eval (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: t)) = a4 := by simp
theorem coordinate_eval_5 :
    (coordinate 5).eval (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: t)) = a5 := by simp
theorem coordinate_eval_6 :
    (coordinate 6).eval (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: t)) = a6 := by simp
theorem coordinate_eval_7 :
    (coordinate 7).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: t)) = a7 := by simp
theorem coordinate_eval_8 :
    (coordinate 8).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: t)) = a8 := by simp
theorem coordinate_eval_9 :
    (coordinate 9).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: t)) = a9 := by simp

/-- Implementation of addition on `LinearCombo`. -/
def add (l₁ l₂ : LinearCombo) : LinearCombo where
  const := l₁.const + l₂.const
  coeffs := l₁.coeffs + l₂.coeffs

instance : Add LinearCombo := ⟨add⟩

@[simp] theorem add_const {l₁ l₂ : LinearCombo} : (l₁ + l₂).const = l₁.const + l₂.const := rfl
@[simp] theorem add_coeffs {l₁ l₂ : LinearCombo} : (l₁ + l₂).coeffs = l₁.coeffs + l₂.coeffs := rfl

/-- Implementation of subtraction on `LinearCombo`. -/
def sub (l₁ l₂ : LinearCombo) : LinearCombo where
  const := l₁.const - l₂.const
  coeffs := l₁.coeffs - l₂.coeffs

instance : Sub LinearCombo := ⟨sub⟩

@[simp] theorem sub_const {l₁ l₂ : LinearCombo} : (l₁ - l₂).const = l₁.const - l₂.const := rfl
@[simp] theorem sub_coeffs {l₁ l₂ : LinearCombo} : (l₁ - l₂).coeffs = l₁.coeffs - l₂.coeffs := rfl

/-- Implementation of negation on `LinearCombo`. -/
def neg (lc : LinearCombo) : LinearCombo where
  const := -lc.const
  coeffs := -lc.coeffs

instance : Neg LinearCombo := ⟨neg⟩

@[simp] theorem neg_const {l : LinearCombo} : (-l).const = -l.const := rfl
@[simp] theorem neg_coeffs {l : LinearCombo} : (-l).coeffs = -l.coeffs  := rfl

theorem sub_eq_add_neg (l₁ l₂ : LinearCombo) : l₁ - l₂ = l₁ + -l₂ := by
  rcases l₁ with ⟨a₁, c₁⟩; rcases l₂ with ⟨a₂, c₂⟩
  apply ext
  · simp [Int.sub_eq_add_neg]
  · simp [Coeffs.sub_eq_add_neg]

/-- Implementation of scalar multiplication of a `LinearCombo` by an `Int`. -/
def smul (lc : LinearCombo) (i : Int) : LinearCombo where
  const := i * lc.const
  coeffs := lc.coeffs.smul i

instance : HMul Int LinearCombo LinearCombo := ⟨fun i lc => lc.smul i⟩

@[simp] theorem smul_const {lc : LinearCombo} {i : Int} : (i * lc).const = i * lc.const := rfl
@[simp] theorem smul_coeffs {lc : LinearCombo} {i : Int} : (i * lc).coeffs = i * lc.coeffs := rfl

@[simp] theorem add_eval (l₁ l₂ : LinearCombo) (v : Coeffs) :
    (l₁ + l₂).eval v = l₁.eval v + l₂.eval v := by
  rcases l₁ with ⟨r₁, c₁⟩; rcases l₂ with ⟨r₂, c₂⟩
  simp only [eval, add_const, add_coeffs, Int.add_assoc, Int.add_left_comm]
  congr
  exact Coeffs.dot_distrib_left c₁ c₂ v

@[simp] theorem neg_eval (lc : LinearCombo) (v : Coeffs) : (-lc).eval v = - lc.eval v := by
  rcases lc with ⟨a, coeffs⟩
  simp [eval, Int.neg_add]

@[simp] theorem sub_eval (l₁ l₂ : LinearCombo) (v : Coeffs) :
    (l₁ - l₂).eval v = l₁.eval v - l₂.eval v := by
  simp [sub_eq_add_neg, Int.sub_eq_add_neg]

@[simp] theorem smul_eval (lc : LinearCombo) (i : Int) (v : Coeffs) :
    (i * lc).eval v = i * lc.eval v := by
  rcases lc with ⟨a, coeffs⟩
  simp [eval, Int.mul_add]

theorem smul_eval_comm (lc : LinearCombo) (i : Int) (v : Coeffs) :
    (i * lc).eval v = lc.eval v * i := by
  simp [Int.mul_comm]

/--
Multiplication of two linear combinations.
This is useful only if at least one of the linear combinations is constant,
and otherwise should be considered as a junk value.
-/
def mul (l₁ l₂ : LinearCombo) : LinearCombo :=
  l₂.const * l₁ + l₁.const * l₂ - { const := l₁.const * l₂.const }

theorem mul_eval_of_const_left (l₁ l₂ : LinearCombo) (v : Coeffs) (w : l₁.coeffs.isZero) :
    (mul l₁ l₂).eval v = l₁.eval v * l₂.eval v := by
  have : Coeffs.dot l₁.coeffs v = 0 := IntList.dot_of_left_zero w
  simp [mul, eval, this, Coeffs.sub_eq_add_neg, Coeffs.dot_distrib_left, Int.add_mul, Int.mul_add,
    Int.mul_comm]

theorem mul_eval_of_const_right (l₁ l₂ : LinearCombo) (v : Coeffs) (w : l₂.coeffs.isZero) :
    (mul l₁ l₂).eval v = l₁.eval v * l₂.eval v := by
  have : Coeffs.dot l₂.coeffs v = 0 := IntList.dot_of_left_zero w
  simp [mul, eval, this, Coeffs.sub_eq_add_neg, Coeffs.dot_distrib_left, Int.add_mul, Int.mul_add,
    Int.mul_comm]

theorem mul_eval (l₁ l₂ : LinearCombo) (v : Coeffs) (w : l₁.coeffs.isZero ∨ l₂.coeffs.isZero) :
    (mul l₁ l₂).eval v = l₁.eval v * l₂.eval v := by
  rcases w with w | w
  · rw [mul_eval_of_const_left _ _ _ w]
  · rw [mul_eval_of_const_right _ _ _ w]

end LinearCombo

end Lean.Omega
