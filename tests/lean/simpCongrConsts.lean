/-!
# Tests `congr_simp` constants
-/

set_option warn.sorry false

/-!
Basic usage: `congr_simp` provides arguments in the following order `lhs, rhs, eq`.
-/

def test1 (a b : Nat) : Nat := sorry

/--
info: test1.congr_simp (a a✝ : Nat) (e_a : a = a✝) (b b✝ : Nat) (e_b : b = b✝) : test1 a b = test1 a✝ b✝
-/
#guard_msgs in
#check test1.congr_simp

/-!
Proofs that depend on other values get rewritten.
-/

def test2 (x : Nat) (h : 2 < x) : Nat := sorry

/-- info: test2.congr_simp (x x✝ : Nat) (e_x : x = x✝) (h : 2 < x) : test2 x h = test2 x✝ ⋯ -/
#guard_msgs in
#check test2.congr_simp

/-!
Values that other values depend on, become fixed.
-/

def test3 (x : Nat) (y : Fin x) : Nat := sorry

/-- info: test3.congr_simp (x : Nat) (y y✝ : Fin x) (e_y : y = y✝) : test3 x y = test3 x y✝ -/
#guard_msgs in
#check test3.congr_simp

def test4 [DecidableEq α] (x : Nat) : Nat := sorry

/-!
`Decidable` instances get right-hand side variants but no equations (because they are implied).
Only the right-hand side is instance implicit.
-/

/--
info: test4.congr_simp.{u_1} {α α✝ : Sort u_1} (e_α : α = α✝) {inst✝ : DecidableEq α} [DecidableEq α✝] (x x✝ : Nat)
  (e_x : x = x✝) : test4 x = test4 x✝
-/
#guard_msgs in
#check test4.congr_simp

/-!
They don't if other values depend on them though.
-/

structure Dep (p : Prop) [Decidable p] : Type where

def test5 [Decidable p] (x : Dep p) : Nat := sorry

/--
info: test5.congr_simp {p : Prop} [Decidable p] (x x✝ : Dep p) (e_x : x = x✝) : test5 x = test5 x✝
-/
#guard_msgs in
#check test5.congr_simp

/-!
Variables also don't get equalities if the result depends on them.
-/

def test6 (x y : Nat) : Fin x := sorry

/-- info: test6.congr_simp (x y y✝ : Nat) (e_y : y = y✝) : test6 x y = test6 x y✝ -/
#guard_msgs in
#check test6.congr_simp

/-!
Proofs that depend on `Decidable` instances also get rewritten properly.
-/

def test7 {α : Type u} [DecidableEq α] {x : α} (h : (x == x) = true) : Nat := sorry

/--
info: test7.congr_simp.{u} {α : Type u} {inst✝ : DecidableEq α} [DecidableEq α] {x x✝ : α} (e_x : x = x✝)
  (h : (x == x) = true) : test7 h = test7 ⋯
-/
#guard_msgs in
#check test7.congr_simp
