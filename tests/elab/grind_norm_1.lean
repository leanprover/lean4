/-!
Discrepancies between the legacy `simp`-based `grind` normalizer and the `Sym.simp`-based one,
collected with `grind_norm check`. `grind_norm` is a debugging tactic for this migration and
will be deleted with this test once `grind` runs on `Sym.simp`. A recorded message is a gap to
fix unless a comment marks it as an accepted difference. Each `#guard_msgs` documents the current status of one
input; an empty message means both normalizers agree.
-/

set_option warn.sorry false

section propositional
variable (p q r : Prop) (a b : Nat)

#guard_msgs in
example : ¬¬p := by grind_norm check; sorry

#guard_msgs in
example : ¬(p ∧ q) := by grind_norm check; sorry

#guard_msgs in
example : ¬(p ∨ q) := by grind_norm check; sorry

#guard_msgs in
example : (p ∨ q) ∨ r := by grind_norm check; sorry

#guard_msgs in
example : p ∨ False := by grind_norm check; sorry

#guard_msgs in
example : (p ↔ q) := by grind_norm check; sorry

#guard_msgs in
example : (p = True) := by grind_norm check; sorry

#guard_msgs in
example : (p = False) := by grind_norm check; sorry

#guard_msgs in
example : ¬(p → q) := by grind_norm check; sorry

#guard_msgs in
example : ¬(∀ x : Nat, x = a) := by grind_norm check; sorry

#guard_msgs in
example : ¬(∃ x : Nat, x = a) := by grind_norm check; sorry

#guard_msgs in
example : (∃ x : Nat, x = a ∧ p) := by grind_norm check; sorry

#guard_msgs in
example : (∃ _ : Nat, p) := by grind_norm check; sorry

#guard_msgs in
example [Decidable p] : (if p then True else False) := by grind_norm check; sorry

#guard_msgs in
example [Decidable p] : (if p then a else b) = a := by grind_norm check; sorry

#guard_msgs in
example (h : Decidable p) : (dite p (fun _ => a) (fun _ => b)) = a := by grind_norm check; sorry

end propositional

section bool
variable (x y : Bool) (a b : Nat)

#guard_msgs in
example : (x && y) = true := by grind_norm check; sorry

#guard_msgs in
example : (x || y) = false := by grind_norm check; sorry

#guard_msgs in
example : (a == b) = true := by grind_norm check; sorry

#guard_msgs in
example : (a != b) = true := by grind_norm check; sorry

#guard_msgs in
example : x = true := by grind_norm check; sorry

#guard_msgs in
example : true = x := by grind_norm check; sorry

#guard_msgs in
example : (x && y) = (y || x) := by grind_norm check; sorry

#guard_msgs in
example : ¬(x = true) := by grind_norm check; sorry

#guard_msgs in
example : cond x a b = a := by grind_norm check; sorry

#guard_msgs in
example : decide (a = b) = true := by grind_norm check; sorry

end bool

section arith
variable (a b c : Nat) (i j : Int)

#guard_msgs in
example : a < b := by grind_norm check; sorry

#guard_msgs in
example : a ≥ b := by grind_norm check; sorry

#guard_msgs in
example : a > b := by grind_norm check; sorry

#guard_msgs in
example : ¬(a ≤ b) := by grind_norm check; sorry

#guard_msgs in
example : ¬(i ≤ j) := by grind_norm check; sorry

#guard_msgs in
example : a.succ = b := by grind_norm check; sorry

#guard_msgs in
example : a + 0 = 0 + a := by grind_norm check; sorry

#guard_msgs in
example : a + b + a = c := by grind_norm check; sorry

#guard_msgs in
example : 2 * a + 3 = b := by grind_norm check; sorry

#guard_msgs in
example : a ^ 1 = a ^ 0 := by grind_norm check; sorry

#guard_msgs in
example : a - a = 0 - a := by grind_norm check; sorry

#guard_msgs in
example : a / 1 = a % 1 := by grind_norm check; sorry

#guard_msgs in
example : i - j = -i := by grind_norm check; sorry

#guard_msgs in
example : ((a : Int) + (b : Int)) = ((a + b : Nat) : Int) := by grind_norm check; sorry

#guard_msgs in
example : ((a * b : Nat) : Int) = (a : Int) := by grind_norm check; sorry

#guard_msgs in
example : Int.subNatNat a b = i := by grind_norm check; sorry

#guard_msgs in
example : i.tdiv j = i.fdiv j := by grind_norm check; sorry

#guard_msgs in
example : i.sign = j := by grind_norm check; sorry

#guard_msgs in
example : (2 : Nat) + 3 = 5 := by grind_norm check; sorry

#guard_msgs in
example : (2 : Int) * 3 - 7 = j := by grind_norm check; sorry

#guard_msgs in
example : (10 : Nat) < 3 := by grind_norm check; sorry

#guard_msgs in
example : (2 : Nat) ∣ 4 := by grind_norm check; sorry

#guard_msgs in
example : i < j := by grind_norm check; sorry

#guard_msgs in
example : i + 1 < j := by grind_norm check; sorry

#guard_msgs in
example : 2 * i ≤ j + 3 := by grind_norm check; sorry

#guard_msgs in
example : i + j = j + i := by grind_norm check; sorry

#guard_msgs in
example : i * j + 1 = i * j := by grind_norm check; sorry

#guard_msgs in
example : -i ≤ j := by grind_norm check; sorry

-- Accepted difference: legacy normalizes only `Nat` and `Int` arithmetic.
/--
error: `grind_norm` discrepancy
legacy:
  x * 2⁻¹ = y
sym:
  x + -2 * y = 0
-/
#guard_msgs in
example (x y : Rat) : x / 2 = y := by grind_norm check; sorry

#guard_msgs in
example : ¬(i < j) := by grind_norm check; sorry

#guard_msgs in
example : i = j := by grind_norm check; sorry

#guard_msgs in
example : i + 3 = 0 := by grind_norm check; sorry

#guard_msgs in
example : 3 = i := by grind_norm check; sorry

#guard_msgs in
example : i = 3 := by grind_norm check; sorry

#guard_msgs in
example : i * j = i := by grind_norm check; sorry

end arith

section structural
variable (a b : Nat) (f : Nat → Nat)

#guard_msgs in
example : (fun x => f x) a = b := by grind_norm check; sorry

#guard_msgs in
example : (let x := a + 0; f x) = b := by grind_norm check; sorry

#guard_msgs in
example (x : Nat) (hx : x = a + 0) : f x = b := by grind_norm check; sorry

#guard_msgs in
example : (match a with | 0 => b | n + 1 => n) = a := by grind_norm check; sorry

#guard_msgs in
example : (match (0 : Nat) with | 0 => b | n + 1 => n) = a := by grind_norm check; sorry

#guard_msgs in
example : (a, b).1 = b := by grind_norm check; sorry

#guard_msgs in
example : Function.comp f f a = b := by grind_norm check; sorry

#guard_msgs in
example : [1, 2].length = a := by grind_norm check; sorry

#guard_msgs in
example : (#[1, 2] : Array Nat).size = a := by grind_norm check; sorry

#guard_msgs in
example : "ab" ++ "c" = "abc" := by grind_norm check; sorry

#guard_msgs in
example : (3 : Fin 5).val = a := by grind_norm check; sorry

#guard_msgs in
example : (a :: []).length = 1 := by grind_norm check; sorry

#guard_msgs in
example : ∀ x, f x = x → f (f x) = x := by grind_norm check; sorry

#guard_msgs in
example : ∀ x, (f x = x ∨ ∀ y, f y = x) := by grind_norm check; sorry

#guard_msgs in
example : (∀ x, f x = x ∧ f x = a) := by grind_norm check; sorry

#guard_msgs in
example : (True → a = b) := by grind_norm check; sorry

#guard_msgs in
example : (a = b → False) := by grind_norm check; sorry

#guard_msgs in
example : ((∀ x, f x = x) → a = b) := by grind_norm check; sorry

#guard_msgs in
example : (Nat.succ a = Nat.zero) := by grind_norm check; sorry

#guard_msgs in
example : (some a = none) := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : a + 1 ≥ 0 := by grind_norm check; sorry

#guard_msgs in
example (a : Int) : a + 1 ≥ 0 := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : a + 3 = 0 := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : 0 = a + 2 := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : a + 2 ≤ 0 := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : 3 ≤ a + 5 := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : a + 5 ≤ 3 := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : 0 ≤ a := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : a ≤ a + 1 := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : a + 1 ≤ a := by grind_norm check; sorry

#guard_msgs in
example (a : Nat) : 2 * a + 1 = 0 := by grind_norm check; sorry

#guard_msgs in
example (a b : Nat) : a * b + 1 = 0 := by grind_norm check; sorry

#guard_msgs in
example (a b : Nat) : a + 1 = b := by grind_norm check; sorry

#guard_msgs in
example (a : Int) : a + 1 + b + c + 5 ≥ 0 := by grind_norm check; sorry

#guard_msgs in
example (a : Int) : a + 1 + b + c + 5 = 0 := by grind_norm check; sorry

end structural

section int_tightening
variable (i : Int)

#guard_msgs in
example : 2 * i = 4 := by grind_norm check; sorry

#guard_msgs in
example : 2 * i + 1 ≤ 4 := by grind_norm check; sorry

#guard_msgs in
example : (2 : Int) ∣ 2 * i := by grind_norm check; sorry

#guard_msgs in
example : (3 : Int) ∣ i := by grind_norm check; sorry

#guard_msgs in
example (j : Int) : 4 * i + 2 = 6 * j := by grind_norm check; sorry

-- Accepted difference: legacy checks "already of the form `p = 0`" before its gcd step.
/--
error: `grind_norm` discrepancy
legacy:
  3 * i + 1 = 0
sym:
  False
-/
#guard_msgs in
example : 3 * i + 1 = 0 := by grind_norm check; sorry

-- Accepted difference: legacy checks "already of the form `p = 0`" before its gcd step.
/--
error: `grind_norm` discrepancy
legacy:
  2 * i + 3 ≤ 0
sym:
  i + 2 ≤ 0
-/
#guard_msgs in
example : 2 * i + 3 ≤ 0 := by grind_norm check; sorry

#guard_msgs in
example (j : Int) : 6 * i ≤ 4 * j + 3 := by grind_norm check; sorry

#guard_msgs in
example : 4 * i < 6 := by grind_norm check; sorry

#guard_msgs in
example : -2 * i = 4 := by grind_norm check; sorry

#guard_msgs in
example : ¬(2 * i ≤ 5) := by grind_norm check; sorry

#guard_msgs in
example : (6 : Int) ∣ 4 * i + 2 := by grind_norm check; sorry

#guard_msgs in
example : (4 : Int) ∣ 2 * i + 1 := by grind_norm check; sorry

#guard_msgs in
example : (2 : Int) ∣ 4 * i := by grind_norm check; sorry

#guard_msgs in
example : (0 : Int) ∣ i := by grind_norm check; sorry

#guard_msgs in
example : (-2 : Int) ∣ 4 * i + 2 := by grind_norm check; sorry

#guard_msgs in
example (j : Int) : (3 : Int) ∣ i + j - i := by grind_norm check; sorry

end int_tightening

section control_flow
variable (a b c : Nat)

/--
error: `grind_norm` discrepancy
legacy:
  a = c
sym:
  (if True then a else b) = c
-/
#guard_msgs in
example : (if 1 < 2 then a else b) = c := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  b = c
sym:
  (if False then a else b) = c
-/
#guard_msgs in
example : (if 2 < 1 then a else b) = c := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  a = c
sym:
  (if True then a else b) = c
-/
#guard_msgs in
example : (if h : 1 < 2 then a else b) = c := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  a = c
sym:
  (if True then a else b) = c
-/
#guard_msgs in
example : cond (1 < 2 : Bool) a b = c := by grind_norm check; sorry

end control_flow

section ground_char
variable (a : Nat)

/--
error: `grind_norm` discrepancy
legacy:
  97 = a
sym:
  'a'.toNat = a
-/
#guard_msgs in
example : 'a'.toNat = a := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  True
sym:
  Char.ofNat 97 = 'a'
-/
#guard_msgs in
example : Char.ofNat 97 = 'a' := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  True
sym:
  'a'.isAlpha = true
-/
#guard_msgs in
example : 'a'.isAlpha = true := by grind_norm check; sorry

#guard_msgs in
example : 'a' < 'b' := by grind_norm check; sorry

end ground_char
