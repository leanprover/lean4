/-!
Discrepancies between the legacy `simp`-based `grind` normalizer and the `Sym.simp`-based one,
collected with `grind_norm check`. `grind_norm` is a debugging tactic for this migration and
will be deleted with this test once `grind` runs on `Sym.simp`. Each `#guard_msgs` documents the current status of one
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

/--
error: `grind_norm` discrepancy
legacy:
  True
sym:
  ↑a + ↑b + -1 * ↑a + -1 * ↑b = 0
-/
#guard_msgs in
example : ((a : Int) + (b : Int)) = ((a + b : Nat) : Int) := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  ↑a * ↑b = ↑a
sym:
  ↑a * ↑b = ↑a
-/
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

/--
error: `grind_norm` discrepancy
legacy:
  False
sym:
  a + 1 = 0
-/
#guard_msgs in
example : (Nat.succ a = Nat.zero) := by grind_norm check; sorry

#guard_msgs in
example : (some a = none) := by grind_norm check; sorry

end structural
