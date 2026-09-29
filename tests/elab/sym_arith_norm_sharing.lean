/-!
The `arith` normalizer must keep terms maximally shared when it builds congruence steps for a
binary application whose first argument is unchanged and whose second argument is rewritten.
With `sym.debug` enabled, a violation surfaces as a panic in `assertShared`.
-/

set_option sym.debug true
set_option warn.sorry false

register_sym_simp arithSimp where
  pre := arith

variable (f : Nat → Nat) (a b c : Nat) (i j : Int) (g : Int → Int)

-- Relations over a semiring: the common constant is cancelled on both sides.
/--
trace: case grind
f : Nat → Nat
a b c : Nat
i j : Int
g : Int → Int
⊢ 0 ≤ 0
-/
#guard_msgs in
example : 0 + 1 ≤ (1 : Nat) := by
  sym =>
    simp arithSimp
    show_goals
    sorry

/--
trace: case grind
f : Nat → Nat
a b c : Nat
i j : Int
g : Int → Int
⊢ a ≤ 0
-/
#guard_msgs in
example : a + 2 ≤ 2 := by
  sym =>
    simp arithSimp
    show_goals
    sorry

/--
trace: case grind
f : Nat → Nat
a b c : Nat
i j : Int
g : Int → Int
⊢ a = 0
-/
#guard_msgs in
example : a + 2 = 2 := by
  sym =>
    simp arithSimp
    show_goals
    sorry

-- Atoms: only the second operand is simplified.
/--
trace: case grind
f : Nat → Nat
a b c : Nat
i j : Int
g : Int → Int
⊢ a + f b = c
-/
#guard_msgs in
example : a + f (b + 0) = c := by
  sym =>
    simp arithSimp
    show_goals
    sorry

/--
trace: case grind
f : Nat → Nat
a b c : Nat
i j : Int
g : Int → Int
⊢ a * f b = c
-/
#guard_msgs in
example : a * f (b + 0) = c := by
  sym =>
    simp arithSimp
    show_goals
    sorry

/--
trace: case grind
f : Nat → Nat
a b c : Nat
i j : Int
g : Int → Int
⊢ i = g j
-/
#guard_msgs in
example : i - g (j + 0) = 0 := by
  sym =>
    simp arithSimp
    show_goals
    sorry

/--
trace: case grind
f : Nat → Nat
a b c : Nat
i j : Int
g : Int → Int
⊢ a ≤ f b
-/
#guard_msgs in
example : a ≤ f (b + 0) := by
  sym =>
    simp arithSimp
    show_goals
    sorry
