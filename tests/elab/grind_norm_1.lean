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

-- Accepted difference: legacy has no ground evaluation for `Fin.val`.
/--
error: `grind_norm` discrepancy
legacy:
  ↑3 = a
sym:
  3 = a
-/
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

section char_solve
variable (x y : Fin 5) (u : UInt8)

-- Accepted difference: legacy normalizes only `Nat` and `Int` arithmetic. `Sym` solves the
-- equation when the coefficient is invertible modulo the characteristic.
/--
error: `grind_norm` discrepancy
legacy:
  3 * x + 1 = 0
sym:
  x = 3
-/
#guard_msgs in
example : 3 * x + 1 = 0 := by grind_norm check; sorry

-- Accepted difference: as above.
/--
error: `grind_norm` discrepancy
legacy:
  2 * x = 2 * y
sym:
  x = y
-/
#guard_msgs in
example : 2 * x = 2 * y := by grind_norm check; sorry

-- Accepted difference: as above.
/--
error: `grind_norm` discrepancy
legacy:
  3 * u = 1
sym:
  u = 171
-/
#guard_msgs in
example : 3 * u = 1 := by grind_norm check; sorry

end char_solve

section control_flow
variable (a b c : Nat) (x : Bool) (p q : Prop) (f g : Nat → Nat)

#guard_msgs in
example : (if 1 < 2 then a else b) = c := by grind_norm check; sorry

#guard_msgs in
example : (if 2 < 1 then a else b) = c := by grind_norm check; sorry

#guard_msgs in
example : (if h : 1 < 2 then a else b) = c := by grind_norm check; sorry

#guard_msgs in
example : (if h : 2 < 1 then a else b) = c := by grind_norm check; sorry

#guard_msgs in
example : cond (1 < 2 : Bool) a b = c := by grind_norm check; sorry

#guard_msgs in
example : cond (2 < 1 : Bool) a b = c := by grind_norm check; sorry

#guard_msgs in
example : cond true a b = c := by grind_norm check; sorry

#guard_msgs in
example : cond x a b = c := by grind_norm check; sorry

-- The branches are normalized when the condition is not decided.
#guard_msgs in
example : (if a < b then a + 0 else 0 + b) = c := by grind_norm check; sorry

#guard_msgs in
example : (if h : a < b then a + 0 else 0 + b) = c := by grind_norm check; sorry

#guard_msgs in
example : (if 1 < 2 then (if 2 < 1 then a else b + 0) else c) = c := by grind_norm check; sorry

#guard_msgs in
example : (if a < b then (if 2 < 1 then a else b) else c) = c := by grind_norm check; sorry

-- Dependent branches.
#guard_msgs in
example : (if h : 1 < 2 then (⟨1, h⟩ : Fin 2).val else b) = c := by grind_norm check; sorry

#guard_msgs in
example (v : Array Nat) : (if h : a < v.size then v[a] else b) = c := by grind_norm check; sorry

-- Over-applied.
#guard_msgs in
example : (if 1 < 2 then f else g) a = c := by grind_norm check; sorry

#guard_msgs in
example : (if a < b then f else g) (a + 0) = c := by grind_norm check; sorry

#guard_msgs in
example : (if 1 < 2 then p else q) := by grind_norm check; sorry

#guard_msgs in
example : ¬(if 2 < 1 then p else q) := by grind_norm check; sorry

-- `match`: the discriminants are normalized first, then the alternatives.
#guard_msgs in
example : (match a + 0, b with | 0, _ => 1 | _, 0 => 2 | _, _ => 3) = b := by grind_norm check; sorry

#guard_msgs in
example (o : Option Nat) : (match o with | some x => x + 0 | none => 0 + b) = a := by grind_norm check; sorry

#guard_msgs in
example : (match a * 0 with | 0 => b | _ + 1 => a) = b := by grind_norm check; sorry

#guard_msgs in
example (v : Array Nat) : (match h : v.size + 0 with | 0 => 0 | n + 1 => v[n]'(by grind)) = b := by grind_norm check; sorry

#guard_msgs in
example (o : Option Nat) : (match o with | some _ => f | none => g) (a + 0) = b := by grind_norm check; sorry

end control_flow

section ground_char
variable (a : Nat) (c : Char) (s : String) (u : UInt32)

#guard_msgs in
example : 'a'.toNat = a := by grind_norm check; sorry

#guard_msgs in
example : Char.ofNat 97 = 'a' := by grind_norm check; sorry

-- Accepted difference. Both sides denote the same character, but they are different terms:
-- `'a'` is `Char.ofNat` applied to the raw literal `97`, and `Char.ofNat 97` is `Char.ofNat`
-- applied to the `OfNat` numeral `97`. `Sym` rewrites the latter into the former, so that a
-- character has a single representation. Legacy keeps the term as written.
/--
error: `grind_norm` discrepancy
legacy:
  Char.ofNat 97 = c
sym:
  'a' = c
-/
#guard_msgs in
example : Char.ofNat 97 = c := by grind_norm check; sorry

#guard_msgs in
example : 'a'.isAlpha = true := by grind_norm check; sorry

#guard_msgs in
example : 'a' < 'b' := by grind_norm check; sorry

#guard_msgs in
example : 'a' ≥ 'b' := by grind_norm check; sorry

#guard_msgs in
example : 'a' ≠ 'b' := by grind_norm check; sorry

#guard_msgs in
example : ('a' == 'b') = true := by grind_norm check; sorry

#guard_msgs in
example : ('a' != 'b') = true := by grind_norm check; sorry

#guard_msgs in
example : 'a'.toUpper = c := by grind_norm check; sorry

#guard_msgs in
example : 'A'.toLower = c := by grind_norm check; sorry

#guard_msgs in
example : '1'.isDigit = true := by grind_norm check; sorry

#guard_msgs in
example : 'a'.isDigit = true := by grind_norm check; sorry

#guard_msgs in
example : ' '.isWhitespace = true := by grind_norm check; sorry

#guard_msgs in
example : 'a'.isUpper = true := by grind_norm check; sorry

#guard_msgs in
example : 'a'.isLower = true := by grind_norm check; sorry

#guard_msgs in
example : '_'.isAlphanum = true := by grind_norm check; sorry

#guard_msgs in
example : 'a'.val = u := by grind_norm check; sorry

#guard_msgs in
example : toString 'a' = s := by grind_norm check; sorry

#guard_msgs in
example : c.toNat = a := by grind_norm check; sorry

#guard_msgs in
example : (if 'a'.isAlpha then a else 0) = a := by grind_norm check; sorry

end ground_char

section ground_eval
variable (a : Nat) (s : String) (l : List Nat) (v : Array Nat)

#guard_msgs in
example : ([1, 2] ++ [3]) = l := by grind_norm check; sorry

#guard_msgs in
example : [1, 2, 3].reverse = l := by grind_norm check; sorry

#guard_msgs in
example : [1, 2, 3][1] = a := by grind_norm check; sorry

#guard_msgs in
example : (#[1, 2] ++ #[3]) = v := by grind_norm check; sorry

#guard_msgs in
example : (#[1, 2].push 3) = v := by grind_norm check; sorry

#guard_msgs in
example : #[1, 2, 3][1] = a := by grind_norm check; sorry

#guard_msgs in
example : #[1, 2].toList = l := by grind_norm check; sorry

#guard_msgs in
example : [1, 2].toArray = v := by grind_norm check; sorry

#guard_msgs in
example : List.replicate 2 a = l := by grind_norm check; sorry

#guard_msgs in
example : (3 : Fin 5) + 4 = 2 := by grind_norm check; sorry

-- Accepted difference: `Sym` solves the equation for `x`; legacy only evaluates the lhs.
/--
error: `grind_norm` discrepancy
legacy:
  2 = x
sym:
  x = 2
-/
#guard_msgs in
example (x : Fin 5) : (3 : Fin 5) + 4 = x := by grind_norm check; sorry

#guard_msgs in
example : (Fin.mk 3 (by decide) : Fin 5).val = a := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 5) : Fin.last 4 = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 5) : x = Fin.last 4 := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 6) : x = (3 : Fin 5).succ := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 6) : x = (3 : Fin 5).castSucc := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 5) : (1 : Fin 5).rev = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 4) : (3 : Fin 5).pred (by decide) = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 8) : x = (2 : Fin 5).castAdd 3 := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 8) : x = (2 : Fin 5).addNat 3 := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 8) : x = Fin.natAdd 3 (2 : Fin 5) := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 3) : (2 : Fin 5).castLT (by decide : (2 : Fin 5).val < 3) = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 7) : Fin.castLE (by decide : 5 ≤ 7) (2 : Fin 5) = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 3) : Fin.subNat 2 (4 : Fin 5) (by decide) = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 5) : (⟨2, by decide⟩ : Fin 5) = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 5) : Fin.ofNat 5 7 = x := by grind_norm check; sorry

#guard_msgs in
example (x : Fin 5) : (7 : Fin 5) = x := by grind_norm check; sorry

#guard_msgs in
example : "abc".length = a := by grind_norm check; sorry

#guard_msgs in
example : "abc" < "abd" := by grind_norm check; sorry

#guard_msgs in
example : "abc" ≠ "abd" := by grind_norm check; sorry

#guard_msgs in
example : ("abc" == "abd") = true := by grind_norm check; sorry

#guard_msgs in
example : "abc".push 'd' = s := by grind_norm check; sorry

#guard_msgs in
example : String.singleton 'a' = s := by grind_norm check; sorry

-- Accepted difference: `Sym` solves the equation for `x`; legacy only evaluates the lhs.
/--
error: `grind_norm` discrepancy
legacy:
  8 = x
sym:
  x = 8
-/
#guard_msgs in
example (x : BitVec 8) : 3#8 + 5#8 = x := by grind_norm check; sorry

#guard_msgs in
example (x : BitVec 8) : (3 : BitVec 8) &&& 5 = x := by grind_norm check; sorry

#guard_msgs in
example (x : BitVec 16) : (3#8).zeroExtend 16 = x := by grind_norm check; sorry

#guard_msgs in
example : (3#8).toNat = a := by grind_norm check; sorry

-- Accepted difference: as above.
/--
error: `grind_norm` discrepancy
legacy:
  0 = x
sym:
  x = 0
-/
#guard_msgs in
example (x : BitVec 8) : 255#8 + 1 = x := by grind_norm check; sorry

#guard_msgs in
example (x : BitVec 8) : 300#8 = x := by grind_norm check; sorry

-- Accepted difference: `Sym` solves the equation for `x`; legacy only evaluates the lhs.
/--
error: `grind_norm` discrepancy
legacy:
  44 = x
sym:
  x = 44
-/
#guard_msgs in
example (x : UInt8) : (200 : UInt8) + 100 = x := by grind_norm check; sorry

#guard_msgs in
example : (200 : UInt8).toNat = a := by grind_norm check; sorry

#guard_msgs in
example : (300 : UInt16).toNat = a := by grind_norm check; sorry

-- Accepted difference: legacy has no ground evaluation for `^` on `UInt64`.
/--
error: `grind_norm` discrepancy
legacy:
  (2 ^ 40).toNat = a
sym:
  1099511627776 = a
-/
#guard_msgs in
example : (2 ^ 40 : UInt64).toNat = a := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  -56 = x
sym:
  x = 200
-/
#guard_msgs in
example (x : Int8) : (100 : Int8) + 100 = x := by grind_norm check; sorry

#guard_msgs in
example (x : Option Nat) : (some 1).isSome = true := by grind_norm check; sorry

#guard_msgs in
example : Nat.succ 2 = a := by grind_norm check; sorry

#guard_msgs in
example : Nat.gcd 4 6 = a := by grind_norm check; sorry

#guard_msgs in
example : (7 : Int).toNat = a := by grind_norm check; sorry

#guard_msgs in
example : (-7 : Int).toNat = a := by grind_norm check; sorry

#guard_msgs in
example : Int.natAbs (-7) = a := by grind_norm check; sorry

#guard_msgs in
example : (2 : Nat) ^ 10 = a := by grind_norm check; sorry

#guard_msgs in
example : (7 : Nat) / 2 = a := by grind_norm check; sorry

#guard_msgs in
example : (7 : Int) % 2 = 1 := by grind_norm check; sorry

#guard_msgs in
example : (-7 : Int) / 2 = -4 := by grind_norm check; sorry

#guard_msgs in
example : Nat.min 2 3 = a := by grind_norm check; sorry

#guard_msgs in
example : min 2 3 = a := by grind_norm check; sorry

#guard_msgs in
example : max 2 3 = a := by grind_norm check; sorry

end ground_eval

section binders
variable (f : Nat → Nat) (q : Nat → Nat → Prop) (a b : Nat)

#guard_msgs in
example : ∀ x, ∃ y, q x y := by grind_norm check; sorry

#guard_msgs in
example : ∀ x, ∃ y, q x y ∧ f x = y + 0 := by grind_norm check; sorry

#guard_msgs in
example : ∃ x, ∀ y, q x y → f y = x := by grind_norm check; sorry

#guard_msgs in
example : ¬ ∀ x, ∃ y, q x y := by grind_norm check; sorry

#guard_msgs in
example : ¬ ∃ x, ∀ y, q x y := by grind_norm check; sorry

#guard_msgs in
example : (∃ x, q x a) → b = a := by grind_norm check; sorry

#guard_msgs in
example : (∀ x, q x a → ∃ y, q y x) := by grind_norm check; sorry

#guard_msgs in
example : (fun x => f (x + 0)) = f := by grind_norm check; sorry

#guard_msgs in
example : (fun x => x + 0) = f := by grind_norm check; sorry

#guard_msgs in
example : ∀ x, x > 0 → ∀ y, y < x → q x y := by grind_norm check; sorry

#guard_msgs in
example : (∀ x, x = a → q x b) := by grind_norm check; sorry

#guard_msgs in
example : (∃ x, x = a ∧ q x b) := by grind_norm check; sorry

#guard_msgs in
example : ∃ x : Nat, True := by grind_norm check; sorry

#guard_msgs in
example : ∀ x : Nat, True := by grind_norm check; sorry

#guard_msgs in
example : ∀ x : Nat, x = x := by grind_norm check; sorry

end binders

section lets
variable (f : Nat → Nat) (a b : Nat)

#guard_msgs in
example : (let x := a + 0; let y := x + x; f y) = b := by grind_norm check; sorry

#guard_msgs in
example : (have x := a + 0; f x) = b := by grind_norm check; sorry

#guard_msgs in
example : ∀ z, (let x := z + 0; f x) = b := by grind_norm check; sorry

#guard_msgs in
example : (let g := fun x => x + 0; g a) = b := by grind_norm check; sorry

#guard_msgs in
example : let x := a; f x = b := by grind_norm check; sorry

#guard_msgs in
example : let x := a; ∀ y, f x = y := by grind_norm check; sorry

end lets

section matching
variable (a b : Nat) (o : Option Nat) (l : List Nat)

#guard_msgs in
example : (match o with | some x => x + 0 | none => 0) = a := by grind_norm check; sorry

#guard_msgs in
example : (match some a with | some x => x | none => 0) = b := by grind_norm check; sorry

#guard_msgs in
example : (match a + 0, b with | 0, _ => 1 | _, 0 => 2 | _, _ => 3) = b := by grind_norm check; sorry

#guard_msgs in
example : (match l with | [] => 0 | x :: _ => x) = a := by grind_norm check; sorry

#guard_msgs in
example : (match [a] with | [] => 0 | x :: _ => x) = a := by grind_norm check; sorry

#guard_msgs in
example : (match (a, b) with | (x, y) => x + y) = a := by grind_norm check; sorry

#guard_msgs in
example : (if a = 0 then 1 else match a with | 0 => 2 | n + 1 => n) = b := by grind_norm check; sorry

#guard_msgs in
example (h : o.isSome) : o.get h = a := by grind_norm check; sorry

#guard_msgs in
example : (o.getD 0) = a := by grind_norm check; sorry

#guard_msgs in
example : (some a).getD 0 = b := by grind_norm check; sorry

#guard_msgs in
example : (a, b).fst = (a, b).snd := by grind_norm check; sorry

#guard_msgs in
example : a ≠ b := by grind_norm check; sorry

#guard_msgs in
example : (a = b) = (b = a) := by grind_norm check; sorry

#guard_msgs in
example : a = b ↔ b = a := by grind_norm check; sorry

#guard_msgs in
example : (a == b) = (b == a) := by grind_norm check; sorry

#guard_msgs in
example (x y : Bool) : (x ^^ y) = true := by grind_norm check; sorry

#guard_msgs in
example (x y : Bool) : (!x) = y := by grind_norm check; sorry

#guard_msgs in
example (x : Bool) : (x = true) = (x = false) := by grind_norm check; sorry

#guard_msgs in
example (x : Bool) : (if x then a else b) = a := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) [Decidable p] : decide p = true := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) [Decidable p] : decide p = false := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) [Decidable p] [Decidable q] : (decide p && decide q) = true := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) : (p → q) := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) : (p → q → p) := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) : (p ∧ True) ∨ (q ∧ False) := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) : (p ↔ True) := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) : (p ∧ q) = (q ∧ p) := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) : ¬(p ↔ q) := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : p ∨ p := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : p ∧ p := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : p ∧ ¬p := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : p ∨ ¬p := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : p → p := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : (p = p) := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : (True = p) := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) : (False = p) := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) [Decidable p] : (if p then q else ¬q) := by grind_norm check; sorry

#guard_msgs in
example (p q : Prop) [Decidable p] : ¬(if p then q else ¬q) := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) [Decidable p] : (if p then a else a) = b := by grind_norm check; sorry

#guard_msgs in
example (p : Prop) [Decidable p] : (if ¬p then a else b) = b := by grind_norm check; sorry

end matching

section norm_attrs
namespace NormAttrs

opaque f : Nat → Nat
opaque g : Nat → Nat
opaque p : Nat → Prop
@[grind norm] axiom fax : f x = x + 2
@[grind norm ←] axiom gf : g (x + 1) = g x + 1
@[grind norm ↓] axiom pax : p (x + 1) = p x
@[grind norm] axiom cond_ax (x : Nat) : x > 0 → g (2 * x) = g x
@[grind unfold] def h (x : Nat) := 2 * x
def k : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * k n
attribute [grind unfold] k
variable (a b : Nat)

#guard_msgs in
example : f a = b := by grind_norm check; sorry

#guard_msgs in
example : f (f a) = b := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  g (a + 1) = b
sym:
  g a + 1 = b
-/
#guard_msgs in
example : g a + 1 = b := by grind_norm check; sorry

#guard_msgs in
example : p (a + 1) := by grind_norm check; sorry

/--
error: `grind_norm` discrepancy
legacy:
  p a
sym:
  p (a + 2)
-/
#guard_msgs in
example : p (a + 2) := by grind_norm check; sorry

#guard_msgs in
example : g (2 * 3) = b := by grind_norm check; sorry

#guard_msgs in
example : g (2 * (a + 1)) = b := by grind_norm check; sorry

#guard_msgs in
example : h a = b := by grind_norm check; sorry

#guard_msgs in
example : h (h a) = b := by grind_norm check; sorry

#guard_msgs in
example : k 0 = b := by grind_norm check; sorry

#guard_msgs in
example : k (a + 1) = b := by grind_norm check; sorry

#guard_msgs in
example : k 2 = b := by grind_norm check; sorry

end NormAttrs
end norm_attrs
