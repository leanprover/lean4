/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/
module

prelude
public import Init.NotationExtra

public section

namespace Bool

/--
Boolean “exclusive or”. `xor x y` can be written `x ^^ y`.

`x ^^ y` is `true` when precisely one of `x` or `y` is `true`. Unlike `and` and `or`, it does not
have short-circuiting behavior, because one argument's value never determines the final value. Also
unlike `and` and `or`, there is no commonly-used corresponding propositional connective.

Examples:
 * `false ^^ false = false`
 * `true ^^ false = true`
 * `false ^^ true = true`
 * `true ^^ true = false`
-/
abbrev xor : Bool → Bool → Bool := bne

@[inherit_doc] infixl:33 " ^^ " => xor

recommended_spelling "xor" for "^^" in [xor, «term_^^_»]

instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∀ x, p x) :=
  match inst true, inst false with
  | isFalse ht, _ => isFalse fun h => absurd (h _) ht
  | _, isFalse hf => isFalse fun h => absurd (h _) hf
  | isTrue ht, isTrue hf => isTrue fun | true => ht | false => hf

instance (p : Bool → Prop) [inst : DecidablePred p] : Decidable (∃ x, p x) :=
  match inst true, inst false with
  | isTrue ht, _ => isTrue ⟨_, ht⟩
  | _, isTrue hf => isTrue ⟨_, hf⟩
  | isFalse ht, isFalse hf => isFalse fun | ⟨true, h⟩ => absurd h ht | ⟨false, h⟩ => absurd h hf

@[simp] theorem default_bool : default = false := rfl

instance : LE Bool := ⟨(. → .)⟩
instance : LT Bool := ⟨(!. && .)⟩

instance (x y : Bool) : Decidable (x ≤ y) := inferInstanceAs (Decidable (x → y))
instance (x y : Bool) : Decidable (x < y) := inferInstanceAs (Decidable (!x && y))

instance : Max Bool := ⟨or⟩
instance : Min Bool := ⟨and⟩

theorem false_ne_true : false ≠ true := Bool.noConfusion

theorem eq_false_or_eq_true : (b : Bool) → b = true ∨ b = false := by decide

theorem eq_false_iff : {b : Bool} → b = false ↔ b ≠ true := by decide

theorem ne_false_iff : {b : Bool} → b ≠ false ↔ b = true := by decide

theorem eq_iff_iff {a b : Bool} : a = b ↔ (a ↔ b) := by cases b <;> simp

@[simp] theorem decide_eq_true  {b : Bool} {_ : Decidable (b = true)}  : decide (b = true)  =  b := by cases b <;> simp
@[simp] theorem decide_eq_false {b : Bool} {_ : Decidable (b = false)} : decide (b = false) = !b := by cases b <;> simp
theorem decide_true_eq  {b : Bool} [Decidable (true = b)]  : decide (true  = b) =  b := by cases b <;> simp
theorem decide_false_eq {b : Bool} [Decidable (false = b)] : decide (false = b) = !b := by cases b <;> simp

-- These lemmas assist with confluence.
@[simp] theorem eq_false_imp_eq_true_iff :
    ∀ (a b : Bool), ((a = false → b = true) ↔ (b = false → a = true)) = True := by decide
@[simp] theorem eq_true_imp_eq_false_iff :
    ∀ (a b : Bool), ((a = true → b = false) ↔ (b = true → a = false)) = True := by decide

/-! ### and -/

@[simp] theorem and_self_left  : ∀ (a b : Bool), (a && (a && b)) = (a && b) := by decide
@[simp] theorem and_self_right : ∀ (a b : Bool), ((a && b) && b) = (a && b) := by decide

@[simp] theorem not_and_self : ∀ (x : Bool), (!x && x) = false := by decide
@[simp] theorem and_not_self : ∀ (x : Bool), (x && !x) = false := by decide

/-
Added for confluence with `not_and_self` `and_not_self` on term
`(b && !b) = true` due to reductions:

1. `(b = true ∨ !b = true)` via `Bool.and_eq_true`
2. `false = true` via `Bool.and_not_self`
-/
@[simp] theorem eq_true_and_eq_false_self : ∀ (b : Bool), (b = true ∧ b = false) ↔ False := by decide
@[simp] theorem eq_false_and_eq_true_self : ∀ (b : Bool), (b = false ∧ b = true) ↔ False := by decide

theorem and_comm : ∀ (x y : Bool), (x && y) = (y && x) := by decide
instance : Std.Commutative (· && ·) := ⟨and_comm⟩

theorem and_left_comm : ∀ (x y z : Bool), (x && (y && z)) = (y && (x && z)) := by decide
theorem and_right_comm : ∀ (x y z : Bool), ((x && y) && z) = ((x && z) && y) := by decide

/-
Bool version `and_iff_left_iff_imp`.

Needed for confluence of term `(a && b) ↔ a` which reduces to `(a && b) = a` via
`Bool.coe_iff_coe` and `a → b` via `Bool.and_eq_true` and
`and_iff_left_iff_imp`.
-/
@[simp] theorem and_eq_left_iff_imp  : ∀ {a b : Bool}, ((a && b) = a) ↔ (a → b) := by decide
@[simp] theorem and_eq_right_iff_imp : ∀ {a b : Bool}, ((a && b) = b) ↔ (b → a) := by decide
@[simp] theorem eq_self_and : ∀ {a b : Bool}, (a = (a && b)) ↔ (a → b) := by decide
@[simp] theorem eq_and_self : ∀ {a b : Bool}, (b = (a && b)) ↔ (b → a) := by decide

@[simp] theorem not_and_eq_left_iff_and  : ∀ {a b : Bool}, ((!a && b) = a) ↔ !a ∧ !b := by decide
@[simp] theorem and_not_eq_right_iff_and : ∀ {a b : Bool}, ((a && !b) = b) ↔ !a ∧ !b := by decide
@[simp] theorem eq_not_self_and : ∀ {a b : Bool}, (a = (!a && b)) ↔ !a ∧ !b := by decide
@[simp] theorem eq_and_not_self : ∀ {a b : Bool}, (b = (a && !b)) ↔ !a ∧ !b := by decide

/-! ### or -/

@[simp] theorem or_self_left  : ∀ (a b : Bool), (a || (a || b)) = (a || b) := by decide
@[simp] theorem or_self_right : ∀ (a b : Bool), ((a || b) || b) = (a || b) := by decide

@[simp] theorem not_or_self : ∀ (x : Bool), (!x || x) = true := by decide
@[simp] theorem or_not_self : ∀ (x : Bool), (x || !x) = true := by decide

/-
Added for confluence with `not_or_self` `or_not_self` on term
`(b || !b) = true` due to reductions:
1. `(b = true ∨ !b = true)` via `Bool.or_eq_true`
2. `true = true` via `Bool.or_not_self`
-/
@[simp] theorem eq_true_or_eq_false_self : ∀(b : Bool), (b = true ∨ b = false) ↔ True := by decide
@[simp] theorem eq_false_or_eq_true_self : ∀(b : Bool), (b = false ∨ b = true) ↔ True := by decide

/-
Bool version `or_iff_left_iff_imp`.

Needed for confluence of term `(a || b) ↔ a` which reduces to `(a || b) = a` via
`Bool.coe_iff_coe` and `a → b` via `Bool.or_eq_true` and
`and_iff_left_iff_imp`.
-/
@[simp] theorem or_eq_left_iff_imp  : ∀ {a b : Bool}, ((a || b) = a) ↔ (b → a) := by decide
@[simp] theorem or_eq_right_iff_imp : ∀ {a b : Bool}, ((a || b) = b) ↔ (a → b) := by decide
@[simp] theorem eq_self_or : ∀ {a b : Bool}, (a = (a || b)) ↔ (b → a) := by decide
@[simp] theorem eq_or_self : ∀ {a b : Bool}, (b = (a || b)) ↔ (a → b) := by decide

@[simp] theorem not_or_eq_left_iff_and  : ∀ {a b : Bool}, ((!a || b) = a) ↔ a ∧ b := by decide
@[simp] theorem or_not_eq_right_iff_and : ∀ {a b : Bool}, ((a || !b) = b) ↔ a ∧ b := by decide
@[simp] theorem eq_not_self_or : ∀ {a b : Bool}, (a = (!a || b)) ↔ a ∧ b := by decide
@[simp] theorem eq_or_not_self : ∀ {a b : Bool}, (b = (a || !b)) ↔ a ∧ b := by decide

theorem or_comm : ∀ (x y : Bool), (x || y) = (y || x) := by decide
instance : Std.Commutative (· || ·) := ⟨or_comm⟩

theorem or_left_comm : ∀ (x y z : Bool), (x || (y || z)) = (y || (x || z)) := by decide
theorem or_right_comm : ∀ (x y z : Bool), ((x || y) || z) = ((x || z) || y) := by decide

/-! ### distributivity -/

theorem and_or_distrib_left  : ∀ (x y z : Bool), (x && (y || z)) = (x && y || x && z) := by decide
theorem and_or_distrib_right : ∀ (x y z : Bool), ((x || y) && z) = (x && z || y && z) := by decide

theorem or_and_distrib_left  : ∀ (x y z : Bool), (x || y && z) = ((x || y) && (x || z)) := by decide
theorem or_and_distrib_right : ∀ (x y z : Bool), (x && y || z) = ((x || z) && (y || z)) := by decide

theorem and_xor_distrib_left  : ∀ (x y z : Bool), (x && (y ^^ z)) = ((x && y) ^^ (x && z)) := by decide
theorem and_xor_distrib_right : ∀ (x y z : Bool), ((x ^^ y) && z) = ((x && z) ^^ (y && z)) := by decide

/-- De Morgan's law for boolean and -/
@[simp] theorem not_and : ∀ (x y : Bool), (!(x && y)) = (!x || !y) := by decide

/-- De Morgan's law for boolean or -/
@[simp] theorem not_or : ∀ (x y : Bool), (!(x || y)) = (!x && !y) := by decide

theorem and_eq_true_iff {x y : Bool} : (x && y) = true ↔ x = true ∧ y = true :=
  Iff.of_eq (and_eq_true x y)

theorem and_eq_false_iff : ∀ {x y : Bool}, (x && y) = false ↔ x = false ∨ y = false := by decide

/-
New simp rule that replaces `Bool.and_eq_false_eq_eq_false_or_eq_false` in
Mathlib due to confluence:

Consider the term: `¬((b && c) = true)`:

1. Reduces to `((b && c) = false)` via `Bool.not_eq_true`
2. Reduces to `¬(b = true ∧ c = true)` via `Bool.and_eq_true`.


1. Further reduces to `b = false ∨ c = false` via `Bool.and_eq_false_eq_eq_false_or_eq_false`.
2. Further reduces to `b = true → c = false` via `not_and` and `Bool.not_eq_true`.
-/
@[simp] theorem and_eq_false_imp : ∀ {x y : Bool}, (x && y) = false ↔ (x = true → y = false) := by decide

theorem or_eq_true_iff : ∀ {x y : Bool}, (x || y) = true ↔ x = true ∨ y = true := by simp

@[simp] theorem or_eq_false_iff : ∀ {x y : Bool}, (x || y) = false ↔ x = false ∧ y = false := by decide

/-! ### eq/beq/bne -/

/--
These two rules follow trivially by simp, but are needed to avoid non-termination
in false_eq and true_eq.
-/
@[simp] theorem false_eq_true : (false = true) = False := by simp
@[simp] theorem true_eq_false : (true = false) = False := by simp

-- The two lemmas below normalize terms with a constant to the
-- right-hand side but risk non-termination if `false_eq_true` and
-- `true_eq_false` are disabled.
@[simp low] theorem false_eq (b : Bool) : (false = b) = (b = false) := by
  cases b <;> simp

@[simp low] theorem true_eq (b : Bool) : (true = b) = (b = true) := by
  cases b <;> simp

@[simp] theorem true_beq  : ∀b, (true  == b) =  b := by decide
@[simp] theorem false_beq : ∀b, (false == b) = !b := by decide
instance : Std.LawfulIdentity (· == ·) true where
  left_id := true_beq
  right_id := beq_true

@[simp] theorem true_bne  : ∀(b : Bool), (true  != b) = !b := by decide
@[simp] theorem false_bne : ∀(b : Bool), (false != b) =  b := by decide
@[simp] theorem bne_true  : ∀(b : Bool), (b != true)  = !b := by decide
@[simp] theorem bne_false : ∀(b : Bool), (b != false) =  b := by decide
instance : Std.LawfulIdentity (· != ·) false where
  left_id := false_bne
  right_id := bne_false

@[simp] theorem not_beq_self : ∀ (x : Bool), ((!x) == x) = false := by decide
@[simp] theorem beq_not_self : ∀ (x : Bool), (x   == !x) = false := by decide

@[simp] theorem not_bne : ∀ (a b : Bool), ((!a) != b) = !(a != b) := by decide
@[simp] theorem bne_not : ∀ (a b : Bool), (a != !b) = !(a != b) := by decide

theorem not_bne_self : ∀ (x : Bool), ((!x) != x) = true := by decide
theorem bne_not_self : ∀ (x : Bool), (x   != !x) = true := by decide

/-
Added for equivalence with `Bool.not_beq_self` and needed for confluence
due to `beq_iff_eq`.
-/
theorem not_eq_self : ∀(b : Bool), ((!b) = b) ↔ False := by simp
@[simp] theorem eq_not_self : ∀(b : Bool), (b = (!b)) ↔ False := by decide

@[simp] theorem beq_self_left  : ∀(a b : Bool), (a == (a == b)) = b := by decide
@[simp] theorem beq_self_right : ∀(a b : Bool), ((a == b) == b) = a := by decide
@[simp] theorem bne_self_left  : ∀(a b : Bool), (a != (a != b)) = b := by decide
@[simp] theorem bne_self_right : ∀(a b : Bool), ((a != b) != b) = a := by decide

theorem not_bne_not : ∀ (x y : Bool), ((!x) != (!y)) = (x != y) := by simp

@[simp] theorem bne_assoc : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by decide
instance : Std.Associative (· != ·) := ⟨bne_assoc⟩

@[simp] theorem bne_right_inj  : ∀ {x y z : Bool}, (x != y) = (x != z) ↔ y = z := by decide
@[simp] theorem bne_left_inj : ∀ {x y z : Bool}, (x != z) = (y != z) ↔ x = y := by decide

theorem eq_not_of_ne : ∀ {x y : Bool}, x ≠ y → x = !y := by decide

/-! ### coercion related normal forms -/

theorem beq_eq_decide_eq [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  cases h : a == b
  · simp [ne_of_beq_false h]
  · simp [eq_of_beq h]

theorem eq_not : ∀ {a b : Bool}, (a = (!b)) ↔ (a ≠ b) := by decide
theorem not_eq : ∀ {a b : Bool}, ((!a) = b) ↔ (a ≠ b) := by decide

@[simp] theorem coe_iff_coe : ∀{a b : Bool}, (a ↔ b) ↔ a = b := by decide

@[simp] theorem coe_true_iff_false  : ∀{a b : Bool}, (a ↔ b = false) ↔ a = (!b) := by decide
@[simp] theorem coe_false_iff_true  : ∀{a b : Bool}, (a = false ↔ b) ↔ (!a) = b := by decide
@[simp] theorem coe_false_iff_false : ∀{a b : Bool}, (a = false ↔ b = false) ↔ (!a) = (!b) := by decide

/-! ### beq properties -/

theorem beq_comm {α} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = (b == a) :=
  Bool.coe_iff_coe.mp (by simp [@eq_comm α])

/-! ### xor -/

theorem false_xor : ∀ (x : Bool), (false ^^ x) = x := false_bne

theorem xor_false : ∀ (x : Bool), (x ^^ false) = x := bne_false

theorem true_xor : ∀ (x : Bool), (true ^^ x) = !x := true_bne

theorem xor_true : ∀ (x : Bool), (x ^^ true) = !x := bne_true

theorem not_xor_self : ∀ (x : Bool), (!x ^^ x) = true := not_bne_self

theorem xor_not_self : ∀ (x : Bool), (x ^^ !x) = true := bne_not_self

theorem not_xor : ∀ (x y : Bool), (!x ^^ y) = !(x ^^ y) := by decide

theorem xor_not : ∀ (x y : Bool), (x ^^ !y) = !(x ^^ y) := by decide

theorem not_xor_not : ∀ (x y : Bool), (!x ^^ !y) = (x ^^ y) := not_bne_not

theorem xor_self : ∀ (x : Bool), (x ^^ x) = false := by decide

theorem xor_comm : ∀ (x y : Bool), (x ^^ y) = (y ^^ x) := by decide

theorem xor_left_comm : ∀ (x y z : Bool), (x ^^ (y ^^ z)) = (y ^^ (x ^^ z)) := by decide

theorem xor_right_comm : ∀ (x y z : Bool), ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y) := by decide

theorem xor_assoc : ∀ (x y z : Bool), ((x ^^ y) ^^ z) = (x ^^ (y ^^ z)) := bne_assoc

theorem xor_right_inj : ∀ {x y z : Bool}, (x ^^ y) = (x ^^ z) ↔ y = z := bne_right_inj

theorem xor_left_inj : ∀ {x y z : Bool}, (x ^^ z) = (y ^^ z) ↔ x = y := bne_left_inj

/-! ### le/lt -/

@[simp] protected theorem le_true : ∀ (x : Bool), x ≤ true := by decide

@[simp] protected theorem false_le : ∀ (x : Bool), false ≤ x := by decide

@[simp] protected theorem le_refl : ∀ (x : Bool), x ≤ x := by decide

@[simp] protected theorem lt_irrefl : ∀ (x : Bool), ¬ x < x := by decide

protected theorem le_trans : ∀ {x y z : Bool}, x ≤ y → y ≤ z → x ≤ z := by decide

protected theorem le_antisymm : ∀ {x y : Bool}, x ≤ y → y ≤ x → x = y := by decide

protected theorem le_total : ∀ (x y : Bool), x ≤ y ∨ y ≤ x := by decide

protected theorem lt_asymm : ∀ {x y : Bool}, x < y → ¬ y < x := by decide

protected theorem lt_trans : ∀ {x y z : Bool}, x < y → y < z → x < z := by decide

protected theorem lt_iff_le_not_le : ∀ {x y : Bool}, x < y ↔ x ≤ y ∧ ¬ y ≤ x := by decide

protected theorem lt_of_le_of_lt : ∀ {x y z : Bool}, x ≤ y → y < z → x < z := by decide

protected theorem lt_of_lt_of_le : ∀ {x y z : Bool}, x < y → y ≤ z → x < z := by decide

protected theorem le_of_lt : ∀ {x y : Bool}, x < y → x ≤ y := by decide

protected theorem le_of_eq : ∀ {x y : Bool}, x = y → x ≤ y := by decide

protected theorem ne_of_lt : ∀ {x y : Bool}, x < y → x ≠ y := by decide

protected theorem lt_of_le_of_ne : ∀ {x y : Bool}, x ≤ y → x ≠ y → x < y := by decide

protected theorem le_of_lt_or_eq : ∀ {x y : Bool}, x < y ∨ x = y → x ≤ y := by decide

protected theorem eq_true_of_true_le : ∀ {x : Bool}, true ≤ x → x = true := by decide

protected theorem eq_false_of_le_false : ∀ {x : Bool}, x ≤ false → x = false := by decide

/-! ### min/max -/

@[simp] protected theorem max_eq_or : max = or := rfl

@[simp] protected theorem min_eq_and : min = and := rfl

/-! ### injectivity lemmas -/

theorem not_inj : ∀ {x y : Bool}, (!x) = (!y) → x = y := by decide

theorem not_inj_iff : ∀ {x y : Bool}, (!x) = (!y) ↔ x = y := by decide

theorem and_or_inj_right : ∀ {m x y : Bool}, (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  decide

theorem and_or_inj_right_iff :
    ∀ {m x y : Bool}, (x && m) = (y && m) ∧ (x || m) = (y || m) ↔ x = y := by decide

theorem and_or_inj_left : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  decide

theorem and_or_inj_left_iff :
    ∀ {m x y : Bool}, (m && x) = (m && y) ∧ (m || x) = (m || y) ↔ x = y := by decide

/-! ## toNat -/

/--
Converts `true` to `1` and `false` to `0`.
-/
@[expose, implicit_reducible] def toNat (b : Bool) : Nat := cond b 1 0

@[simp, bitvec_to_nat, grind =] theorem toNat_false : false.toNat = 0 := rfl

@[simp, bitvec_to_nat, grind =] theorem toNat_true : true.toNat = 1 := rfl

theorem toNat_le (c : Bool) : c.toNat ≤ 1 := by
  cases c <;> trivial

@[bitvec_to_nat]
theorem toNat_lt (b : Bool) : b.toNat < 2 :=
  Nat.lt_succ_of_le (toNat_le _)

@[simp] theorem toNat_eq_zero {b : Bool} : b.toNat = 0 ↔ b = false := by
  cases b <;> simp
@[simp] theorem toNat_eq_one  {b : Bool} : b.toNat = 1 ↔ b = true := by
  cases b <;> simp

/-! ## toInt -/

/--
Converts `true` to `1` and `false` to `0`.
-/
@[expose] def toInt (b : Bool) : Int := cond b 1 0

@[simp, grind =] theorem toInt_false : false.toInt = 0 := rfl

@[simp, grind =] theorem toInt_true : true.toInt = 1 := rfl

/-! ### ite -/

@[simp] theorem if_true_left  (p : Prop) [h : Decidable p] (f : Bool) :
    (ite p true f) = (p || f) := by cases h with | _ p => simp [p]

@[simp] theorem if_false_left  (p : Prop) [h : Decidable p] (f : Bool) :
    (ite p false f) = (!p && f) := by cases h with | _ p => simp [p]

@[simp] theorem if_true_right  (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t true) = (!(p : Bool) || t) := by cases h with | _ p => simp [p]

@[simp] theorem if_false_right  (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by cases h with | _ p => simp [p]

@[simp] theorem ite_eq_true_distrib (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = true) = ite p (t = true) (f = true) := by
  cases h with | _ p => simp [p]

@[simp] theorem ite_eq_false_distrib (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = false) = ite p (t = false) (f = false) := by
  cases h with | _ p => simp [p]

@[simp] theorem ite_eq_false : (if b = false then p else q) ↔ if b then q else p := by
  cases b <;> simp

@[simp] theorem ite_eq_true_else_eq_false {q : Prop} :
    (if b = true then q else b = false) ↔ (b = true → q) := by
  cases b <;> simp

/-
`not_ite_eq_true_eq_true` and related theorems below are added for
non-confluence.  A motivating example is
`¬((if u then b else c) = true)`.

This reduces to:
1. `¬((if u then (b = true) else (c = true))` via `ite_eq_true_distrib`
2. `(if u then b c) = false)` via `Bool.not_eq_true`.

Similar logic holds for `¬((if u then b else c) = false)` and related
lemmas.
-/

@[simp]
theorem not_ite_eq_true_eq_true {p : Prop} [h : Decidable p] {b c : Bool} :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  cases h with | _ p => simp [p]

@[simp]
theorem not_ite_eq_false_eq_false {p : Prop} [h : Decidable p] {b c : Bool} :
  ¬(ite p (b = false) (c = false)) ↔ (ite p (b = true) (c = true)) := by
  cases h with | _ p => simp [p]

@[simp]
theorem not_ite_eq_true_eq_false {p : Prop} [h : Decidable p] {b c : Bool} :
  ¬(ite p (b = true) (c = false)) ↔ (ite p (b = false) (c = true)) := by
  cases h with | _ p => simp [p]

@[simp]
theorem not_ite_eq_false_eq_true {p : Prop} [h : Decidable p] {b c : Bool} :
  ¬(ite p (b = false) (c = true)) ↔ (ite p (b = true) (c = false)) := by
  cases h with | _ p => simp [p]

/-
It would be nice to have this for confluence between `if_true_left` and `ite_false_same` on
`if b = true then True else b = true`.
However the discrimination tree key is just `→`, so this is tried too often.
-/
theorem eq_false_imp_eq_true : ∀ {b : Bool}, (b = false → b = true) ↔ (b = true) := by decide

/-
It would be nice to have this for confluence between `if_true_left` and `ite_false_same` on
`if b = false then True else b = false`.
However the discrimination tree key is just `→`, so this is tried too often.
-/
theorem eq_true_imp_eq_false : ∀ {b : Bool}, (b = true → b = false) ↔ (b = false) := by decide

/-! ### forall -/

theorem forall_bool' {p : Bool → Prop} (b : Bool) : (∀ x, p x) ↔ p b ∧ p !b :=
  ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨h₁, h₂⟩ x ↦ by cases b <;> cases x <;> assumption⟩

@[simp]
theorem forall_bool {p : Bool → Prop} : (∀ b, p b) ↔ p false ∧ p true :=
  forall_bool' false

/-! ### exists -/

theorem exists_bool' {p : Bool → Prop} (b : Bool) : (∃ x, p x) ↔ p b ∨ p !b :=
  ⟨fun ⟨x, hx⟩ ↦ by cases x <;> cases b <;> first | exact .inl ‹_› | exact .inr ‹_›,
    fun h ↦ by cases h <;> exact ⟨_, ‹_›⟩⟩

@[simp]
theorem exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p false ∨ p true :=
  exists_bool' false

/-! ### cond -/

theorem cond_eq_ite {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by
  cases b <;> simp

@[deprecated cond_eq_ite (since := "2025-10-29")]
theorem cond_eq_if : (bif b then x else y) = (if b then x else y) := cond_eq_ite b x y

@[simp] theorem cond_not (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by
  cases b <;> rfl

@[simp] theorem cond_self (c : Bool) (t : α) : cond c t t = t := by cases c <;> rfl

/-- If the return values are propositions, there is no harm in simplifying a `bif` to an `if`. -/
@[simp] theorem cond_prop {b : Bool} {p q : Prop} :
    (bif b then p else q) ↔ if b then p else q := by
  cases b <;> simp

/-
This is a simp rule in Mathlib, but results in non-confluence that is difficult
to fix as decide distributes over propositions. As an example, observe that
`cond (decide (p ∧ q)) t f` could simplify to either:

* `if p ∧ q then t else f` via `Bool.cond_decide` or
* `cond (decide p && decide q) t f` via `Bool.decide_and`.

A possible approach to improve normalization between `cond` and `ite` would be
to completely simplify away `cond` by making `cond_eq_ite` a `simp` rule, but
that has not been taken since it could surprise users to migrate pure `Bool`
operations like `cond` to a mix of `Prop` and `Bool`.
-/
theorem cond_decide {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  simp [cond_eq_ite]

@[simp] theorem cond_eq_ite_iff {a : Bool} {p : Prop} [h : Decidable p] {x y u v : α} :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  simp [Bool.cond_eq_ite]

@[simp] theorem ite_eq_cond_iff {p : Prop} {a : Bool} [h : Decidable p] {x y u v : α} :
  (ite p x y = cond a u v) ↔ ite p x y = ite a u v := by
  simp [Bool.cond_eq_ite]

@[simp] theorem cond_eq_true_distrib : ∀(c t f : Bool),
    (cond c t f = true) = ite (c = true) (t = true) (f = true) := by
  decide

@[simp] theorem cond_eq_false_distrib : ∀(c t f : Bool),
    (cond c t f = false) = ite (c = true) (t = false) (f = false) := by decide

protected theorem cond_true  {α : Sort u} {a b : α} : cond true  a b = a := cond_true  a b
protected theorem cond_false {α : Sort u} {a b : α} : cond false a b = b := cond_false a b

@[simp] theorem cond_true_left   : ∀(c f : Bool), cond c true f  = ( c || f) := by decide
@[simp] theorem cond_false_left  : ∀(c f : Bool), cond c false f = (!c && f) := by decide
@[simp] theorem cond_true_right  : ∀(c t : Bool), cond c t true  = (!c || t) := by decide
@[simp] theorem cond_false_right : ∀(c t : Bool), cond c t false = ( c && t) := by decide

-- These restore confluence between the above lemmas and `cond_not`.
@[simp] theorem cond_then_not_self  : ∀ (c b : Bool), cond c (!c) b = (!c && b) := by decide
@[simp] theorem cond_else_not_self : ∀ (c b : Bool), cond c b (!c) = (!c || b) := by decide

@[simp] theorem cond_then_self  : ∀ (c b : Bool), cond c c b = (c || b) := by decide
@[simp] theorem cond_else_self : ∀ (c b : Bool), cond c b c = (c && b) := by decide

theorem cond_pos {b : Bool} {a a' : α} (h : b = true) : (bif b then a else a') = a := by
  rw [h, cond_true]

theorem cond_neg {b : Bool} {a a' : α} (h : b = false) : (bif b then a else a') = a' := by
  rw [h, cond_false]

theorem apply_cond (f : α → β) {b : Bool} {a a' : α} :
    f (bif b then a else a') = bif b then f a else f a' := by
  cases b <;> simp

/-! # decidability -/

protected theorem decide_coe (b : Bool) [Decidable (b = true)] : decide (b = true) = b := decide_eq_true

@[simp] theorem decide_and (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∧ q) = (p && q) := by
  cases dp with | _ p => simp [p]

@[simp] theorem decide_or (p q : Prop) [dpq : Decidable (p ∨ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∨ q) = (p || q) := by
  cases dp with | _ p => simp [p]

@[simp] theorem decide_iff_dist (p q : Prop) [dpq : Decidable (p ↔ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ↔ q) = (decide p == decide q) := by
  cases dp with | _ p => simp [p]

@[bool_to_prop]
theorem and_eq_decide (p q : Bool) : (p && q) = decide (p ∧ q) := by simp

@[bool_to_prop]
theorem or_eq_decide (p q : Bool) : (p || q) = decide (p ∨ q) := by simp

@[bool_to_prop]
theorem decide_beq_decide (p q : Prop) [dpq : Decidable (p ↔ q)] [dp : Decidable p] [dq : Decidable q] :
    (decide p == decide q) = decide (p ↔ q) := by
  cases dp with | _ p => simp [p]

end Bool

export Bool (cond_eq_if cond_eq_ite xor and or not)

/-! ### decide -/

@[simp] theorem false_eq_decide_iff {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with | _ q => simp [q]

@[simp] theorem true_eq_decide_iff {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]

/-! ### coercions -/

/--
This should not be turned on globally as an instance because it degrades performance in Mathlib,
but may be used locally.
-/
@[instance_reducible]
def boolPredToPred : Coe (α → Bool) (α  → Prop) where
  coe r := fun a => Eq (r a) true

/--
This should not be turned on globally as an instance because it degrades performance in Mathlib,
but may be used locally.
-/
@[expose, instance_reducible] def boolRelToRel : Coe (α → α → Bool) (α → α → Prop) where
  coe r := fun a b => Eq (r a b) true

/-! ### subtypes -/

@[simp] theorem Subtype.beq_iff {α : Type u} [BEq α] {p : α → Prop} {x y : {a : α // p a}} :
    (x == y) = (x.1 == y.1) := rfl

/-! ### Proof by reflection support  -/

@[expose] protected noncomputable def Bool.and' (a b : Bool) : Bool :=
  Bool.rec false b a

@[expose] protected noncomputable def Bool.or' (a b : Bool) : Bool :=
  Bool.rec b true a

@[expose] protected noncomputable def Bool.not' (a : Bool) : Bool :=
  Bool.rec true false a

@[simp] theorem Bool.and'_eq_and (a b : Bool) : a.and' b = a.and b := by
  cases a <;> simp [Bool.and']

@[simp] theorem Bool.or'_eq_or (a b : Bool) : a.or' b = a.or b := by
  cases a <;> simp [Bool.or']

@[simp] theorem Bool.not'_eq_not (a : Bool) : a.not' = a.not := by
  cases a <;> simp [Bool.not']

theorem Bool.rec_eq {α : Sort _} (b : Bool) {x y : α} : Bool.rec y x b = if b then x else y := by
  cases b <;> simp
