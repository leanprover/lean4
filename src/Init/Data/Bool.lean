/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/
prelude
import Init.BinderPredicates

/-- Boolean exclusive or -/
abbrev xor : Bool → Bool → Bool := bne

namespace Bool

/- Namespaced versions that can be used instead of prefixing `_root_` -/
@[inherit_doc not] protected abbrev not := not
@[inherit_doc or]  protected abbrev or  := or
@[inherit_doc and] protected abbrev and := and
@[inherit_doc xor] protected abbrev xor := xor

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

@[simp] theorem decide_eq_true {b : Bool} : decide (b = true) = b := by cases b <;> simp
@[simp] theorem decide_eq_false {b : Bool} : decide (b = false) = !b := by cases b <;> simp
@[simp] theorem decide_true_eq {b : Bool} : decide (true = b) = b := by cases b <;> simp
@[simp] theorem decide_false_eq {b : Bool} : decide (false = b) = !b := by cases b <;> simp

/-! ### and -/

@[simp] theorem not_and_self : ∀ (x : Bool), (!x && x) = false := by decide

@[simp] theorem and_not_self : ∀ (x : Bool), (x && !x) = false := by decide

theorem and_comm : ∀ (x y : Bool), (x && y) = (y && x) := by decide

theorem and_left_comm : ∀ (x y z : Bool), (x && (y && z)) = (y && (x && z)) := by decide

theorem and_right_comm : ∀ (x y z : Bool), ((x && y) && z) = ((x && z) && y) := by decide

theorem and_or_distrib_left : ∀ (x y z : Bool), (x && (y || z)) = ((x && y) || (x && z)) := by
  decide

theorem and_or_distrib_right : ∀ (x y z : Bool), ((x || y) && z) = ((x && z) || (y && z)) := by
  decide

theorem and_xor_distrib_left : ∀ (x y z : Bool), (x && xor y z) = xor (x && y) (x && z) := by decide

theorem and_xor_distrib_right : ∀ (x y z : Bool), (xor x y && z) = xor (x && z) (y && z) := by
  decide

/-- De Morgan's law for boolean and -/
theorem not_and : ∀ (x y : Bool), (!(x && y)) = (!x || !y) := by decide

theorem and_eq_true_iff : ∀ (x y : Bool), (x && y) = true ↔ x = true ∧ y = true := by decide

theorem and_eq_false_iff : ∀ (x y : Bool), (x && y) = false ↔ x = false ∨ y = false := by decide

/-! ### or -/

@[simp] theorem not_or_self : ∀ (x : Bool), (!x || x) = true := by decide

@[simp] theorem or_not_self : ∀ (x : Bool), (x || !x) = true := by decide

theorem or_comm : ∀ (x y : Bool), (x || y) = (y || x) := by decide

theorem or_left_comm : ∀ (x y z : Bool), (x || (y || z)) = (y || (x || z)) := by decide

theorem or_right_comm : ∀ (x y z : Bool), ((x || y) || z) = ((x || z) || y) := by decide

theorem or_and_distrib_left : ∀ (x y z : Bool), (x || (y && z)) = ((x || y) && (x || z)) := by
  decide

theorem or_and_distrib_right : ∀ (x y z : Bool), ((x && y) || z) = ((x || z) && (y || z)) := by
  decide

/-- De Morgan's law for boolean or -/
theorem not_or : ∀ (x y : Bool), (!(x || y)) = (!x && !y) := by decide

theorem or_eq_true_iff : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by decide

theorem or_eq_false_iff : ∀ (x y : Bool), (x || y) = false ↔ x = false ∧ y = false := by decide

/-! ### xor -/

@[simp] theorem false_xor : ∀ (x : Bool), xor false x = x := by decide

@[simp] theorem xor_false : ∀ (x : Bool), xor x false = x := by decide

@[simp] theorem true_xor : ∀ (x : Bool), xor true x = !x := by decide

@[simp] theorem xor_true : ∀ (x : Bool), xor x true = !x := by decide

@[simp] theorem not_xor_self : ∀ (x : Bool), xor (!x) x = true := by decide

@[simp] theorem xor_not_self : ∀ (x : Bool), xor x (!x) = true := by decide

theorem not_xor : ∀ (x y : Bool), xor (!x) y = !(xor x y) := by decide

theorem xor_not : ∀ (x y : Bool), xor x (!y) = !(xor x y) := by decide

@[simp] theorem not_xor_not : ∀ (x y : Bool), xor (!x) (!y) = (xor x y) := by decide

theorem xor_self : ∀ (x : Bool), xor x x = false := by decide

theorem xor_comm : ∀ (x y : Bool), xor x y = xor y x := by decide

theorem xor_left_comm : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by decide

theorem xor_right_comm : ∀ (x y z : Bool), xor (xor x y) z = xor (xor x z) y := by decide

theorem xor_assoc : ∀ (x y z : Bool), xor (xor x y) z = xor x (xor y z) := by decide

@[simp]
theorem xor_left_inj : ∀ (x y z : Bool), xor x y = xor x z ↔ y = z := by decide

@[simp]
theorem xor_right_inj : ∀ (x y z : Bool), xor x z = xor y z ↔ x = y := by decide

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

/-- convert a `Bool` to a `Nat`, `false -> 0`, `true -> 1` -/
def toNat (b:Bool) : Nat := cond b 1 0

@[simp] theorem toNat_false : false.toNat = 0 := rfl

@[simp] theorem toNat_true : true.toNat = 1 := rfl

theorem toNat_le (c : Bool) : c.toNat ≤ 1 := by
  cases c <;> trivial

@[deprecated toNat_le] abbrev toNat_le_one := toNat_le

theorem toNat_lt (b : Bool) : b.toNat < 2 :=
  Nat.lt_succ_of_le (toNat_le _)

@[simp] theorem toNat_eq_zero (b : Bool) : b.toNat = 0 ↔ b = false := by
  cases b <;> simp
@[simp] theorem toNat_eq_one (b : Bool) : b.toNat = 1 ↔ b = true := by
  cases b <;> simp

end Bool

/-! ### cond -/

theorem cond_eq_if : (bif b then x else y) = (if b then x else y) := by
  cases b <;> simp

/-! ### decide -/

@[simp] theorem false_eq_decide_iff {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with | _ q => simp [q]

@[simp] theorem true_eq_decide_iff {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]
