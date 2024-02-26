/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/
prelude
import Init.BinderPredicates
import Init.ByCases

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

@[simp] theorem decide_eq_true  {b : Bool} {h : Decidable (b = true)}  : @decide (b = true)  h =  b := by cases b <;> simp
@[simp] theorem decide_eq_false {b : Bool} {h : Decidable (b = false)} : @decide (b = false) h = !b := by cases b <;> simp
@[simp] theorem decide_true_eq  {b : Bool} {h : Decidable (true = b)}  : @decide (true  = b) h =  b := by cases b <;> simp
@[simp] theorem decide_false_eq {b : Bool} {h : Decidable (false = b)} : @decide (false = b) h = !b := by cases b <;> simp

/-! ### and -/

/- jhx: consistency with `and_self_left` and `and_self_right` for `Prop`. -/
@[simp] theorem and_self_left  : ∀(a b : Bool), (a && (a && b)) = (a && b) := by decide
@[simp] theorem and_self_right : ∀(a b : Bool), ((a && b) && b) = (a && b) := by decide

@[simp] theorem not_and_self : ∀ (x : Bool), (!x && x) = false := by decide

@[simp] theorem and_not_self : ∀ (x : Bool), (x && !x) = false := by decide

theorem and_comm : ∀ (x y : Bool), (x && y) = (y && x) := by decide

theorem and_left_comm : ∀ (x y z : Bool), (x && (y && z)) = (y && (x && z)) := by decide

theorem and_right_comm : ∀ (x y z : Bool), ((x && y) && z) = ((x && z) && y) := by decide


/-! ### or -/

/- jhx: consistency with `or_self_left` and `or_self_right` (simp theorems in Std). -/
@[simp] theorem or_self_left : ∀(a b : Bool), (a || (a || b)) = (a || b) := by decide
@[simp] theorem or_self_right : ∀(a b : Bool), ((a || b) || b) = (a || b) := by decide

@[simp] theorem not_or_self : ∀ (x : Bool), (!x || x) = true := by decide

@[simp] theorem or_not_self : ∀ (x : Bool), (x || !x) = true := by decide

theorem or_comm : ∀ (x y : Bool), (x || y) = (y || x) := by decide

theorem or_left_comm : ∀ (x y z : Bool), (x || (y || z)) = (y || (x || z)) := by decide

theorem or_right_comm : ∀ (x y z : Bool), ((x || y) || z) = ((x || z) || y) := by decide

/-! ### distributivity -/

theorem and_or_distrib_left : ∀ (x y z : Bool), (x && (y || z)) = ((x && y) || (x && z)) := by
  decide

theorem and_or_distrib_right : ∀ (x y z : Bool), ((x || y) && z) = ((x && z) || (y && z)) := by
  decide

theorem or_and_distrib_left : ∀ (x y z : Bool), (x || (y && z)) = ((x || y) && (x || z)) := by
  decide

theorem or_and_distrib_right : ∀ (x y z : Bool), ((x && y) || z) = ((x || z) && (y || z)) := by
  decide

/-- De Morgan's law for boolean and -/
/- jhx: simp in Mathlib -/
@[simp] theorem not_and : ∀ (x y : Bool), (!(x && y)) = (!x || !y) := by decide

/-- De Morgan's law for boolean or -/
/- jhx: simp in Mathlib -/
@[simp] theorem not_or : ∀ (x y : Bool), (!(x || y)) = (!x && !y) := by decide

/- jhx: simp in Mathlib as Mathlib as `Bool.and_eq_true_eq_eq_true_and_eq_true`. -/
theorem and_eq_true_iff (x y : Bool) : (x && y) = true ↔ x = true ∧ y = true :=
  Iff.of_eq (and_eq_true x y)

theorem and_eq_false_iff : ∀ (x y : Bool), (x && y) = false ↔ x = false ∨ y = false := by decide

/-
New simp rule that replaces `Bool.and_eq_false_eq_eq_false_or_eq_false` in
Mathlib due to confluence:

Consider the term: `¬((b && c) = true)`:

1. Reduces to `((b && c) = false)` via `Bool.not_eq_true`
2. Reduces to `¬(b = true ∧ c = true)` via `Bool.and_eq_true`.


1. Further reduces to `b = false ∨ c = false` via `Bool.and_eq_false_eq_eq_false_or_eq_false`.
2. Further reduces to `b = true → c = false` via `not_and` and `Bool.not_eq_true`.
-/
@[simp]
theorem and_eq_false_imp : ∀ (x y : Bool), (x && y) = false ↔ (x = true → y = false) := by decide

/- jhx: simp for parity with `or_eq_false_iff`. -/
@[simp] theorem or_eq_true_iff : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by decide

/- jhx: simp in Mathlib as `Bool.or_eq_false_eq_eq_false_and_eq_false`. -/
@[simp] theorem or_eq_false_iff : ∀ (x y : Bool), (x || y) = false ↔ x = false ∧ y = false := by decide

/-! ### beq/bne -/

/- Added for constency with `and_not_self`, `or_not_self`, `bne_not_self` and related. -/
@[simp] theorem not_beq_self : ∀ (x : Bool), (!x == x) = false := by decide
@[simp] theorem beq_not_self : ∀ (x : Bool), (x == !x) = false := by decide

/- These were added for constency with `and_self_left` `or_self_left` and related. -/
@[simp] theorem beq_self_left (a b : Bool) : (a == (a == b)) = b := by revert a b ; decide
@[simp] theorem beq_self_right (a b : Bool) : ((a == b) == b) = a := by revert a b ; decide
@[simp] theorem bne_self_left (a b : Bool) : (a != (a != b)) = b := by revert a b ; decide
@[simp] theorem bne_self_right (a b : Bool) : ((a != b) != b) = a := by revert a b ; decide

/- In std as `not_xor_not`. -/
@[simp] theorem not_bne_not : ∀ (x y : Bool), ((!x) != (!y)) = (x != y) := by decide

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

/-! ###  beq -/

/- hxx: Added for compat with `true_bne`. -/
@[simp] theorem true_beq  : ∀b, (true  == b) =  b := by decide
@[simp] theorem false_beq : ∀b, (false == b) = !b := by decide
@[simp] theorem beq_true  : ∀b, (b == true)  =  b := by decide
@[simp] theorem beq_false : ∀b, (b == false) = !b := by decide

/- jhx: simp rule `true_xor` in std -/
@[simp] theorem true_bne  : ∀(b : Bool), (true  != b) = !b := by decide
/- simp rule `false_xor` in std -/
@[simp] theorem false_bne : ∀(b : Bool), (false != b) =  b := by decide
/- simp rule `xor_true` in std -/
@[simp] theorem bne_true  : ∀(b : Bool), (b != true)  = !b := by decide
/- simp rule `xor_false` in std -/
@[simp] theorem bne_false : ∀(b : Bool), (b != false) =  b := by decide


/- jhx: std as `not_xor_self` and `xor_not_self`. -/
@[simp] theorem not_bne_self : ∀ (x : Bool), ((!x) != x) = true := by decide
@[simp] theorem bne_not_self : ∀ (x : Bool), (x != !x) = true := by decide


/--
In Std as xor_assoc (not simp rule in std, but made one in Mathlib)
-/
@[simp]
theorem bne_assoc : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by decide

/--
In Std as xor_left_inj (simp rule)
-/
@[simp]
theorem bne_left_inj : ∀ (x y z : Bool), (x != y) = (x != z) ↔ y = z := by decide

/--
In Std as xor_right_inj (simp rule)
-/
@[simp]
theorem bne_right_inj : ∀ (x y z : Bool), (x != z) = (y != z) ↔ x = y := by decide

/-! ### bool to prop normal forms: b = true, b = false -/

/- ### Simp lemmas for Bool to Prop normal forms: `b = true`, `b = false`-/

/- jhx: Mathlib simp rule. -/
@[simp] theorem not_eq_not : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by decide

/- jhx: Mathlib simp rule. -/
@[simp] theorem not_not_eq : ∀ {a b : Bool}, ¬(!a) = b ↔ a = b := by decide


/- New simp rule -/
@[simp] theorem coe_iff_coe : ∀(a b : Bool), (a ↔ b) ↔ a = b := by decide

/- New simp rule -/
@[simp] theorem coe_true_iff_false : ∀(a b : Bool), (a ↔ b = false) ↔ a = (!b) := by decide

/- New simp rule -/
@[simp] theorem coe_false_iff_true : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by decide

/- New simp rule -/
@[simp] theorem coe_false_iff_false : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by decide

/-! ### xor -/

theorem false_xor : ∀ (x : Bool), xor false x = x := false_bne

theorem xor_false : ∀ (x : Bool), xor x false = x := bne_false

theorem true_xor : ∀ (x : Bool), xor true x = !x := true_bne

theorem xor_true : ∀ (x : Bool), xor x true = !x := bne_true

theorem not_xor_self : ∀ (x : Bool), xor (!x) x = true := not_bne_self

theorem xor_not_self : ∀ (x : Bool), xor x (!x) = true := bne_not_self

theorem not_xor : ∀ (x y : Bool), xor (!x) y = !(xor x y) := by decide

theorem xor_not : ∀ (x y : Bool), xor x (!y) = !(xor x y) := by decide

theorem not_xor_not : ∀ (x y : Bool), xor (!x) (!y) = (xor x y) := not_bne_not

theorem xor_self : ∀ (x : Bool), xor x x = false := by decide

theorem xor_comm : ∀ (x y : Bool), xor x y = xor y x := by decide

theorem xor_left_comm : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by decide

theorem xor_right_comm : ∀ (x y z : Bool), xor (xor x y) z = xor (xor x z) y := by decide

theorem xor_assoc : ∀ (x y z : Bool), xor (xor x y) z = xor x (xor y z) := bne_assoc

theorem xor_left_inj : ∀ (x y z : Bool), xor x y = xor x z ↔ y = z := bne_left_inj

theorem xor_right_inj : ∀ (x y z : Bool), xor x z = xor y z ↔ x = y := bne_right_inj

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


/-! ### ite -/

/- Added for compatibility with `if_true_left` (Mathlib simp rule) -/
@[simp]
theorem if_true_left  (p : Prop) {h : Decidable p} (f : Bool) :
    (ite p true f) = (p || f) := by by_cases h : p <;> simp [h]

/- Added for compatibility with `if_false_left` (Mathlib simp rule) -/
@[simp]
theorem if_false_left  (p : Prop) {h : Decidable p} (f : Bool) :
    (ite p false f) = (!p && f) := by by_cases h : p <;> simp [h]

/- Added for compatibility with `if_true_right` (Mathlib simp rule) -/
@[simp]
theorem if_true_right  (p : Prop) {h : Decidable p} (t : Bool) :
    (ite p t true) = (!(p : Bool) || t) := by by_cases h : p <;> simp [h]

/- Added for compatibility with `if_false_right` (Mathlib simp rule) -/
@[simp]
theorem if_false_right  (p : Prop) {h : Decidable p} (t : Bool) :
    (ite p t false) = (p && t) := by by_cases h : p <;> simp [h]

/- jhx:  Mathlib simp rule -/
@[simp] theorem ite_eq_true_distrib (p : Prop) {h : Decidable p} (t f : Bool) :
    (ite p t f = true) = ite p (t = true) (f = true) := by
  by_cases h : p <;> simp [h]

/- jhx: Mathlib simp rule -/
@[simp] theorem ite_eq_false_distrib (p : Prop) {h : Decidable p} (t f : Bool) :
    (ite p t f = false) = ite p (t = false) (f = false) := by
  by_cases h : p <;> simp [h]

/-
`not_if_prop_coerce_true` and `not_if_prop_coerce_false` are added
for non-confluence.  The motivating example for `not_if_prop_coerce_true`
is `¬((if u then b else c) = true)`.

This reduces to:
1. `¬((if u then (b = true) else (c = true))` via `ite_eq_true_distrib`
2. `(if u then b c) = false)` via `Bool.not_eq_true`.

Similar logic holds for `¬((if u then b else c) = false)` and related
lemmas.
-/

@[simp]
theorem not_ite_eq_true_eq_true (p : Prop) {h : Decidable p} (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  by_cases h : p <;> simp [h]

@[simp]
theorem not_ite_eq_false_eq_false (p : Prop) {h : Decidable p} (b c : Bool) :
  ¬(ite p (b = false) (c = false)) ↔ (ite p (b = true) (c = true)) := by
  by_cases h : p <;> simp [h]

/- Added for consistency with `not_ite_eq_true_eq_true` -/
@[simp]
theorem not_ite_eq_true_eq_false (p : Prop) {h : Decidable p} (b c : Bool) :
  ¬(ite p (b = true) (c = false)) ↔ (ite p (b = false) (c = true)) := by
  by_cases h : p <;> simp [h]

/- Added for consistency with `not_ite_eq_true_eq_true` -/
@[simp]
theorem not_ite_eq_false_eq_true (p : Prop) {h : Decidable p} (b c : Bool) :
  ¬(ite p (b = false) (c = true)) ↔ (ite p (b = true) (c = false)) := by
  by_cases h : p <;> simp [h]

/-! ### cond -/

theorem cond_eq_if : (bif b then x else y) = (if b then x else y) := by
  cases b <;> simp

theorem cond_eq_ite {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by
  cases b <;> simp

/- Mathlib simp rule -/
@[simp]
theorem cond_not {α : Type _} (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by cases b <;> rfl

/- Mathlib simp rule-/
@[simp] theorem cond_self {α} (c : Bool) (t : α) : cond c t t = t := by cases c <;> simp

/-
This is a simp rule in Mathlib, but results in non-confluence that is
difficult to fix as decide distributes over propositions.

A possible fix would be to completely simplify away `cond`, but that
is not taken since it could result in major rewriting of code that is
otherwise purely about `Bool`.
-/
theorem cond_decide {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  simp [cond_eq_ite]

/-
In lieu of cond_decide or cond_eq_ite being simp, we have more restained simp rules
`cond_eq_ite_iff` and `ite_eq_cond_iff`.
-/

@[simp]
theorem cond_eq_ite_iff (a : Bool) (p : Prop) {h : Decidable p} (x y u v : α) :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  simp [Bool.cond_eq_ite]

@[simp]
theorem ite_eq_cond_iff (p : Prop) {h : Decidable p} (a : Bool) (x y u v : α) :
  (ite p x y = cond a u v) ↔ ite p x y = ite a u v := by
  simp [Bool.cond_eq_ite]

/--
New rule (added for consistency with ite_eq_true_distrib)
-/
@[simp] theorem cond_eq_true_distrib : ∀(c t f : Bool),
    (cond c t f = true) = ite (c = true) (t = true) (f = true) := by
  decide

/--
New rule (added for consistency with ite_eq_false_distrib)
-/
@[simp] theorem cond_eq_false_distrib : ∀(c t f : Bool),
    (cond c t f = false) = ite (c = true) (t = false) (f = false) := by decide

/- jhx: Mathlib clone -/
protected theorem cond_true {α : Type u} {a b : α} : cond true a b = a := cond_true a b
protected theorem cond_false {α : Type u} {a b : α} : cond false a b = b := cond_false a b

/- jhx: parity with `if_true_left` -/
@[simp] theorem cond_true_left : ∀(c f : Bool), cond c true f = (c || f) := by decide

/- jhx: parity with `if_false_left` -/
@[simp] theorem cond_false_left : ∀(c f : Bool), cond c false f = (!c && f) := by decide

/- jhx: parity with `if_true_right` -/
@[simp] theorem cond_true_right : ∀(c t : Bool), cond c t true = (!c || t) := by decide
/- jhx: parity with `if_false_right` -/
@[simp] theorem cond_false_right : ∀(c t : Bool), cond c t false = (c && t) := by decide

/- jhx: New simp rules -/
@[simp] theorem cond_true_same  : ∀(c b : Bool), cond c c b = (c || b) := by decide
@[simp] theorem cond_false_same : ∀(c b : Bool), cond c b c = (c && b) := by decide

/-# decidability -/

protected theorem decide_coe (b : Bool) {h : Decidable (b = true)} : @decide (b = true) h = b := decide_eq_true

/- Mathlib simp rule -/
@[simp]
theorem decide_and (p q : Prop) {dpq : Decidable (p ∧ q)} {dp : Decidable p} {dq : Decidable q} :
    decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]

/- Mathlib simp rule -/
@[simp]
theorem decide_or (p q : Prop) {dpq : Decidable (p ∨ q)} {dp : Decidable p} {dq : Decidable q} :
    decide (p ∨ q) = (p || q) := by
  by_cases p <;> by_cases q <;> simp [*]

/-
This is a new rule.  Added for consistency with decide_and/decide_or.
-/
@[simp]
theorem decide_iff_dist (p q : Prop) {dpq : Decidable (p ↔ q)} {dp : Decidable p} {dq : Decidable q} :
    decide (p ↔ q) = (decide p == decide q) := by
  by_cases g : p <;> by_cases h : q <;> simp [g, h, BEq.beq]

end Bool

export Bool (cond_eq_if)

/-! ### decide -/

@[simp] theorem false_eq_decide_iff {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with | _ q => simp [q]

@[simp] theorem true_eq_decide_iff {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]
