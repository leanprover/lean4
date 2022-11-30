import Lean

/- from core:
class OfNat (α : Type u) (n : Nat) where
  ofNat : α
class Mul (α : Type u) where
  mul : α → α → α
class Add (α : Type u) where
  add : α → α → α
-/

class Inv (α : Type u) where
    inv : α → α

postfix:max "⁻¹" => Inv.inv

class One (α : Type u) where
    one : α
export One (one)

instance [One α] : OfNat α (nat_lit 1) where
    ofNat := one

class Zero (α : Type u) where
    zero : α
export Zero (zero)

instance [Zero α] : OfNat α (nat_lit 0) where
    ofNat := zero

class MulComm (α : Type u) [Mul α] : Prop where
    mul_comm : {a b : α} → a * b = b * a
export MulComm (mul_comm)

class MulAssoc (α : Type u) [Mul α] : Prop where
    mul_assoc : {a b c : α} → a * b * c = a * (b * c)
export MulAssoc (mul_assoc)

class OneUnit (α : Type u) [Mul α] [One α] : Prop where
    one_mul : {a : α} → 1 * a = a
    mul_one : {a : α} → a * 1 = a
export OneUnit (one_mul mul_one)

class AddComm (α : Type u) [Add α] : Prop where
    add_comm : {a b : α} → a + b = b + a
export AddComm (add_comm)

class AddAssoc (α : Type u) [Add α] : Prop where
    add_assoc : {a b c : α} → a + b + c = a + (b + c)
export AddAssoc (add_assoc)

class ZeroUnit (α : Type u) [Add α] [Zero α] : Prop where
    zero_add : {a : α} → 0 + a = a
    add_zero : {a : α} → a + 0 = a
export ZeroUnit (zero_add add_zero)

class InvMul (α : Type u) [Mul α] [One α] [Inv α] : Prop where
    inv_mul : {a : α} → a⁻¹ * a = 1
export InvMul (inv_mul)

class NegAdd (α : Type u) [Add α] [Zero α] [Neg α] : Prop where
    neg_add : {a : α} → -a + a = 0
export NegAdd (neg_add)

class ZeroMul (α : Type u) [Mul α] [Zero α] : Prop where
    zero_mul : {a : α} → 0 * a = 0
export ZeroMul (zero_mul)

class Distrib (α : Type u) [Add α] [Mul α] : Prop where
    mul_add : {a b c : α} → a * (b + c) = a * b + a * c
    add_mul : {a b c : α} → (a + b) * c = a * c + b * c
export Distrib (mul_add add_mul)

class Domain (α : Type u) [Mul α] [Zero α] : Prop where
    eq_zero_or_eq_zero_of_mul_eq_zero : {a b : α} → a * b = 0 → a = 0 ∨ b = 0
export Domain (eq_zero_or_eq_zero_of_mul_eq_zero)

class abbrev Semigroup (α : Type u) := Mul α, MulAssoc α
class abbrev AddSemigroup (α : Type u) := Add α, AddAssoc α
class abbrev Monoid (α : Type u) := Semigroup α, One α, OneUnit α
class abbrev AddMonoid (α : Type u) := AddSemigroup α, Zero α, ZeroUnit α
class abbrev CommSemigroup (α : Type u) := Semigroup α, MulComm α
class abbrev CommMonoid (α : Type u) := Monoid α, MulComm α
class abbrev Group (α : Type u) := Monoid α, Inv α, InvMul α
class abbrev AddGroup (α : Type u) := AddMonoid α, Neg α, NegAdd α
class abbrev Semiring (α : Type u) := AddMonoid α, Monoid α, AddComm α, ZeroMul α, Distrib α
class abbrev Ring (α : Type u) := AddGroup α, Monoid α, AddComm α, Distrib α
class abbrev CommRing (α : Type u) := Ring α, MulComm α
class abbrev IntegralDomain (α : Type u) := CommRing α, Domain α

section test1
variable (α : Type u) [h : CommMonoid α]
example : Semigroup α := inferInstance
example : Monoid α := inferInstance
example : CommSemigroup α := inferInstance
end test1

section test2
variable (β : Type u) [CommSemigroup β] [One β] [OneUnit β]
example : Monoid β := inferInstance
example : CommMonoid β := inferInstance
example : Semigroup β := inferInstance
end test2

section test3
variable (β : Type u) [Mul β] [One β] [MulAssoc β] [OneUnit β]
example : Monoid β := inferInstance
example : Semigroup β := inferInstance
end test3

theorem neg_zero [AddGroup α] : -(0 : α) = 0 := by
    rw [←add_zero (a := -(0 : α)), neg_add]

theorem sub_zero [AddGroup α] {a : α} : a + -(0 : α) = a := by
    rw [←add_zero (a := a), add_assoc, neg_zero, add_zero]

theorem neg_neg [AddGroup α] {a : α} : -(-a) = a := by {
    rw [←add_zero (a := - -a)];
    rw [←neg_add (a := a)];
    rw [←add_assoc];
    rw [neg_add];
    rw [zero_add];
}

theorem add_neg [AddGroup α] {a : α} : a + -a = 0 := by {
    have h : - -a + -a = 0 := by { rw [neg_add] };
    rw [neg_neg] at h;
    exact h
}

theorem add_idem_iff_zero [AddGroup α] {a : α} : a + a = a ↔ a = 0 := by
    apply Iff.intro
    focus
        intro h
        have h' := congr_arg (λ x => x + -a) h
        simp at h'
        rw [add_assoc, add_neg, add_zero] at h'
        exact h'
    focus
        intro h
        subst a
        rw [add_zero]

instance [Ring α] : ZeroMul α := by {
    apply ZeroMul.mk;
    intro a;
    have h : 0 * a + 0 * a = 0 * a := by { rw [← add_mul, add_zero] };
    rw [add_idem_iff_zero (a := 0 * a)] at h;
    rw [h];
}

example [Ring α] : Semiring α := inferInstance

section prod

instance [Mul α] [Mul β] : Mul (α × β) where
    mul p p' := (p.1 * p'.1, p.2 * p'.2)

instance [Inv α] [Inv β] : Inv (α × β) where
    inv p := (p.1⁻¹, p.2⁻¹)

instance [One α] [One β] : One (α × β) where
    one := (1, 1)

theorem Product.ext : {p q : α × β} → p.1 = q.1 → p.2 = q.2 → p = q
    | (a, b), (c, d) => by simp_all

instance [Semigroup α] [Semigroup β] : Semigroup (α × β) where
    mul_assoc := by
        intros
        apply Product.ext
        apply mul_assoc
        apply mul_assoc

instance [Monoid α] [Monoid β] : Monoid (α × β) where
    one_mul := by
        intros
        apply Product.ext
        apply one_mul
        apply one_mul
    mul_one := by
        intros
        apply Product.ext
        apply mul_one
        apply mul_one

instance [Group α] [Group β] : Group (α × β) where
    inv_mul := by
        intros
        apply Product.ext
        apply inv_mul
        apply inv_mul

end prod
