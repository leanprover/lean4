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

export Zero (zero)

instance [Zero α] : OfNat α (nat_lit 0) where
    ofNat := zero

class MulComm (α : Type u) [Mul α] : Prop where
    mulComm : {a b : α} → a * b = b * a
export MulComm (mulComm)

class MulAssoc (α : Type u) [Mul α] : Prop where
    mulAssoc : {a b c : α} → a * b * c = a * (b * c)
export MulAssoc (mulAssoc)

class OneUnit (α : Type u) [Mul α] [One α] : Prop where
    oneMul : {a : α} → 1 * a = a
    mulOne : {a : α} → a * 1 = a
export OneUnit (oneMul mulOne)

class AddComm (α : Type u) [Add α] : Prop where
    addComm : {a b : α} → a + b = b + a
export AddComm (addComm)

class AddAssoc (α : Type u) [Add α] : Prop where
    addAssoc : {a b c : α} → a + b + c = a + (b + c)
export AddAssoc (addAssoc)

class ZeroUnit (α : Type u) [Add α] [Zero α] : Prop where
    zeroAdd : {a : α} → 0 + a = a
    addZero : {a : α} → a + 0 = a
export ZeroUnit (zeroAdd addZero)

class InvMul (α : Type u) [Mul α] [One α] [Inv α] : Prop where
    invMul : {a : α} → a⁻¹ * a = 1
export InvMul (invMul)

class NegAdd (α : Type u) [Add α] [Zero α] [Neg α] : Prop where
    negAdd : {a : α} → -a + a = 0
export NegAdd (negAdd)

class ZeroMul (α : Type u) [Mul α] [Zero α] : Prop where
    zeroMul : {a : α} → 0 * a = 0
export ZeroMul (zeroMul)

class Distrib (α : Type u) [Add α] [Mul α] : Prop where
    leftDistrib : {a b c : α} → a * (b + c) = a * b + a * c
    rightDistrib : {a b c : α} → (a + b) * c = a * c + b * c
export Distrib (leftDistrib rightDistrib)

class Domain (α : Type u) [Mul α] [Zero α] : Prop where
    eqZeroOrEqZeroOfMulEqZero : {a b : α} → a * b = 0 → a = 0 ∨ b = 0
export Domain (eqZeroOrEqZeroOfMulEqZero)

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

theorem negZero [AddGroup α] : -(0 : α) = 0 := by
    rw [←addZero (a := -(0 : α)), negAdd]

theorem subZero [AddGroup α] {a : α} : a + -(0 : α) = a := by
    rw [←addZero (a := a), addAssoc, negZero, addZero]

theorem negNeg [AddGroup α] {a : α} : -(-a) = a := by {
    rw [←addZero (a := - -a)];
    rw [←negAdd (a := a)];
    rw [←addAssoc];
    rw [negAdd];
    rw [zeroAdd];
}

theorem addNeg [AddGroup α] {a : α} : a + -a = 0 := by {
    have h : - -a + -a = 0 := by { rw [negAdd] };
    rw [negNeg] at h;
    exact h
}

theorem addIdemIffZero [AddGroup α] {a : α} : a + a = a ↔ a = 0 := by
    apply Iff.intro
    focus
        intro h
        have h' := congrArg (λ x => x + -a) h
        simp at h'
        rw [addAssoc, addNeg, addZero] at h'
        exact h'
    focus
        intro h
        subst a
        rw [addZero]

instance [Ring α] : ZeroMul α := by {
    apply ZeroMul.mk;
    intro a;
    have h : 0 * a + 0 * a = 0 * a := by { rw [←rightDistrib, addZero] };
    rw [addIdemIffZero (a := 0 * a)] at h;
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
    mulAssoc := by
        intros
        apply Product.ext
        apply mulAssoc
        apply mulAssoc

instance [Monoid α] [Monoid β] : Monoid (α × β) where
    oneMul := by
        intros
        apply Product.ext
        apply oneMul
        apply oneMul
    mulOne := by
        intros
        apply Product.ext
        apply mulOne
        apply mulOne

instance [Group α] [Group β] : Group (α × β) where
    invMul := by
        intros
        apply Product.ext
        apply invMul
        apply invMul

end prod
