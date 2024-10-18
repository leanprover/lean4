-- Regressions for #3210

example : ¬1 % 2 = 0 := by
  simp

universe u

class One (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1
instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

example : Not
  (@Eq.{1} Nat
    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (@One.toOfNat1.{0} Nat (@One.ofOfNat1.{0} Nat (instOfNatNat (nat_lit 1)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  simp

@[simp] theorem OfNat.ofNat_ofNat : OfNat.ofNat (no_index OfNat.ofNat n) = OfNat.ofNat n := rfl

example : Not
  (@Eq.{1} Nat
    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
      (@OfNat.ofNat.{0} Nat 1 (@One.toOfNat1.{0} Nat (@One.ofOfNat1.{0} Nat (instOfNatNat 1))))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
    (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) := by
  simp only [reduceCtorEq, not_false_eq_true]

def WithTop (α : Type) := Option α

class Top (α : Type) where top : α

instance top : Top (WithTop α) := ⟨none⟩

example {α : Type} (x : α) : ¬ some x = (Top.top : WithTop α) := by simp
