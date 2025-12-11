module
def Xor' (a b : Prop) := (a ∧ ¬b) ∨ (b ∧ ¬a)

@[grind =] theorem xor_def {a b : Prop} : Xor' a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a) := Iff.rfl

class Nat.AtLeastTwo' (n : Nat) : Prop where
  prop : 2 ≤ n

instance instNatAtLeastTwo' {n : Nat} : Nat.AtLeastTwo' (n + 2) where
  prop := Nat.succ_le_succ <| Nat.succ_le_succ <| Nat.zero_le _

instance (priority := 100) instOfNatAtLeastTwo'
    {R : Type _} {n : Nat} [NatCast R] [Nat.AtLeastTwo' n] :
    OfNat R n where
  ofNat := n.cast

class Distrib' (R : Type _) extends Add R where

instance Nat.instDistrib' : Distrib' Nat where

theorem Nat.even_xor_odd'.extracted_1_2 (k : Nat) :
  Xor'
    (@Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
        (@instHAdd.{0} Nat (@Distrib'.toAdd.{0} Nat Nat.instDistrib'))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
          inferInstance
          (@OfNat.ofNat.{0} Nat (nat_lit 2)
            (@instOfNatAtLeastTwo'.{0} Nat (nat_lit 2) inferInstance inferInstance)) k) 1)
      (2 * k))
    True := by grind
