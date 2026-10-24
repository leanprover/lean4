namespace SMI

def f (n : Nat) : Nat := n + 1
def p (n : Nat) : Nat := n
def q (n : Nat) : Nat := n

@[simp] theorem f_zero : f 0 = 1 := rfl
@[simp] theorem f_f (n : Nat) : f (f n) = n + 2 := rfl
@[simp] theorem p_q (n : Nat) : p n = q n := rfl
@[simp] def h (n : Nat) : Nat := n * 1

theorem f_two : f 2 = 3 := rfl

namespace Sc
attribute [scoped simp] f_two
end Sc

class C (α : Type) where
  c : Nat

instance instCNat : C Nat := ⟨1⟩
instance (priority := low) instCNat2 : C Nat := ⟨2⟩
def instCInt : C Int := ⟨3⟩

namespace Sc
scoped instance instCString : C String := ⟨4⟩
end Sc

end SMI
