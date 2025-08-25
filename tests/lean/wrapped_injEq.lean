namespace Irreducible

@[irreducible] def WrappedNat (_n : Nat) := Nat

structure WithWrapped : Type :=
(n : Nat)
(m : WrappedNat n)

#check WithWrapped.mk.injEq

end Irreducible

namespace Semireducible

def WrappedNat (_n : Nat) := Nat

structure WithWrapped : Type :=
(n : Nat)
(m : WrappedNat n)

#check WithWrapped.mk.injEq

end Semireducible

namespace Reducible

abbrev WrappedNat (_n : Nat) := Nat

structure WithWrapped : Type :=
(n : Nat)
(m : WrappedNat n)

#check WithWrapped.mk.injEq

end Reducible
