section algebra_hierarchy_classes_to_comm_ring

class Semiring (α : Type) extends Add α, Mul α, Zero α, One α

class CommSemiring (R : Type) extends Semiring R

class Ring (R : Type) extends Semiring R

class CommRing (R : Type) extends Ring R

end algebra_hierarchy_classes_to_comm_ring

section algebra_hierarchy_morphisms

class FunLike (F : Type) (α : outParam Type) (β : outParam <| α → Type) where
  coe : F → ∀ a : α, β a

instance (priority := 100) FunLike.insthasCoeToFun {F α : Type} {β : α → Type} [FunLike F α β] : CoeFun F fun _ ↦ ∀ a : α, β a where coe := FunLike.coe

structure ZeroHom (M N : Type) [Zero M] [Zero N] where
  toFun : M → N

class ZeroHomClass (F : Type) (M N : outParam Type) [Zero M] [Zero N]
  extends FunLike F M fun _ => N where

structure OneHom (M : Type) (N : Type) [One M] [One N] where
  toFun : M → N

class OneHomClass (F : Type) (M N : outParam Type) [One M] [One N]
  extends FunLike F M fun _ => N where

structure AddHom (M : Type) (N : Type) [Add M] [Add N] where
  toFun : M → N

class AddHomClass (F : Type) (M N : outParam Type) [Add M] [Add N]
  extends FunLike F M fun _ => N where

structure MulHom (M : Type) (N : Type) [Mul M] [Mul N] where
  toFun : M → N

infixr:25 " →ₙ* " => MulHom

class MulHomClass (F : Type) (M N : outParam Type) [Mul M] [Mul N]
  extends FunLike F M fun _ => N where

structure AddMonoidHom (M : Type) (N : Type) [Add M] [Zero M] [Add N] [Zero N] extends
  ZeroHom M N, AddHom M N

infixr:25 " →+ " => AddMonoidHom

class AddMonoidHomClass (F : Type) (M N : outParam Type) [Add M] [Zero M] [Add N] [Zero N]
  extends AddHomClass F M N, ZeroHomClass F M N

structure MonoidHom (M : Type) (N : Type) [Mul M] [One M] [Mul N] [One N] extends
  OneHom M N, M →ₙ* N

infixr:25 " →* " => MonoidHom

class MonoidHomClass (F : Type) (M N : outParam Type) [Mul M] [One M] [Mul N] [One N]
  extends MulHomClass F M N, OneHomClass F M N

structure MonoidWithZeroHom (M : Type) (N : Type)
  [Mul M] [Zero M] [One M] [Mul N] [Zero N] [One N] extends ZeroHom M N, MonoidHom M N

infixr:25 " →*₀ " => MonoidWithZeroHom

structure NonUnitalRingHom (α β : Type) [Add α] [Zero α] [Mul α]
  [Add β] [Zero β] [Mul β] extends α →ₙ* β, α →+ β

class MonoidWithZeroHomClass (F : Type) (M N : outParam Type) [Mul M] [Zero M] [One M]
  [Mul N] [Zero N] [One N] extends MonoidHomClass F M N, ZeroHomClass F M N

infixr:25 " →ₙ+* " => NonUnitalRingHom

structure RingHom (α : Type) (β : Type) [Semiring α] [Semiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β

infixr:25 " →+* " => RingHom

class RingHomClass (F : Type) (α β : outParam Type) [Semiring α]
  [Semiring β] extends MonoidHomClass F α β, AddMonoidHomClass F α β,
  MonoidWithZeroHomClass F α β

instance instRingHomClass (R S : Type) [Semiring R] [Semiring S] :
    RingHomClass (R →+* S) R S where
  coe f := f.toFun

-- this is needed to create the troublesome instance `Algebra.instid`
def RingHom.id (α : Type) [Semiring α] : α →+* α := by
  refine { toFun := _root_.id.. }

end algebra_hierarchy_morphisms

section HSMul_stuff

class HSMul (α : Type) (β : Type) (γ : outParam Type) where
  hSMul : α → β → γ

class SMul (M : Type) (α : Type) where
  smul : M → α → α

infixr:73 " • " => HSMul.hSMul

instance instHSMul {α β : Type} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

-- note that the function `SMulZeroClass.toSMul` is what disrupts `simp` later
class SMulZeroClass (M A : Type) extends SMul M A where

class SMulWithZero (R M : Type) extends SMulZeroClass R M where

instance MulZeroClass.toSMulWithZero (R : Type) [Mul R] [Zero R] : SMulWithZero R R where
  smul := (· * ·)

end HSMul_stuff

section Algebra_stuff

class Algebra (R A : Type) [CommSemiring R] [Semiring A] extends SMul R A,
  R →+* A where

-- needed for troublesome `Algebra.instid`
def RingHom.toAlgebra' {R S : Type} [CommSemiring R] [Semiring S] (i : R →+* S)
    : Algebra R S where
  smul c x := i c * x
  toRingHom := i

-- needed for troublesome `Algebra.instid`
def RingHom.toAlgebra {R S : Type} [CommSemiring R] [CommSemiring S] (i : R →+* S) : Algebra R S :=
  i.toAlgebra'

-- comment this out and the failing `simp` works
instance Algebra.instid (R : Type) [CommSemiring R] : Algebra R R :=
  (RingHom.id R).toAlgebra

end Algebra_stuff

namespace Pi_stuff

instance instSMul {I : Type} {f : I → Type} {M : Type} [∀ i, SMul M <| f i] : SMul M (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

end Pi_stuff

section oliver_example

theorem Pi.smul_apply {I : Type} {f : I → Type} {β : Type} [∀ i, SMul β (f i)] (x : ∀ i, f i) (b : β) (i : I) : (b • x) i = b • (x i) :=
  rfl

instance (R : Type) [CommRing R] : CommSemiring R where

-- `foo` and `bar` are defeq
example {R : Type} [CommRing R] : True :=
  let foo := (Algebra.instid R).toSMul
  let bar : SMul R R := SMulZeroClass.toSMul
  have : foo = bar := rfl -- they are defeq
  trivial

-- this proof works fine
example {α R : Type} [CommRing R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  simp only [Pi.smul_apply]

-- At issue #2461, the presence of `bar` broke this proof
example {α R : Type} [CommRing R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  let bar : SMul R R := SMulZeroClass.toSMul
  simp only [Pi.smul_apply]

example {α R : Type} [CommRing R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  simp only [Pi.smul_apply]

-- At issue #2461, the proof was fixed when we using `Ring` instead of `CommRing`.
example {α R : Type} [Ring R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  let bar : SMul R R := SMulZeroClass.toSMul
  simp only [Pi.smul_apply]

example {α R : Type} [Ring R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  simp only [Pi.smul_apply]

end oliver_example
