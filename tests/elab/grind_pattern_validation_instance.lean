/-!
Test for `grind` pattern validation. It covers the case where
an instance is not tagged with the implicit instance binder.
This happens in declarations such as
```lean
ZeroMemClass.zero_mem {S : Type} {M : outParam Type} {inst1 : Zero M} {inst2 : SetLike S M}
  [self : @ZeroMemClass S M inst1 inst2] (s : S) : 0 ∈ s
```
-/

def Set (α : Type u) := α → Prop

/-- Membership in a set -/
protected def Set.Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

class SetLike (A : Type) (B : outParam Type) where
  protected coe : A → Set B
  protected coe_injective : Function.Injective coe

instance [SetLike A B]: CoeTC A (Set B) where coe := SetLike.coe

instance [SetLike A B] : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩

class ZeroMemClass (S : Type) (M : outParam Type) [Zero M] [SetLike S M] : Prop where
  zero_mem : ∀ s : S, (0 : M) ∈ s

class Ring (R : Type) extends Zero R

@[ext]
structure Subring (M : Type) [Ring M] where
  carrier : Set M
  zero_mem' : 0 ∈ carrier

instance {M} [Ring M] : SetLike (Subring M) M where
  coe := Subring.carrier
  coe_injective a b h := by ext; assumption

theorem Subring.zero_mem {M} [Ring M] (s : Subring M) : 0 ∈ s :=
  s.zero_mem'

grind_pattern ZeroMemClass.zero_mem => 0 ∈ s

instance {M} [Ring M] : ZeroMemClass (Subring M) M where
  zero_mem := Subring.zero_mem

example {R : Type} [Ring R] (S : Subring R) : 0 ∈ S := by
  grind

example {R : Type} [Ring R] (S : Subring R) : 0 ∈ S := by
  grind only [ZeroMemClass.zero_mem]

example {R : Type} [Ring R] (S : Subring R) : 0 ∈ S := by
  grind only [Subring.zero_mem]
