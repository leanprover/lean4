class A (α : Type) where
  x : α -- To make sure we have nontrivial equalities

class B (α : Type) extends A α

class C (α : Type) [A α] where
  prop : False

class D (α : Type) [A α] extends C α

instance (α : Type) [B α] [C α] : D α where

section

-- Defining two separate instances
instance : A (Fin 2) where
  x := 0

instance : B (Fin 2) where
  x := 0

-- Make sure the two instances are equal, modulo instance transparency.
example : B.toA = instAFinOfNatNat := by
  fail_if_success with_reducible rfl
  with_reducible_and_instances rfl

set_option trace.Meta.synthInstance true
/--
trace: [Meta.synthInstance] ✅️ A (Fin 2)
  [Meta.synthInstance] new goal A (Fin 2)
    [Meta.synthInstance.instances] #[@B.toA, instAFinOfNatNat]
  [Meta.synthInstance] ✅️ apply instAFinOfNatNat to A (Fin 2)
    [Meta.synthInstance.tryResolve] ✅️ A (Fin 2) ≟ A (Fin 2)
    [Meta.synthInstance.answer] ✅️ A (Fin 2)
  [Meta.synthInstance] result instAFinOfNatNat
---
trace: [Meta.synthInstance] ✅️ OfNat Nat 2
  [Meta.synthInstance] new goal OfNat Nat 2
    [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.ofNat, instOfNatNat]
  [Meta.synthInstance] ✅️ apply instOfNatNat to OfNat Nat 2
    [Meta.synthInstance.tryResolve] ✅️ OfNat Nat 2 ≟ OfNat Nat 2
    [Meta.synthInstance.answer] ✅️ OfNat Nat 2
  [Meta.synthInstance] result instOfNatNat 2
---
trace: [Meta.synthInstance] ❌️ C (Fin 2)
  [Meta.synthInstance] new goal C (Fin 2)
    [Meta.synthInstance.instances] #[@D.toC]
  [Meta.synthInstance] ✅️ apply @D.toC to C (Fin 2)
    [Meta.synthInstance.tryResolve] ✅️ C (Fin 2) ≟ C (Fin 2)
    [Meta.synthInstance] new goal D (Fin 2)
      [Meta.synthInstance.instances] #[instDOfC]
  [Meta.synthInstance] ✅️ apply instDOfC to D (Fin 2)
    [Meta.synthInstance.tryResolve] ✅️ D (Fin 2) ≟ D (Fin 2)
      [Meta.synthInstance] ✅️ B (Fin 2)
        [Meta.synthInstance] new goal B (Fin 2)
          [Meta.synthInstance.instances] #[instBFinOfNatNat]
        [Meta.synthInstance] ✅️ apply instBFinOfNatNat to B (Fin 2)
          [Meta.synthInstance.tryResolve] ✅️ B (Fin 2) ≟ B (Fin 2)
          [Meta.synthInstance.answer] ✅️ B (Fin 2)
        [Meta.synthInstance] result instBFinOfNatNat
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
example : True := by
  fail_if_success have : C (Fin 2) := inferInstance
  trivial

end


section

-- Defining the instance and a shortcut (as an abbrev)
instance : B (Fin 3) where
  x := 0

@[instance] abbrev instAFinThree : A (Fin 3) := inferInstance

-- Now they are really reducibly defeq!
example : B.toA = instAFinThree := by
  with_reducible rfl

set_option trace.Meta.synthInstance true
/--
trace: [Meta.synthInstance] ✅️ A (Fin 3)
  [Meta.synthInstance] new goal A (Fin 3)
    [Meta.synthInstance.instances] #[@B.toA, instAFinThree]
  [Meta.synthInstance] ✅️ apply instAFinThree to A (Fin 3)
    [Meta.synthInstance.tryResolve] ✅️ A (Fin 3) ≟ A (Fin 3)
    [Meta.synthInstance.answer] ✅️ A (Fin 3)
  [Meta.synthInstance] result instAFinThree
---
trace: [Meta.synthInstance] ✅️ OfNat Nat 3
  [Meta.synthInstance] new goal OfNat Nat 3
    [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.ofNat, instOfNatNat]
  [Meta.synthInstance] ✅️ apply instOfNatNat to OfNat Nat 3
    [Meta.synthInstance.tryResolve] ✅️ OfNat Nat 3 ≟ OfNat Nat 3
    [Meta.synthInstance.answer] ✅️ OfNat Nat 3
  [Meta.synthInstance] result instOfNatNat 3
---
trace: [Meta.synthInstance] ❌️ C (Fin 3)
  [Meta.synthInstance] new goal C (Fin 3)
    [Meta.synthInstance.instances] #[@D.toC]
  [Meta.synthInstance] ✅️ apply @D.toC to C (Fin 3)
    [Meta.synthInstance.tryResolve] ✅️ C (Fin 3) ≟ C (Fin 3)
    [Meta.synthInstance] new goal D (Fin 3)
      [Meta.synthInstance.instances] #[instDOfC]
  [Meta.synthInstance] ✅️ apply instDOfC to D (Fin 3)
    [Meta.synthInstance.tryResolve] ✅️ D (Fin 3) ≟ D (Fin 3)
      [Meta.synthInstance] ✅️ B (Fin 3)
        [Meta.synthInstance] new goal B (Fin 3)
          [Meta.synthInstance.instances] #[instBFinOfNatNat_1]
        [Meta.synthInstance] ✅️ apply instBFinOfNatNat_1 to B (Fin 3)
          [Meta.synthInstance.tryResolve] ✅️ B (Fin 3) ≟ B (Fin 3)
          [Meta.synthInstance.answer] ✅️ B (Fin 3)
        [Meta.synthInstance] result instBFinOfNatNat_1
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
example : True := by
  fail_if_success have : C (Fin 3) := inferInstance
  trivial

end
