

def A.foo {α : Type} [Add α] (a : α) : α × α :=
(a, a + a)

def B.foo {α : Type} (a : α) : α × α :=
(a, a)

open A
open B

set_option trace.Meta.synthInstance true

/--
info: B.foo "hello" : String × String
---
trace: [Meta.synthInstance] ❌️ Add String
  [Meta.synthInstance] new goal Add String
    [Meta.synthInstance.instances] #[@Lean.Grind.AddCommMonoid.toAdd, @Lean.Grind.Semiring.toAdd]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Semiring.toAdd to Add String
    [Meta.synthInstance.tryResolve] ✅️ Add String ≟ Add String
    [Meta.synthInstance] new goal Lean.Grind.Semiring String
      [Meta.synthInstance.instances] #[@Lean.Grind.Ring.toSemiring, @Lean.Grind.CommSemiring.toSemiring]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommSemiring.toSemiring to Lean.Grind.Semiring String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Semiring String ≟ Lean.Grind.Semiring String
    [Meta.synthInstance] new goal Lean.Grind.CommSemiring String
      [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toCommSemiring]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toCommSemiring to Lean.Grind.CommSemiring String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.CommSemiring String ≟ Lean.Grind.CommSemiring String
    [Meta.synthInstance] new goal Lean.Grind.CommRing String
      [Meta.synthInstance.instances] #[@Lean.Grind.Field.toCommRing]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Field.toCommRing to Lean.Grind.CommRing String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.CommRing String ≟ Lean.Grind.CommRing String
    [Meta.synthInstance] no instances for Lean.Grind.Field String
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toSemiring to Lean.Grind.Semiring String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Semiring String ≟ Lean.Grind.Semiring String
    [Meta.synthInstance] new goal Lean.Grind.Ring String
      [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toRing]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toRing to Lean.Grind.Ring String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Ring String ≟ Lean.Grind.Ring String
  [Meta.synthInstance] ✅️ apply @Lean.Grind.AddCommMonoid.toAdd to Add String
    [Meta.synthInstance.tryResolve] ✅️ Add String ≟ Add String
    [Meta.synthInstance] new goal Lean.Grind.AddCommMonoid String
      [Meta.synthInstance.instances] #[@Lean.Grind.AddCommGroup.toAddCommMonoid, @Lean.Grind.NatModule.toAddCommMonoid]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.NatModule.toAddCommMonoid to Lean.Grind.AddCommMonoid String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommMonoid String ≟ Lean.Grind.AddCommMonoid String
    [Meta.synthInstance] new goal Lean.Grind.NatModule String
      [Meta.synthInstance.instances] #[@Lean.Grind.IntModule.toNatModule, @Lean.Grind.Semiring.toNatModule]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Semiring.toNatModule to Lean.Grind.NatModule String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.NatModule String ≟ Lean.Grind.NatModule String
  [Meta.synthInstance] ✅️ apply @Lean.Grind.IntModule.toNatModule to Lean.Grind.NatModule String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.NatModule String ≟ Lean.Grind.NatModule String
    [Meta.synthInstance] new goal Lean.Grind.IntModule String
      [Meta.synthInstance.instances] #[@Lean.Grind.Ring.toIntModule]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toIntModule to Lean.Grind.IntModule String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.IntModule String ≟ Lean.Grind.IntModule String
  [Meta.synthInstance] ✅️ apply @Lean.Grind.AddCommGroup.toAddCommMonoid to Lean.Grind.AddCommMonoid String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommMonoid String ≟ Lean.Grind.AddCommMonoid String
    [Meta.synthInstance] new goal Lean.Grind.AddCommGroup String
      [Meta.synthInstance.instances] #[@Lean.Grind.IntModule.toAddCommGroup, @Lean.Grind.Ring.toAddCommGroup]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toAddCommGroup to Lean.Grind.AddCommGroup String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommGroup String ≟ Lean.Grind.AddCommGroup String
  [Meta.synthInstance] ✅️ apply @Lean.Grind.IntModule.toAddCommGroup to Lean.Grind.AddCommGroup String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommGroup String ≟ Lean.Grind.AddCommGroup String
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
-- `foo` is overloaded, the case `A.foo` is discarded because we don't have an instance `[Add String]`.
-- However, we still want to see the trace since we used trace.Meta.synthInstance
#check foo "hello"

/--
trace: [Meta.synthInstance] ❌️ Add Bool
  [Meta.synthInstance] new goal Add Bool
    [Meta.synthInstance.instances] #[@Lean.Grind.AddCommMonoid.toAdd, @Lean.Grind.Semiring.toAdd]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Semiring.toAdd to Add Bool
    [Meta.synthInstance.tryResolve] ✅️ Add Bool ≟ Add Bool
    [Meta.synthInstance] new goal Lean.Grind.Semiring Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.Ring.toSemiring, @Lean.Grind.CommSemiring.toSemiring]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommSemiring.toSemiring to Lean.Grind.Semiring Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Semiring Bool ≟ Lean.Grind.Semiring Bool
    [Meta.synthInstance] new goal Lean.Grind.CommSemiring Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toCommSemiring]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toCommSemiring to Lean.Grind.CommSemiring Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.CommSemiring Bool ≟ Lean.Grind.CommSemiring Bool
    [Meta.synthInstance] new goal Lean.Grind.CommRing Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.Field.toCommRing]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Field.toCommRing to Lean.Grind.CommRing Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.CommRing Bool ≟ Lean.Grind.CommRing Bool
    [Meta.synthInstance] no instances for Lean.Grind.Field Bool
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toSemiring to Lean.Grind.Semiring Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Semiring Bool ≟ Lean.Grind.Semiring Bool
    [Meta.synthInstance] new goal Lean.Grind.Ring Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toRing]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toRing to Lean.Grind.Ring Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Ring Bool ≟ Lean.Grind.Ring Bool
  [Meta.synthInstance] ✅️ apply @Lean.Grind.AddCommMonoid.toAdd to Add Bool
    [Meta.synthInstance.tryResolve] ✅️ Add Bool ≟ Add Bool
    [Meta.synthInstance] new goal Lean.Grind.AddCommMonoid Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.AddCommGroup.toAddCommMonoid, @Lean.Grind.NatModule.toAddCommMonoid]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.NatModule.toAddCommMonoid to Lean.Grind.AddCommMonoid Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommMonoid Bool ≟ Lean.Grind.AddCommMonoid Bool
    [Meta.synthInstance] new goal Lean.Grind.NatModule Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.IntModule.toNatModule, @Lean.Grind.Semiring.toNatModule]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Semiring.toNatModule to Lean.Grind.NatModule Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.NatModule Bool ≟ Lean.Grind.NatModule Bool
  [Meta.synthInstance] ✅️ apply @Lean.Grind.IntModule.toNatModule to Lean.Grind.NatModule Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.NatModule Bool ≟ Lean.Grind.NatModule Bool
    [Meta.synthInstance] new goal Lean.Grind.IntModule Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.Ring.toIntModule]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toIntModule to Lean.Grind.IntModule Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.IntModule Bool ≟ Lean.Grind.IntModule Bool
  [Meta.synthInstance] ✅️ apply @Lean.Grind.AddCommGroup.toAddCommMonoid to Lean.Grind.AddCommMonoid Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommMonoid Bool ≟ Lean.Grind.AddCommMonoid Bool
    [Meta.synthInstance] new goal Lean.Grind.AddCommGroup Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.IntModule.toAddCommGroup, @Lean.Grind.Ring.toAddCommGroup]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toAddCommGroup to Lean.Grind.AddCommGroup Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommGroup Bool ≟ Lean.Grind.AddCommGroup Bool
  [Meta.synthInstance] ✅️ apply @Lean.Grind.IntModule.toAddCommGroup to Lean.Grind.AddCommGroup Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.AddCommGroup Bool ≟ Lean.Grind.AddCommGroup Bool
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
theorem ex : foo true = (true, true) :=
rfl
