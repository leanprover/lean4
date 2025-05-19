

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
    [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.toAdd, @Lean.Grind.NatModule.toAdd, @Lean.Grind.IntModule.toAdd]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.IntModule.toAdd to Add String
    [Meta.synthInstance.tryResolve] ✅️ Add String ≟ Add String
    [Meta.synthInstance] new goal Lean.Grind.IntModule String
      [Meta.synthInstance.instances] #[@Lean.Grind.RatModule.toIntModule]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.RatModule.toIntModule to Lean.Grind.IntModule String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.IntModule String ≟ Lean.Grind.IntModule String
    [Meta.synthInstance] no instances for Lean.Grind.RatModule String
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.NatModule.toAdd to Add String
    [Meta.synthInstance.tryResolve] ✅️ Add String ≟ Add String
    [Meta.synthInstance] new goal Lean.Grind.NatModule String
      [Meta.synthInstance.instances] #[Lean.Grind.IntModule.toNatModule]
  [Meta.synthInstance] ✅️ apply Lean.Grind.IntModule.toNatModule to Lean.Grind.NatModule String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.NatModule String ≟ Lean.Grind.NatModule String
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
    [Meta.synthInstance] no instances for Lean.Grind.CommRing String
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toSemiring to Lean.Grind.Semiring String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Semiring String ≟ Lean.Grind.Semiring String
    [Meta.synthInstance] new goal Lean.Grind.Ring String
      [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toRing]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toRing to Lean.Grind.Ring String
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Ring String ≟ Lean.Grind.Ring String
    [Meta.synthInstance] no instances for Lean.Grind.CommRing String
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
-- `foo` is overloaded, the case `A.foo` is discarded because we don't have an instance `[Add String]`.
-- However, we still want to see the trace since we used trace.Meta.synthInstance
#check foo "hello"

/--
trace: [Meta.synthInstance] ❌️ Add Bool
  [Meta.synthInstance] new goal Add Bool
    [Meta.synthInstance.instances] #[@Lean.Grind.Semiring.toAdd]
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
    [Meta.synthInstance] no instances for Lean.Grind.CommRing Bool
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.Ring.toSemiring to Lean.Grind.Semiring Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Semiring Bool ≟ Lean.Grind.Semiring Bool
    [Meta.synthInstance] new goal Lean.Grind.Ring Bool
      [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toRing]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toRing to Lean.Grind.Ring Bool
    [Meta.synthInstance.tryResolve] ✅️ Lean.Grind.Ring Bool ≟ Lean.Grind.Ring Bool
    [Meta.synthInstance] no instances for Lean.Grind.CommRing Bool
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
theorem ex : foo true = (true, true) :=
rfl
