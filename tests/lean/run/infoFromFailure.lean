

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
info: [Meta.synthInstance] ❌️ Add String
  [Meta.synthInstance] new goal Add String
    [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toAdd]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toAdd to Add String
    [Meta.synthInstance.tryResolve] ✅️ Add String ≟ Add String
    [Meta.synthInstance] no instances for Lean.Grind.CommRing String
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
-- `foo` is overloaded, the case `A.foo` is discarded because we don't have an instance `[Add String]`.
-- However, we still want to see the trace since we used trace.Meta.synthInstance
#check foo "hello"

/--
info: [Meta.synthInstance] ❌️ Add Bool
  [Meta.synthInstance] new goal Add Bool
    [Meta.synthInstance.instances] #[@Lean.Grind.CommRing.toAdd]
  [Meta.synthInstance] ✅️ apply @Lean.Grind.CommRing.toAdd to Add Bool
    [Meta.synthInstance.tryResolve] ✅️ Add Bool ≟ Add Bool
    [Meta.synthInstance] no instances for Lean.Grind.CommRing Bool
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
theorem ex : foo true = (true, true) :=
rfl
