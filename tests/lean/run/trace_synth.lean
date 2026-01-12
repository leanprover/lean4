class Foo (s : String) : Type where
instance : Foo "one" where
instance [Foo "three"] : Foo "two" where

def f (s : String) [Foo s] := ()

/-- info: () -/
#guard_msgs in
#eval f "one"

/--
error: failed to synthesize instance of type class
  Foo "two"

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval f "two"

/--
error: failed to synthesize instance of type class
  Foo "two"
---
trace: [Meta.synthInstance] ❌️ Foo "two"
  [Meta.synthInstance] new goal Foo "two"
    [Meta.synthInstance.instances] #[@instFoo_1]
  [Meta.synthInstance] ✅️ apply @instFoo_1 to Foo "two"
    [Meta.synthInstance.tryResolve] ✅️ Foo "two" ≟ Foo "two"
    [Meta.synthInstance] no instances for Foo "three"
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
[Meta.synthInstance] ❌️ Foo "two"
  [Meta.synthInstance] result <not-available> (cached)
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
#eval f "two"

/--
error: failed to synthesize instance of type class
  Foo "three"
---
trace: [Meta.synthInstance] ❌️ Foo "three"
  [Meta.synthInstance] no instances for Foo "three"
    [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
[Meta.synthInstance] ❌️ Foo "three"
  [Meta.synthInstance] result <not-available> (cached)
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
#eval f "three"
