import Lean.Elab.Command

/-!
Tests that a type class resolution cache entry depends on the options the search read
(`Lean.getRecordedOption`) and on no others.
-/

open Lean Meta Elab Command

class Boo (α : Type) where

instance : Boo Nat := ⟨⟩

/--
trace: [Meta.synthInstance.cache] new: Boo Nat
[Meta.synthInstance.cache] cached: Boo Nat
[Meta.synthInstance.cache] cached: Boo Nat
[Meta.synthInstance.cache] new: Boo Nat
-/
#guard_msgs in
run_cmd liftTermElabM do
  let ty := mkApp (mkConst ``Boo) (mkConst ``Nat)
  let query : TermElabM Unit :=
    withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
      discard <| synthInstance? ty
  query
  query
  -- An option the search does not read does not partition the cache.
  withOptions (·.setBool `pp.universes true) do query
  -- `backward.synthInstance.canonInstances` is read by the search, so it does.
  withOptions (·.setBool `backward.synthInstance.canonInstances false) do query

class Foo (α : Type) where val : α
instance : Foo Nat := ⟨0⟩
instance [Foo α] : Foo (List α) := ⟨[Foo.val]⟩

abbrev T := Foo (List (List (List Nat)))

-- `synthInstance.maxSize` decides whether this instance can be built at all. Both searches run in
-- one elaboration and so share the cache; if the failure under the small limit were served back
-- under the large one, the second search would report no instance where one exists.
/--
error: failed to synthesize instance of type class
  T

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : T × T :=
  (set_option synthInstance.maxSize 1 in inferInstance,
   set_option synthInstance.maxSize 128 in inferInstance)
