/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.System.IO
public import Lean.Data.LBool
public import Lean.Data.PersistentHashMap

public section

namespace Lean

/--
Equality for cache keys with a work budget. `.undef` means the comparison exhausted its budget.
The comparison may break referential transparency by depending on pointer sharing, so it runs
in `BaseIO`. A definite result must agree with the key's intended equality.
-/
class BudgetedBEq (α : Type u) where
  beq : α → α → USize → BaseIO LBool

/--
A persistent cache storing one candidate per full hash. Insertion replaces both the key and value
for that hash. Lookup verifies the candidate with budgeted equality and evicts it on exhaustion.
Hash retrieval must take constant time; structural key equality is never used by the backing map.
-/
structure BudgetedCache (α : Type u) (β : Type v) [Hashable α] where
  private map : @PersistentHashMap α β ⟨fun a b => hash a == hash b⟩ _ :=
    @PersistentHashMap.empty α β ⟨fun a b => hash a == hash b⟩ _
  deriving Inhabited

namespace BudgetedCache

variable {α : Type u} {β : Type v} [Hashable α]

instance : EmptyCollection (BudgetedCache α β) := ⟨default⟩

@[inline] def insert (c : BudgetedCache α β) (key : α) (value : β) : BudgetedCache α β :=
  { map := c.map.insert key value }

/--
Finds a cached value with the given comparison budget, as interpreted by `BudgetedBEq`.
On exhaustion, calls `onEvict` with the cache after erasing the candidate. The caller
must retain this update. Hits, absent hashes, and definite inequality do not call `onEvict`.
-/
@[inline] def find? {β : Type} [BudgetedBEq α] {m : Type → Type w} [Monad m] [MonadLiftT BaseIO m]
    (c : BudgetedCache α β) (key : α) (onEvict : BudgetedCache α β → m Unit)
    (budget : USize := 64) : m (Option β) := do
  let some (stored, value) := c.map.findEntry? key | return none
  match ← BudgetedBEq.beq key stored budget with
  | .true => return some value
  | .false => return none
  | .undef =>
    onEvict { map := c.map.erase key }
    return none

end BudgetedCache
end Lean
