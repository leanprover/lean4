module
-- This is a companion file for `grind_indexmap.lean`,
-- showing how to construct the annotations needed for an automatic proof of
-- `theorem getElem_indices_lt`
-- (It should only differ from that file in the neighbourhood of that theorem.)

import Std.Data.HashMap
import Lean.LibrarySuggestions.Default

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

/--
An `IndexMap α β` is a map from keys of type `α` to values of type `β`,
which also maintains the insertion order of keys.

Internally `IndexMap` is implementented redundantly as a `HashMap` from keys to indices
(and hence the key type must be `Hashable`), along with `Array`s of keys and values.
These implementation details are private, and hidden from the user.
-/
structure IndexMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α), keys[i]? = some a ↔ indices[a]? = some i := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =]
private theorem size_keys : m.keys.size = m.size := size_keys' _

@[local grind =]
private theorem size_values : m.values.size = m.size := rfl

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β) (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[local grind _=_]
private theorem mem_indices {m : IndexMap α β} {a : α} :
    a ∈ m.indices ↔ a ∈ m := by rfl

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat := m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m := by get_elem_tactic) : Nat := m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β := m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat) (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

/-!
This section of the file contains a walkthrough showing how to construct a
`by grind` proof of `theorem getElem_indices_lt` below.
-/

example {h : a ∈ m} : m.indices[a] < m.size := by
  fail_if_success grind
  -- Fails: doesn't attempt to relate `m.indices[a]` with `m.indices[a]?`,
  -- so there's no hope of using `m.WF`.
  sorry

example {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  fail_if_success grind
  -- Fails:
  -- now we have an equivalence class `{some m.indices[a], m.indices[a]?, some m.indices[a]}`
  -- but there's nothing to trigger `IndexMap.WF`.
  sorry

example {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  have := m.WF m.indices[a]
  grind -- Succeeds! But we're sad that we had to write the `have` steps by hand.

-- Let's ask `grind` what it did using `grind?`:
example {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  have := m.WF m.indices[a]
  grind?

-- And then use the code action to expand `grind?` into a `grind =>` script:
example {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  have := m.WF m.indices[a]
  grind =>
    instantiate only [#41bd]
    instantiate only [= getElem?_neg]
    instantiate only [= size_keys]

-- We can query the internal `grind` state:
example {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  have := m.WF m.indices[a]
  grind =>
    instantiate only [#41bd]
    -- Display asserted facts
    show_asserted
    -- Display asserted facts with `generation > 0`
    show_asserted gen > 0
    -- Display propositions known to be `True`, containing `m`, and `generation > 0`
    show_true m && gen > 0
    -- Display equivalence classes with terms that contain `m`
    show_eqcs m
    instantiate only [= getElem?_neg]
    instantiate only [= size_keys]

-- Let's start adding `grind` annotations to make that proof more automatic.
-- We need `IndexMap.WF` to trigger automatically when it see `m.indices[a]?`.

-- First attempt:
/--
error: invalid pattern(s) for `WF`
  [@getElem? (HashMap #6 `[Nat] #4 #3) _ `[Nat] _ _ (@indices _ #5 _ _ #2) #0]
the following theorem parameters cannot be instantiated:
  i : Nat
-/
#guard_msgs in
local grind_pattern IndexMap.WF => self.indices[a]?

-- Second attempt:
section
local grind_pattern IndexMap.WF => self.indices[a]?, some i

example {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  -- have := m.WF m.indices[a] -- No longer needed!
  grind
end

-- Third attempt: we can also be lazy and use `grind _=_`,
-- which says "please make patterns out of both the LHS and RHS":
attribute [local grind _=_] IndexMap.WF

example {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind

-- What about the `have : m.indices[a]? = some m.indices[a]`?
-- We just need to make sure `getElem?_pos` is activated here.

-- We're considering activating this globally in https://github.com/leanprover/lean4/pull/11963
-- but right now it breaks too many of the proof scripts generated by `grind?`.
local grind_pattern getElem?_pos => c[i] where
  guard dom c i

private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  grind

grind_pattern getElem_indices_lt => m.indices[a]

@[reducible] -- This avoids needing boilerplate lemmas for the fields below, but may not be ideal.
instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.values[m.indices[a]'h]
  getElem? m a := m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a := m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys    := m.keys.set i a
      values  := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys    := m.keys.push a
      values  := m.values.push b }

instance : Singleton (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) :=
  ⟨fun _ => rfl⟩

-- This is not needed if we activate `grind_pattern getElem?_pos => c[i]` above.
@[local grind .]
private theorem WF' (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind

/--
Erase the key-value pair with the given key, moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m

/-! ### Verification theorems -/

@[grind =]
theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind +locals

@[grind =]
theorem getElem_insert (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind +locals

theorem findIdx_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.findIdx a h < m.size := by
  grind +locals

grind_pattern findIdx_lt => m.findIdx a h

@[grind =]
theorem findIdx_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind +locals

@[grind =]
theorem findIdx?_eq (m : IndexMap α β) (a : α) :
    m.findIdx? a = if h : a ∈ m then some (m.findIdx a h) else none := by
  grind +locals

@[grind =]
theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind +locals

omit [LawfulBEq α] [LawfulHashable α] in
@[grind =]
theorem getIdx?_eq (m : IndexMap α β) (i : Nat) :
    m.getIdx? i = if h : i < m.size then some (m.getIdx i h) else none := by
  grind +locals

end IndexMap
