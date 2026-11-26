module

public import Lean.ConstTrie

/-!
Verifies the lookup logic of the per-module constant prefix tries (`Lean.ConstTrie`): the binary
search over hash-sorted children (`findChildIdx?`), lookup via `ConstTrie.find?` in well-formed
tries, and that `ConstTrie.ofArrays` builds a well-formed trie whose `find?` and `foldlM` agree with
its input. Furthermore, looking up a name in the lazily merged `ImportedConsts` of several module
tries (`ImportedConsts.mergeModuleTreesLazy`) via `ImportedConsts.findEntry?` agrees with the
lookups in the individual tries.
-/

namespace ConstTrieSpec
open Lean Lean.ConstTrie

/-- The entries of a trie in `foldlM` order. -/
public def entries : ConstTrie α → List (Name × α)
  | .leaf k v => [(k, v)]
  | .inner _ cs => cs.toList.flatMap entries
  | .node k v cs => (k, v) :: cs.toList.flatMap entries
decreasing_by
  all_goals
    rename_i c hc
    have := List.sizeOf_lt_of_mem hc
    cases cs; simp_all; omega

/--
`ofArrays names vals` maps `n` to the value paired with its last occurrence among the first
`min names.size vals.size` names.
-/
public theorem find?_ofArrays (names : Array Name) (vals : Array α) (n : Name) (v : α) :
    (ofArrays names vals).find? n = some v ↔ ∃ j, ∃ h₁ : j < names.size, ∃ h₂ : j < vals.size,
      names[j] = n ∧ vals[j] = v ∧
      ∀ j' (h₁' : j' < names.size), j < j' → j' < vals.size → names[j'] ≠ n

public theorem find?_ofArrays_of_distinct (names : Array Name) (vals : Array α)
    (hsize : names.size = vals.size)
    (distinct : ∀ i j (hi : i < names.size) (hj : j < names.size), names[i] = names[j] → i = j)
    (n : Name) (v : α) :
    (ofArrays names vals).find? n = some v ↔
      ∃ i, ∃ h : i < names.size, names[i] = n ∧ vals[i]'(hsize ▸ h) = v

public theorem find?_ofArrays_getElem (names : Array Name) (vals : Array α)
    (hsize : names.size = vals.size)
    (distinct : ∀ i j (hi : i < names.size) (hj : j < names.size), names[i] = names[j] → i = j)
    (i : Nat) (h : i < names.size) :
    (ofArrays names vals).find? names[i] = some (vals[i]'(hsize ▸ h))

public theorem find?_ofArrays_eq_none (names : Array Name) (vals : Array α) (n : Name) (h : n ∉ names) :
    (ofArrays names vals).find? n = none

public theorem foldlM_eq_entries [Monad m] [LawfulMonad m] (t : ConstTrie α) (f : σ → Name → α → m σ)
    (init : σ) : t.foldlM f init = (entries t).foldlM (fun s p => f s p.1 p.2) init

public theorem entries_ofArrays_perm (names : Array Name) (vals : Array α)
    (hsize : names.size = vals.size)
    (distinct : ∀ i j (hi : i < names.size) (hj : j < names.size), names[i] = names[j] → i = j) :
    (entries (ofArrays names vals)).Perm (names.zip vals).toList

end ConstTrieSpec
