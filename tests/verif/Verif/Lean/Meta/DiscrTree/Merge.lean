module

public import Lean.Meta.DiscrTree.Basic
import all Lean.Expr
import all Lean.Meta.DiscrTree.Types

/-!
Verifies that merging per-module discrimination trees (`DiscrTree.ofModuleRoots` applied to the
`DiscrTree.moduleRootsOf` of each module) agrees with inserting the entries of all modules in module
order with `DiscrTree.insertKeyValue`: forcing all `lazy` nodes of the trie under any root key gives
exactly the trie under this key after sequential insertion (`ofModuleRoots_spec`). Both sides are
characterized by the relation `Den` between entries and tries: `insertAux_den` for sequential
insertion and `mergeTries_spec` for the merge.

`==` on values must be symmetric and transitive: the merge deduplicates the values of a module
before folding them into those of earlier modules, which loses values when `==` is not transitive
(see the example at the end). As the operations of `PersistentHashMap` are `partial`,
`ofModuleRoots_spec` assumes their lookup laws (`MapLaws`).
-/

open Lean Meta DiscrTree

namespace DiscrTreeMergeSpec
variable {α β γ : Type}

deriving instance ReflBEq, LawfulBEq for Lean.Literal
deriving instance ReflBEq, LawfulBEq for Lean.FVarId
deriving instance ReflBEq, LawfulBEq for Key

/--
The lookup laws of `PersistentHashMap` for `Key`. Its operations are implemented by `partial`
functions, so these laws cannot be proved here and are assumed instead.
-/
public structure MapLaws (β : Type) : Prop where
  find?_empty : ∀ k : Key, ({} : PersistentHashMap Key β).find? k = none
  find?_insert : ∀ (m : PersistentHashMap Key β) (k : Key) (v : β) (k' : Key),
    (m.insert k v).find? k' = if k == k' then some v else m.find? k'
  find?_alter : ∀ (m : PersistentHashMap Key β) (k : Key) (f : Option β → Option β) (k' : Key),
    (m.alter k f).find? k' = if k == k' then f (m.find? k) else m.find? k'

/-- `Forces t r`: forcing all `lazy` nodes of `t` terminates with `r`. -/
public inductive Forces : Trie α → Trie α → Prop
  | lazy {t : Thunk (Trie α)} {r : Trie α} : Forces t.get r → Forces (.lazy t) r
  | chain {k : Key} {c r : Trie α} : Forces c r → Forces (.chain k c) (.chain k r)
  | node {vs : Array α} {cs cs' : Array (Key × Trie α)} :
      cs.toList.map (·.1) = cs'.toList.map (·.1) →
      (∀ p ∈ cs.toList.zip cs'.toList, Forces p.1.2 p.2.2) → Forces (.node vs cs) (.node vs cs')
  | suffix {ks : Array Key} {i : Nat} {v : α} : Forces (.suffix ks i v) (.suffix ks i v)

section
variable [BEq α] [PartialEquivBEq α]

/-- Inserts the entries of a module in order. -/
public def insertModule (d : DiscrTree α) (es : Array (Array Key × α)) : DiscrTree α :=
  es.foldl (fun d e => d.insertKeyValue e.1 e.2) d

/--
After forcing all `lazy` nodes, the trie under each root key of the merged per-module trees is the
one under this key after inserting the entries of all modules in order.
-/
public theorem ofModuleRoots_spec (laws : MapLaws (Trie α)) (mods : Array (Array (Array Key × α)))
    (hne : ∀ es ∈ mods, ∀ e ∈ es, 0 < e.1.size) (k : Key) :
    Option.Rel Forces ((ofModuleRoots (mods.map moduleRootsOf)).root.find? k)
      ((mods.foldl insertModule {}).root.find? k)

end

end DiscrTreeMergeSpec
