/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean.Meta

/- See file `DiscrTree.lean` for the actual implementation and documentation. -/

namespace DiscrTree

inductive Key where
  | const : Name → Nat → Key
  | fvar  : FVarId → Nat → Key
  | lit   : Literal → Key
  | star  : Key
  | other : Key
  | arrow : Key
  | proj  : Name → Nat → Key
  deriving Inhabited, BEq, Repr

protected def Key.hash : Key → UInt64
  | Key.const n a => mixHash 5237 $ mixHash (hash n) (hash a)
  | Key.fvar n a  => mixHash 3541 $ mixHash (hash n) (hash a)
  | Key.lit v     => mixHash 1879 $ hash v
  | Key.star      => 7883
  | Key.other     => 2411
  | Key.arrow     => 17
  | Key.proj s i  => mixHash 11 $ mixHash (hash s) (hash i)

instance : Hashable Key := ⟨Key.hash⟩

inductive Trie (α : Type) where
  | node (vs : Array α) (children : Array (Key × Trie α)) : Trie α

end DiscrTree

open DiscrTree
open Std (PersistentHashMap)

structure DiscrTree (α : Type) where
  root : PersistentHashMap Key (Trie α) := {}

end Lean.Meta
