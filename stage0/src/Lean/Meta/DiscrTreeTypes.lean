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
  deriving Inhabited, BEq

protected def Key.hash : Key → USize
  | Key.const n a => mixUSizeHash 5237 $ mixUSizeHash (hashUSize n) (hashUSize a)
  | Key.fvar n a  => mixUSizeHash 3541 $ mixUSizeHash (hashUSize n) (hashUSize a)
  | Key.lit v     => mixUSizeHash 1879 $ hashUSize v
  | Key.star      => 7883
  | Key.other     => 2411
  | Key.arrow     => 17

instance : HashableUSize Key := ⟨Key.hash⟩

inductive Trie (α : Type) where
  | node (vs : Array α) (children : Array (Key × Trie α)) : Trie α

end DiscrTree

open DiscrTree
open Std (PersistentHashMap)

structure DiscrTree (α : Type) where
  root : PersistentHashMap Key (Trie α) := {}

end Lean.Meta
