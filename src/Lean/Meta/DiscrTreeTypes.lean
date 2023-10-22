/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean.Meta

/-! See file `DiscrTree.lean` for the actual implementation and documentation. -/

namespace DiscrTree
/--
Discrimination tree key. See `DiscrTree`
-/
inductive Key where
  | const : Name → Nat → Key
  | fvar  : FVarId → Nat → Key
  | lit   : Literal → Key
  | star  : Key
  | other : Key
  | arrow : Key
  | proj  : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr

protected def Key.hash : Key → UInt64
  | .const n a   => mixHash 5237 $ mixHash (hash n) (hash a)
  | .fvar n a    => mixHash 3541 $ mixHash (hash n) (hash a)
  | .lit v       => mixHash 1879 $ hash v
  | .star        => 7883
  | .other       => 2411
  | .arrow       => 17
  | .proj s i a  =>  mixHash (hash a) $ mixHash (hash s) (hash i)

instance : Hashable Key := ⟨Key.hash⟩

/--
Discrimination tree trie. See `DiscrTree`.
-/
inductive Trie (α : Type) where
  | node (vs : Array α) (children : Array (Key × Trie α)) : Trie α

end DiscrTree

open DiscrTree

/-!
Notes regarding term reduction at the `DiscrTree` module.

- In `simp`, we want to have `simp` theorem such as
```
@[simp] theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a := rfl
```
If we enable `iota`, then the lhs is reduced to `f a`.
Note that when retrieving terms, we may also disable `beta` and `zeta` reduction.
See issue https://github.com/leanprover/lean4/issues/2669

- During type class resolution, we often want to reduce types using even `iota` and projection reductionn.
Example:
```
inductive Ty where
  | int
  | bool

@[reducible] def Ty.interp (ty : Ty) : Type :=
  Ty.casesOn (motive := fun _ => Type) ty Int Bool

def test {a b c : Ty} (f : a.interp → b.interp → c.interp) (x : a.interp) (y : b.interp) : c.interp :=
  f x y

def f (a b : Ty.bool.interp) : Ty.bool.interp :=
  -- We want to synthesize `BEq Ty.bool.interp` here, and it will fail
  -- if we do not reduce `Ty.bool.interp` to `Bool`.
  test (.==.) a b
```
-/

/--
Discrimination trees. It is an index from terms to values of type `α`.
-/
structure DiscrTree (α : Type) where
  root : PersistentHashMap Key (Trie α) := {}

end Lean.Meta
