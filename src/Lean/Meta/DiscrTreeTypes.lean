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
(Imperfect) Discrimination tree key. See `DiscrTree`.
The parameter `simpleReduce` controls how aggressive the term is reduced.
-/
inductive Key (simpleReduce : Bool) where
  /-- A constant application with name `declName` and `arity` arguments. -/
  | const (declName : Name) (arity : Nat)
  /--
  Free variables (and arity). Thus, an entry in the discrimination tree
  may reference hypotheses from the local context.
  -/
  | fvar (fvarId : FVarId) (arity : Nat)
  /-- Literal. -/
  | lit (litVal : Literal)
  /--
  Star or wildcard. We use them to represent metavariables and terms
  we want to ignore. We ignore implicit arguments and proofs.
  -/
  | star
  /--
  Other terms. We use to represent other kinds of terms
  (e.g., nested lambda, forall, sort, etc).
  -/
  | other
  /-- Arrow (aka non dependent arrows). -/
  | arrow
  /-- Projection (applications). -/
  | proj (structName : Name) (projIdx : Nat) (arity : Nat)
  /--
  Ground terms.
  We use to implement the `ground p` pattern annotation.
  When the `DiscrTree` is trying to match a term `e` with key the `.ground`,
  it succeeds if `e` does not contain free or meta variables.
  Note that, in the pattern `ground p`, the term `p` is ignored.
  We can also view `ground` as a variant of `star` that matches all ground terms.
  -/
  | ground : Key simpleReduce
  deriving Inhabited, BEq, Repr

protected def Key.hash : Key s → UInt64
  | Key.const n a   => mixHash 5237 $ mixHash (hash n) (hash a)
  | Key.fvar n a    => mixHash 3541 $ mixHash (hash n) (hash a)
  | Key.lit v       => mixHash 1879 $ hash v
  | Key.star        => 7883
  | Key.other       => 2411
  | Key.arrow       => 17
  | Key.ground      => 11
  | Key.proj s i a  =>  mixHash (hash a) $ mixHash (hash s) (hash i)

instance : Hashable (Key s) := ⟨Key.hash⟩

/--
Discrimination tree trie. See `DiscrTree`.
-/
inductive Trie (α : Type) (simpleReduce : Bool) where
  | node (vs : Array α) (children : Array (Key simpleReduce × Trie α simpleReduce)) : Trie α simpleReduce

end DiscrTree

open DiscrTree

/--
Discrimination trees. It is an index from terms to values of type `α`.

If `simpleReduce := true`, then only simple reduction are performed while
indexing/retrieving terms. For example, `iota` reduction is not performed.

We use `simpleReduce := false` in the type class resolution module,
and `simpleReduce := true` in `simp`.

Motivations:
- In `simp`, we want to have `simp` theorem such as
```
@[simp] theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a := rfl
```
If we enable `iota`, then the lhs is reduced to `f a`.

- During type class resolution, we often want to reduce types using even `iota`.
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
structure DiscrTree (α : Type) (simpleReduce : Bool) where
  root : PersistentHashMap (Key simpleReduce) (Trie α simpleReduce) := {}

end Lean.Meta
