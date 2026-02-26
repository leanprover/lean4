import Lean.Elab.Term

/-!
# Turán's theorem
-/

set_option warn.sorry false

section Mathlib.Tactic.TypeStar

open Lean

elab "Sort*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort u)

elab "Type*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort (.succ u))

end Mathlib.Tactic.TypeStar

section Mathlib.Data.Set.Defs

universe u
variable {α : Type u}

/-- A set is a collection of elements of some type `α`.

Although `Set` is defined as `α → Prop`, this is an implementation detail which should not be
relied on. Instead, `setOf` and membership of a set (`∈`) should be used to convert between sets
and predicates.
-/
def Set (α : Type u) := α → Prop

/-- Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}` -/
def setOf {α : Type u} (p : α → Prop) : Set α :=
  p

namespace Set

/-- Membership in a set -/
protected def Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

end Set

end Mathlib.Data.Set.Defs

section Mathlib.Order.Defs.Unbundled

variable {α : Sort*} (r : α → α → Prop)

/-- `IsSymm` as a definition, suitable for use in proofs. -/
def Symmetric := ∀ ⦃x y⦄, r x y → r y x

end Mathlib.Order.Defs.Unbundled

section Mathlib.Data.List.Defs

namespace List

variable {α : Type*}

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns both `a` and proofs
of `a ∈ l` and `p a`. -/
def chooseX : ∀ l : List α, ∀ _ : ∃ a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a }
  | [], hp => False.elim (Exists.elim hp fun _ h => not_mem_nil h.left)
  | l :: ls, hp =>
    if pl : p l then ⟨l, ⟨mem_cons.mpr <| Or.inl rfl, pl⟩⟩
    else
      -- pattern matching on `hx` too makes this not reducible!
      let ⟨a, ha⟩ :=
        chooseX ls
          (hp.imp fun _ ⟨o, h₂⟩ => ⟨(mem_cons.mp o).resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
      ⟨a, mem_cons.mpr <| Or.inr ha.1, ha.2⟩

end Choose

end List

end Mathlib.Data.List.Defs

section Mathlib.Data.Set.CoeSort

namespace Set

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Given the set `s`, `Elem s` is the `Type` of element of `s`.

It is currently an abbreviation so that instance coming from `Subtype` are available.
If you're interested in making it a `def`, as it probably should be,
you'll then need to create additional instances (and possibly prove lemmas about them).
See e.g. `Mathlib/Data/Set/Order.lean`.
-/
@[coe, reducible] def Elem (s : Set α) : Type u := {x // x ∈ s}

/-- Coercion from a set to the corresponding subtype. -/
instance : CoeSort (Set α) (Type u) := ⟨Elem⟩

end Set

end Mathlib.Data.Set.CoeSort

section Mathlib.Data.Multiset.Defs

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

/-- `Multiset α` is the quotient of `List α` by list permutation. The result
  is a type of finite sets with duplicates allowed. -/
def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset

/-- The quotient map from `List α` to `Multiset α`. -/
def ofList : List α → Multiset α :=
  Quot.mk _

section Mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def Mem (s : Multiset α) (a : α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun l₁ l₂ (e : l₁ ~ l₂) => propext <| e.mem_iff

instance : Membership α (Multiset α) :=
  ⟨Mem⟩

instance decidableMem [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a ∈ s) :=
  Quot.recOnSubsingleton s fun l ↦ inferInstanceAs (Decidable (a ∈ l))

end Mem

/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card : Multiset α → Nat := Quot.lift length sorry

/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
nonrec def pmap {p : α → Prop} (f : ∀ a, p a → β) (s : Multiset α) : (∀ a ∈ s, p a) → Multiset β :=
  Quot.recOn s (fun l H => ofList (pmap f l H)) sorry

end Multiset

end Mathlib.Data.Multiset.Defs

section Mathlib.Data.Multiset.ZeroCons

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-- `0 : Multiset α` is the empty set -/
protected def zero : Multiset α :=
  ofList (@nil α)

instance : Zero (Multiset α) :=
  ⟨Multiset.zero⟩

end Multiset

end Mathlib.Data.Multiset.ZeroCons

section Mathlib.Data.Multiset.Basic

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section Choose

variable (p : α → Prop) [DecidablePred p] (l : Multiset α)

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `chooseX p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
def chooseX : ∀ _hp : ∃ a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a } :=
  Quotient.recOn l (fun l' h => List.chooseX p l' h) sorry

end Choose

end Multiset

end Mathlib.Data.Multiset.Basic

section Mathlib.Data.Multiset.MapFold

variable {α β : Type*}

namespace Multiset

/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => ofList <| l.map f) sorry

end Multiset

end Mathlib.Data.Multiset.MapFold

section Mathlib.Data.Multiset.Filter

variable {α : Type*}

namespace Multiset

variable (p : α → Prop) [DecidablePred p]

/-- `Filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => ofList <| List.filter p l) sorry

end Multiset

end Mathlib.Data.Multiset.Filter

section Mathlib.Data.Finset.Defs

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

/-- `Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset (α : Type*) where
  /-- The underlying multiset -/
  val : Multiset α

namespace Finset

theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t := sorry

instance : Membership α (Finset α) :=
  ⟨fun s a => a ∈ s.1⟩

instance decidableMem [_h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _

end Finset

end Mathlib.Data.Finset.Defs

section Mathlib.Data.Finset.Dedup

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

end Finset

/-! ### dedup on list and multiset -/

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/-- `toFinset s` removes duplicates from the multiset `s` to produce a finset. -/
def toFinset (s : Multiset α) : Finset α := ⟨s⟩

end Multiset

end Mathlib.Data.Finset.Dedup

section Mathlib.Data.Finset.Empty

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

section Empty

variable {s : Finset α}

/-- The empty finset -/
protected def empty : Finset α := ⟨0⟩

end Empty
end Finset

end Mathlib.Data.Finset.Empty

section Mathlib.Data.Finset.Filter

variable {α : Type*}

namespace Finset

section Filter

variable (p : α → Prop) [DecidablePred p]

/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`.
For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). -/
def filter (s : Finset α) : Finset α :=
  ⟨s.1.filter p⟩

end Finset.Filter

end Mathlib.Data.Finset.Filter

section Mathlib.Data.Finset.Basic

variable {α : Type*}

namespace Finset

section Choose

variable (p : α → Prop) [DecidablePred p] (l : Finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃ a, a ∈ l ∧ p a) : { a // a ∈ l ∧ p a } :=
  Multiset.chooseX p l.val hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃ a, a ∈ l ∧ p a) : α :=
  chooseX p l hp

end Choose

end Finset

end Mathlib.Data.Finset.Basic

section Mathlib.Data.Finset.Image

variable {α β γ : Type*}

namespace Finset

section Map

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α → β) (s : Finset α) : Finset β := ⟨s.1.map f⟩

end Map

section Image

variable [DecidableEq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset

end Image

end Finset

end Mathlib.Data.Finset.Image

section Mathlib.Data.Finset.Card

variable {α β R : Type*}

namespace Finset

variable {s t : Finset α} {a b : α}

/-- `s.card` is the number of elements of `s`, aka its cardinality.
The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : Nat :=
  Multiset.card s.1

end Finset

end Mathlib.Data.Finset.Card

section Mathlib.Data.Fintype.Defs

variable {α β γ : Type*}

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α

namespace Finset

variable [Fintype α] {s t : Finset α}

/-- `univ` is the universal finite set of type `Finset α` implied from
  the assumption `Fintype α`. -/
def univ : Finset α := @Fintype.elems α _

end Finset

namespace Fintype

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1⟩⟩

end Fintype

end Mathlib.Data.Fintype.Defs

section Mathlib.Data.Fintype.Sets

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

/-- Construct a finset enumerating a set `s`, given a `Fintype` instance. -/
def toFinset (s : Set α) [Fintype s] : Finset α :=
  (@Finset.univ s _).map <| Subtype.val

end Set

instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) sorry

end Mathlib.Data.Fintype.Sets

section Mathlib.Data.Sym.Sym2

open Function

universe u

variable {α β γ : Type*}

namespace Sym2

/-- This is the relation capturing the notion of pairs equivalent up to permutations. -/
inductive Rel (α : Type u) : α × α → α × α → Prop
  | refl (x y : α) : Rel _ (x, y) (x, y)
  | swap (x y : α) : Rel _ (x, y) (y, x)

end Sym2

/-- `Sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs. -/
abbrev Sym2 (α : Type u) := Quot (Sym2.Rel α)

/-- Constructor for `Sym2`. This is the quotient map `α × α → Sym2 α`. -/
protected abbrev Sym2.mk {α : Type*} (p : α × α) : Sym2 α := Quot.mk (Sym2.Rel α) p

namespace Sym2

/-- The universal property of `Sym2`; symmetric functions of two arguments are equivalent to
functions from `Sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`Sym2.fromRel` instead. -/
def lift : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } → (Sym2 α → β) :=
  fun f => Quot.lift (uncurry f) <| by sorry

section Relations

variable {r : α → α → Prop}

/-- Symmetric relations define a set on `Sym2 α` by taking all those pairs
of elements that are related.
-/
def fromRel (sym : Symmetric r) : Set (Sym2 α) :=
  setOf (lift ⟨r, fun _ _ => propext ⟨(sym ·), (sym ·)⟩⟩)

instance fromRel.decidablePred (sym : Symmetric r) [h : DecidableRel r] :
    DecidablePred (· ∈ Sym2.fromRel sym) := fun z => z.recOnSubsingleton fun _ => h _ _

end Relations

end Sym2

end Mathlib.Data.Sym.Sym2

section Mathlib.Data.List.Sym

namespace List

variable {α β : Type*}

section Sym2

/-- `xs.sym2` is a list of all unordered pairs of elements from `xs`.
If `xs` has no duplicates then neither does `xs.sym2`. -/
protected def sym2 : List α → List (Sym2 α)
  | [] => []
  | x :: xs => (x :: xs).map (fun y => .mk (x, y)) ++ xs.sym2

end Sym2

end List

end Mathlib.Data.List.Sym

section Mathlib.Data.Multiset.Sym

namespace Multiset

variable {α β : Type*}

section Sym2

/-- `m.sym2` is the multiset of all unordered pairs of elements from `m`, with multiplicity.
If `m` has no duplicates then neither does `m.sym2`. -/
protected def sym2 (m : Multiset α) : Multiset (Sym2 α) :=
  m.liftOn (fun xs => ofList xs.sym2) fun _ _ h => sorry

end Sym2

end Multiset

end Mathlib.Data.Multiset.Sym

section Mathlib.Data.Finset.Sym

namespace Finset

variable {α β : Type*}

protected def sym2 (s : Finset α) : Finset (Sym2 α) := ⟨s.1.sym2⟩

section
variable {s t : Finset α} {a b : α}

instance _root_.Sym2.instFintype [Fintype α] : Fintype (Sym2 α) where
  elems := Finset.univ.sym2

end

end Finset

end Mathlib.Data.Finset.Sym

section Mathlib.Combinatorics.SimpleGraph.Basic

open Function

universe u v w

/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G : SimpleGraph V) {a b c u v w : V} {e : Sym2 V}

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

/-- The edges of G consist of the unordered pairs of vertices related by
`G.Adj`. This is the order embedding; for the edge set of a particular graph, see
`SimpleGraph.edgeSet`.

The way `edgeSet` is defined is such that `mem_edgeSet` is proved by `Iff.rfl`.
(That is, `s(v, w) ∈ G.edgeSet` is definitionally equal to `G.Adj v w`.)
-/
-- Porting note: We need a separate definition so that dot notation works.
def edgeSetEmbedding (V : Type*) : SimpleGraph V → Set (Sym2 V) :=
  fun G => Sym2.fromRel (r := G.1) sorry

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G

variable (G₁ G₂)

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred sorry

end EdgeSet

end SimpleGraph

end Mathlib.Combinatorics.SimpleGraph.Basic

section Mathlib.Combinatorics.SimpleGraph.Finite
namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {e : Sym2 V}
variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edgeSet` of the graph as a `Finset`. -/
abbrev edgeFinset : Finset (Sym2 V) := Set.toFinset G.edgeSet

end SimpleGraph
end Mathlib.Combinatorics.SimpleGraph.Finite

section Mathlib.Combinatorics.SimpleGraph.Clique

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

/-! ### `n`-cliques -/

section NClique

variable {n : Nat} {s : Finset α}

/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (G : SimpleGraph α) (n : Nat) (s : Finset α) : Prop where

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : Nat}

/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : Nat) : Prop :=
  ∀ t, ¬G.IsNClique n t

end CliqueFree

end SimpleGraph
end Mathlib.Combinatorics.SimpleGraph.Clique

section Mathlib.Order.Partition.Finpartition
open Finset

variable {α : Type*}

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
structure Finpartition (a : α) where
  /-- The elements of the finite partition of `a` -/
  parts : Finset α

/-! ### Finite partitions of finsets -/

namespace Finpartition

variable [DecidableEq α] {s t u : Finset α} (P : Finpartition s) {a : α}

theorem existsUnique_mem (ha : a ∈ s) : ∃ t, t ∈ P.parts ∧ a ∈ t := by sorry

/-- The part of the finpartition that `a` lies in. -/
def part (a : α) : Finset α := if ha : a ∈ s then choose (hp := P.existsUnique_mem ha) else .empty

section SetSetoid

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
def ofSetSetoid (s : Setoid α) (x : Finset α) [DecidableRel s.r] : Finpartition x where
  parts := x.image fun a ↦ x.filter (s.r a ·)

end SetSetoid

section Setoid

variable [Fintype α]

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
def ofSetoid (s : Setoid α) [DecidableRel s.r] : Finpartition (univ : Finset α) :=
  ofSetSetoid s univ

end Setoid

end Finpartition

end Mathlib.Order.Partition.Finpartition

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n r : Nat}

variable (G) in
/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : Nat) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → H.edgeFinset.card ≤ G.edgeFinset.card

namespace IsTuranMaximal

variable {s t u : V}

variable (h : G.IsTuranMaximal r)
include h

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
theorem equivalence_not_adj : Equivalence (¬G.Adj · ·) where
  refl := sorry
  symm := sorry
  trans := sorry

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `equivalence_not_adj`. -/
def setoid : Setoid V := ⟨_, h.equivalence_not_adj⟩

instance : DecidableRel h.setoid.r :=
  inferInstanceAs <| DecidableRel (¬G.Adj · ·)

/-- The finpartition derived from `h.setoid`. -/
def finpartition [DecidableEq V] : Finpartition (univ : Finset V) := Finpartition.ofSetoid h.setoid

theorem not_adj_iff_part_eq [DecidableEq V] :
    ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t := by sorry

theorem card_parts_extracted_1_11 [DecidableEq V] :
  let fp := h.finpartition;
  fp.parts.card < (Finset.univ (α := V)).card ∧ fp.parts.card < r →
    ∀ (x y : V),
      x ≠ y → fp.part x = fp.part y →
      ∀ ⦃z : Finset V⦄, z.card = r → ∃ x ∈ ↑z, ∃ y ∈ ↑z, x ≠ y ∧ ¬G.Adj x y := by
  intro fp l x y hn he z zc
  simp [h.not_adj_iff_part_eq] ---- should work
  sorry

end IsTuranMaximal

end SimpleGraph
