/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez, Markus Himmel, Paul Reichert
-/
module

prelude
public import Std.Data.DTreeMap.Lemmas

@[expose] public section

/-!
# Extensional dependent tree maps

This file develops the type `Std.ExtDTreeMap` of extensional dependent tree maps.

Lemmas about the operations on `Std.ExtDTreeMap` will be available in the
module `Std.Data.ExtDTreeMap.Lemmas`.

See the module `Std.Data.DTreeMap.Raw.Basic` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {cmp : α → α → Ordering}

attribute [local instance] Std.DTreeMap.isSetoid

open scoped Std.DTreeMap

namespace Std

/--
Extensional dependent tree maps.

A tree map stores an assignment of keys to values. It depends on a comparator function that
defines an ordering on the keys and provides efficient order-dependent queries, such as retrieval
of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass).
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
is less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e., there can be only one entry
with key either `a` or `b` in a tree map. Looking up either `a` or `b` always yields the same entry,
if any is present. The `get` operations of the _dependent_ tree map additionally require a
`LawfulEqCmp` instance to ensure that `cmp a b = .eq` always implies `a = b`, so that their
respective value types are equal.

To avoid expensive copies, users should make sure that the tree map is used linearly.

Internally, the tree maps are represented as size-bounded trees, a type of self-balancing binary
search tree with efficient order statistic lookups.

In contrast to regular dependent tree maps, `Std.ExtDTreeMap` offers several extensionality lemmas
and therefore has more lemmas about equality of tree maps. This doesn't affect the amount of
supported functions though: `Std.ExtDTreeMap` supports all operations from `Std.DTreeMap`.

In order to use most functions, a `TransCmp` instance is required. This is necessary to make sure
that the functions are congruent, i.e. equivalent tree maps as parameters produce equivalent return
values.

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.DTreeMap.Raw` and
`Std.DTreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`ExtDTreeMap` over `DTreeMap.Raw`.
-/
structure ExtDTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- Implementation detail of the tree map -/
  mk' ::
  /-- Implementation detail of the tree map -/
  inner : Quotient (DTreeMap.isSetoid α β cmp)

/-- Implementation detail of the tree map -/
abbrev ExtDTreeMap.mk (t : DTreeMap α β cmp) : ExtDTreeMap α β cmp :=
  .mk' (Quotient.mk _ t)

/-- Implementation detail of the tree map -/
abbrev ExtDTreeMap.lift {γ : Sort w} (f : DTreeMap α β cmp → γ) (h : ∀ a b, a ~m b → f a = f b)
    (t : ExtDTreeMap α β cmp) : γ :=
  t.1.lift f h

/-- Implementation detail of the tree map -/
def ExtDTreeMap.lift₂ {γ : Sort w}  (f : DTreeMap α β cmp → DTreeMap α β cmp → γ) (h : ∀ a b c d, a ~m c → b ~m d → f a b = f c d) (m₁ m₂ : ExtDTreeMap α β cmp) : γ :=
  Quotient.lift₂ f h m₁.inner m₂.inner

/-- Implementation detail of the tree map -/
abbrev ExtDTreeMap.liftOn₂ {γ : Sort w} (t₁ t₂ : ExtDTreeMap α β cmp)
    (f : DTreeMap α β cmp → DTreeMap α β cmp → γ) (h : ∀ a b c d, a ~m c → b ~m d → f a b = f c d) : γ :=
  t₁.1.liftOn₂ t₂.1 f h

/-- Implementation detail of the tree map -/
abbrev ExtDTreeMap.pliftOn {γ : Sort w} (t : ExtDTreeMap α β cmp)
    (f : (x : DTreeMap α β cmp) → t = mk x → γ) (h : ∀ a b h₁ h₂, a ~m b → f a h₁ = f b h₂) : γ :=
  t.1.pliftOn (fun x hx => f x (by cases t; cases hx; rfl)) (fun a b _ _ h' => h a b _ _ h')

theorem ExtDTreeMap.sound {t₁ t₂ : DTreeMap α β cmp} (h : t₁ ~m t₂) : mk t₁ = mk t₂ :=
  congrArg mk' (Quotient.sound h)

theorem ExtDTreeMap.exact {t₁ t₂ : DTreeMap α β cmp} (h : mk t₁ = mk t₂) : t₁ ~m t₂ :=
  Quotient.exact (congrArg inner h)

@[cases_eliminator, induction_eliminator, elab_as_elim]
theorem ExtDTreeMap.inductionOn {motive : ExtDTreeMap α β cmp → Prop}
    (t : ExtDTreeMap α β cmp) (mk : ∀ a, motive (mk a)) : motive t :=
  (t.1.inductionOn fun _ => mk _ : motive ⟨t.1⟩)

@[elab_as_elim]
theorem ExtDTreeMap.inductionOn₂ {motive : ExtDTreeMap α β cmp → ExtDTreeMap α β cmp → Prop}
    (t₁ t₂ : ExtDTreeMap α β cmp) (mk : ∀ a b, motive (mk a) (mk b)) : motive t₁ t₂ :=
  t₁.inductionOn fun _ => t₂.inductionOn fun _ => mk _ _

namespace ExtDTreeMap
local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

@[inline, inherit_doc DTreeMap.empty]
def empty : ExtDTreeMap α β cmp :=
  mk .empty

instance : EmptyCollection (ExtDTreeMap α β cmp) where
  emptyCollection := empty

instance : Inhabited (ExtDTreeMap α β cmp) where
  default := ∅

@[simp, grind =]
theorem empty_eq_emptyc : (empty : ExtDTreeMap α β cmp) = ∅ :=
  rfl

@[inline, inherit_doc DTreeMap.insert]
def insert [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (b : β a) : ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (m.insert a b)) (fun _ _ h => sound (h.insert a b))

instance [TransCmp cmp] : Singleton ((a : α) × β a) (ExtDTreeMap α β cmp) where
  singleton e := (∅ : ExtDTreeMap α β cmp).insert e.1 e.2

instance [TransCmp cmp] : Insert ((a : α) × β a) (ExtDTreeMap α β cmp) where
  insert e s := s.insert e.1 e.2

instance [TransCmp cmp] : LawfulSingleton ((a : α) × β a) (ExtDTreeMap α β cmp) where
  insert_empty_eq _ := rfl

@[inline, inherit_doc DTreeMap.insertIfNew]
def insertIfNew [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (b : β a) : ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (m.insertIfNew a b)) (fun _ _ h => sound (h.insertIfNew a b))

@[inline, inherit_doc DTreeMap.containsThenInsert]
def containsThenInsert [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (b : β a) : Bool × ExtDTreeMap α β cmp :=
  t.lift (fun m => let m' := m.containsThenInsert a b; (m'.1, mk m'.2))
    (fun m m' h =>
      Prod.ext
        (m.containsThenInsert_fst.symm ▸ m'.containsThenInsert_fst.symm ▸ h.contains_eq)
        (sound <|
          m.containsThenInsert_snd.symm ▸ m'.containsThenInsert_snd.symm ▸ h.insert a b))

@[inline, inherit_doc DTreeMap.containsThenInsertIfNew]
def containsThenInsertIfNew [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (b : β a) :
    Bool × ExtDTreeMap α β cmp :=
  t.lift (fun m => let m' := m.containsThenInsertIfNew a b; (m'.1, mk m'.2))
    (fun m m' h =>
      Prod.ext
        (m.containsThenInsertIfNew_fst.symm ▸ m'.containsThenInsertIfNew_fst.symm ▸ h.contains_eq)
        (sound <|
          m.containsThenInsertIfNew_snd.symm ▸ m'.containsThenInsertIfNew_snd.symm ▸ h.insertIfNew a b))

@[inline, inherit_doc DTreeMap.getThenInsertIfNew?]
def getThenInsertIfNew? [TransCmp cmp] [LawfulEqCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (b : β a) :
    Option (β a) × ExtDTreeMap α β cmp :=
  t.lift (fun m => let m' := m.getThenInsertIfNew? a b; (m'.1, mk m'.2))
    (fun m m' h =>
      Prod.ext
        (m.getThenInsertIfNew?_fst.symm ▸ m'.getThenInsertIfNew?_fst.symm ▸ h.get?_eq)
        (sound <|
          m.getThenInsertIfNew?_snd.symm ▸ m'.getThenInsertIfNew?_snd.symm ▸ h.insertIfNew a b))

@[inline, inherit_doc DTreeMap.contains]
def contains [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) : Bool :=
  t.lift (fun m => m.contains a) (fun _ _ h => h.contains_eq)

instance [TransCmp cmp] : Membership α (ExtDTreeMap α β cmp) where
  mem m a := m.contains a

instance [TransCmp cmp] {m : ExtDTreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc DTreeMap.size]
def size (t : ExtDTreeMap α β cmp) : Nat :=
  t.lift (fun m => m.size) (fun _ _ h => h.size_eq)

@[inline, inherit_doc DTreeMap.isEmpty]
def isEmpty (t : ExtDTreeMap α β cmp) : Bool :=
  t.lift (fun m => m.isEmpty) (fun _ _ h => h.isEmpty_eq)

@[simp, grind =]
theorem isEmpty_iff {t : ExtDTreeMap α β cmp} [TransCmp cmp] : t.isEmpty ↔ t = ∅ := by
  rcases t with ⟨⟨t⟩⟩
  refine t.equiv_empty_iff_isEmpty.symm.trans ?_
  exact ⟨fun h => sound h, exact⟩

@[simp]
theorem isEmpty_eq_false_iff {t : ExtDTreeMap α β cmp} [TransCmp cmp] : t.isEmpty = false ↔ ¬t = ∅ :=
  (Bool.not_eq_true _).symm.to_iff.trans (not_congr isEmpty_iff)

@[inline, inherit_doc DTreeMap.erase]
def erase [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) : ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (m.erase a))
    (fun _ _ h => sound (h.erase a))

@[inline, inherit_doc DTreeMap.get?]
def get? [TransCmp cmp] [LawfulEqCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) : Option (β a) :=
  t.lift (fun m => m.get? a) (fun _ _ h => h.get?_eq)

@[inline, inherit_doc DTreeMap.get]
def get [TransCmp cmp] [LawfulEqCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (h : a ∈ t) : β a :=
  t.pliftOn (fun m h' => m.get a (h' ▸ h :))
    (fun _ _ _ _ h => h.get_eq)

@[inline, inherit_doc DTreeMap.get!]
def get! [TransCmp cmp] [LawfulEqCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) [Inhabited (β a)] : β a :=
  t.lift (fun m => m.get! a) (fun _ _ h => h.get!_eq)

@[inline, inherit_doc DTreeMap.getD]
def getD [TransCmp cmp] [LawfulEqCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (fallback : β a) : β a :=
  t.lift (fun m => m.getD a fallback) (fun _ _ h => h.getD_eq)

@[inline, inherit_doc DTreeMap.getKey?]
def getKey? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) : Option α :=
  t.lift (fun m => m.getKey? a) (fun _ _ h => h.getKey?_eq)

@[inline, inherit_doc DTreeMap.getKey]
def getKey [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (h : a ∈ t) : α :=
  t.pliftOn (fun m h' => m.getKey a (h' ▸ h :))
    (fun _ _ _ _ h => h.getKey_eq)

@[inline, inherit_doc DTreeMap.getKey!]
def getKey! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) (a : α) : α :=
  t.lift (fun m => m.getKey! a) (fun _ _ h => h.getKey!_eq)

@[inline, inherit_doc DTreeMap.getKeyD]
def getKeyD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (fallback : α) : α :=
  t.lift (fun m => m.getKeyD a fallback) (fun _ _ h => h.getKeyD_eq)

@[inline, inherit_doc DTreeMap.minEntry?]
def minEntry? [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Option ((a : α) × β a) :=
  t.lift (fun m => m.minEntry?) (fun _ _ h => h.minEntry?_eq)

@[inline, inherit_doc DTreeMap.minEntry]
def minEntry [TransCmp cmp] (t : ExtDTreeMap α β cmp) (h : t ≠ ∅) : (a : α) × β a :=
  t.pliftOn (fun m h' => m.minEntry (h' ▸ isEmpty_eq_false_iff.mpr h :))
    (fun _ _ _ _ h => h.minEntry_eq)

@[inline, inherit_doc DTreeMap.minEntry!]
def minEntry! [TransCmp cmp] [Inhabited ((a : α) × β a)] (t : ExtDTreeMap α β cmp) : (a : α) × β a :=
  t.lift (fun m => m.minEntry!) (fun _ _ h => h.minEntry!_eq)

@[inline, inherit_doc DTreeMap.minEntryD]
def minEntryD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (fallback : (a : α) × β a) : (a : α) × β a :=
  t.lift (fun m => m.minEntryD fallback) (fun _ _ h => h.minEntryD_eq)

@[inline, inherit_doc DTreeMap.maxEntry?]
def maxEntry? [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Option ((a : α) × β a) :=
  t.lift (fun m => m.maxEntry?) (fun _ _ h => h.maxEntry?_eq)

@[inline, inherit_doc DTreeMap.maxEntry]
def maxEntry [TransCmp cmp] (t : ExtDTreeMap α β cmp) (h : t ≠ ∅) : (a : α) × β a :=
  t.pliftOn (fun m h' => m.maxEntry (h' ▸ isEmpty_eq_false_iff.mpr h :))
    (fun _ _ _ _ h => h.maxEntry_eq)

@[inline, inherit_doc DTreeMap.maxEntry!]
def maxEntry! [TransCmp cmp] [Inhabited ((a : α) × β a)] (t : ExtDTreeMap α β cmp) : (a : α) × β a :=
  t.lift (fun m => m.maxEntry!) (fun _ _ h => h.maxEntry!_eq)

@[inline, inherit_doc DTreeMap.maxEntryD]
def maxEntryD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (fallback : (a : α) × β a) : (a : α) × β a :=
  t.lift (fun m => m.maxEntryD fallback) (fun _ _ h => h.maxEntryD_eq)

@[inline, inherit_doc DTreeMap.minKey?]
def minKey? [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Option α :=
  t.lift (fun m => m.minKey?) (fun _ _ h => h.minKey?_eq)

@[inline, inherit_doc DTreeMap.minKey]
def minKey [TransCmp cmp] (t : ExtDTreeMap α β cmp) (h : t ≠ ∅) : α :=
  t.pliftOn (fun m h' => m.minKey (h' ▸ isEmpty_eq_false_iff.mpr h :))
    (fun _ _ _ _ h => h.minKey_eq)

@[inline, inherit_doc DTreeMap.minKey!]
def minKey! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) : α :=
  t.lift (fun m => m.minKey!) (fun _ _ h => h.minKey!_eq)

@[inline, inherit_doc DTreeMap.minKeyD]
def minKeyD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (fallback : α) : α :=
  t.lift (fun m => m.minKeyD fallback) (fun _ _ h => h.minKeyD_eq)

@[inline, inherit_doc DTreeMap.maxKey?]
def maxKey? [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Option α :=
  t.lift (fun m => m.maxKey?) (fun _ _ h => h.maxKey?_eq)

@[inline, inherit_doc DTreeMap.maxKey]
def maxKey [TransCmp cmp] (t : ExtDTreeMap α β cmp) (h : t ≠ ∅) : α :=
  t.pliftOn (fun m h' => m.maxKey (h' ▸ isEmpty_eq_false_iff.mpr h :))
    (fun _ _ _ _ h => h.maxKey_eq)

@[inline, inherit_doc DTreeMap.maxKey!]
def maxKey! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) : α :=
  t.lift (fun m => m.maxKey!) (fun _ _ h => h.maxKey!_eq)

@[inline, inherit_doc DTreeMap.maxKeyD]
def maxKeyD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (fallback : α) : α :=
  t.lift (fun m => m.maxKeyD fallback) (fun _ _ h => h.maxKeyD_eq)

@[inline, inherit_doc DTreeMap.entryAtIdx?]
def entryAtIdx? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat) : Option ((a : α) × β a) :=
  t.lift (fun m => m.entryAtIdx? n) (fun _ _ h => h.entryAtIdx?_eq)

@[inline, inherit_doc DTreeMap.entryAtIdx]
def entryAtIdx [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat) (h : n < t.size) : (a : α) × β a :=
  t.pliftOn (fun m h' => m.entryAtIdx n (h' ▸ h :))
    (fun _ _ _ _ h => h.entryAtIdx_eq)

@[inline, inherit_doc DTreeMap.entryAtIdx!]
def entryAtIdx! [TransCmp cmp] [Inhabited ((a : α) × β a)] (t : ExtDTreeMap α β cmp) (n : Nat) : (a : α) × β a :=
  t.lift (fun m => m.entryAtIdx! n) (fun _ _ h => h.entryAtIdx!_eq)

@[inline, inherit_doc DTreeMap.entryAtIdxD]
def entryAtIdxD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat)
    (fallback : (a : α) × β a) : (a : α) × β a :=
  t.lift (fun m => m.entryAtIdxD n fallback) (fun _ _ h => h.entryAtIdxD_eq)

@[inline, inherit_doc DTreeMap.keyAtIdx?]
def keyAtIdx? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat) : Option α :=
  t.lift (fun m => m.keyAtIdx? n) (fun _ _ h => h.keyAtIdx?_eq)

@[inline, inherit_doc DTreeMap.keyAtIdx]
def keyAtIdx [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat) (h : n < t.size) : α :=
  t.pliftOn (fun m h' => m.keyAtIdx n (h' ▸ h :))
    (fun _ _ _ _ h => h.keyAtIdx_eq)

@[inline, inherit_doc DTreeMap.keyAtIdx!]
def keyAtIdx! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) (n : Nat) : α :=
  t.lift (fun m => m.keyAtIdx! n) (fun _ _ h => h.keyAtIdx!_eq)

@[inline, inherit_doc DTreeMap.keyAtIdxD]
def keyAtIdxD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat) (fallback : α) : α :=
  t.lift (fun m => m.keyAtIdxD n fallback) (fun _ _ h => h.keyAtIdxD_eq)

@[inline, inherit_doc DTreeMap.getEntryGE?]
def getEntryGE? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  t.lift (fun m => m.getEntryGE? k) (fun _ _ h => h.getEntryGE?_eq)

@[inline, inherit_doc DTreeMap.getEntryGT?]
def getEntryGT? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  t.lift (fun m => m.getEntryGT? k) (fun _ _ h => h.getEntryGT?_eq)

@[inline, inherit_doc DTreeMap.getEntryLE?]
def getEntryLE? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  t.lift (fun m => m.getEntryLE? k) (fun _ _ h => h.getEntryLE?_eq)

@[inline, inherit_doc DTreeMap.getEntryLT?]
def getEntryLT? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  t.lift (fun m => m.getEntryLT? k) (fun _ _ h => h.getEntryLT?_eq)

@[inline, inherit_doc DTreeMap.getEntryGE]
def getEntryGE [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) :
    (a : α) × β a :=
  t.pliftOn (fun m h' => m.getEntryGE k (h' ▸ h :))
    (fun _ _ _ _ h => h.getEntryGE_eq)

@[inline, inherit_doc DTreeMap.getEntryGT]
def getEntryGT [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) :
    (a : α) × β a :=
  t.pliftOn (fun m h' => m.getEntryGT k (h' ▸ h :))
    (fun _ _ _ _ h => h.getEntryGT_eq)

@[inline, inherit_doc DTreeMap.getEntryLE]
def getEntryLE [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) :
    (a : α) × β a :=
  t.pliftOn (fun m h' => m.getEntryLE k (h' ▸ h :))
    (fun _ _ _ _ h => h.getEntryLE_eq)

@[inline, inherit_doc DTreeMap.getEntryLT]
def getEntryLT [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) :
    (a : α) × β a :=
  t.pliftOn (fun m h' => m.getEntryLT k (h' ▸ h :))
    (fun _ _ _ _ h => h.getEntryLT_eq)

@[inline, inherit_doc DTreeMap.getEntryGE!]
def getEntryGE! [TransCmp cmp] [Inhabited (Sigma β)] (t : ExtDTreeMap α β cmp) (k : α) : (a : α) × β a :=
  t.lift (fun m => m.getEntryGE! k) (fun _ _ h => h.getEntryGE!_eq)

@[inline, inherit_doc DTreeMap.getEntryGT!]
def getEntryGT! [TransCmp cmp] [Inhabited (Sigma β)] (t : ExtDTreeMap α β cmp) (k : α) : (a : α) × β a :=
  t.lift (fun m => m.getEntryGT! k) (fun _ _ h => h.getEntryGT!_eq)

@[inline, inherit_doc DTreeMap.getEntryLE!]
def getEntryLE! [TransCmp cmp] [Inhabited (Sigma β)] (t : ExtDTreeMap α β cmp) (k : α) : (a : α) × β a :=
  t.lift (fun m => m.getEntryLE! k) (fun _ _ h => h.getEntryLE!_eq)

@[inline, inherit_doc DTreeMap.getEntryLT!]
def getEntryLT! [TransCmp cmp] [Inhabited (Sigma β)] (t : ExtDTreeMap α β cmp) (k : α) : (a : α) × β a :=
  t.lift (fun m => m.getEntryLT! k) (fun _ _ h => h.getEntryLT!_eq)

@[inline, inherit_doc DTreeMap.getEntryGED]
def getEntryGED [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  t.lift (fun m => m.getEntryGED k fallback) (fun _ _ h => h.getEntryGED_eq)

@[inline, inherit_doc DTreeMap.getEntryGTD]
def getEntryGTD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  t.lift (fun m => m.getEntryGTD k fallback) (fun _ _ h => h.getEntryGTD_eq)

@[inline, inherit_doc DTreeMap.getEntryLED]
def getEntryLED [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  t.lift (fun m => m.getEntryLED k fallback) (fun _ _ h => h.getEntryLED_eq)

@[inline, inherit_doc DTreeMap.getEntryLTD]
def getEntryLTD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  t.lift (fun m => m.getEntryLTD k fallback) (fun _ _ h => h.getEntryLTD_eq)

@[inline, inherit_doc DTreeMap.getKeyGE?]
def getKeyGE? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option α :=
  t.lift (fun m => m.getKeyGE? k) (fun _ _ h => h.getKeyGE?_eq)

@[inline, inherit_doc DTreeMap.getKeyGT?]
def getKeyGT? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option α :=
  t.lift (fun m => m.getKeyGT? k) (fun _ _ h => h.getKeyGT?_eq)

@[inline, inherit_doc DTreeMap.getKeyLE?]
def getKeyLE? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option α :=
  t.lift (fun m => m.getKeyLE? k) (fun _ _ h => h.getKeyLE?_eq)

@[inline, inherit_doc DTreeMap.getKeyLT?]
def getKeyLT? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option α :=
  t.lift (fun m => m.getKeyLT? k) (fun _ _ h => h.getKeyLT?_eq)

@[inline, inherit_doc DTreeMap.getKeyGE]
def getKeyGE [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) : α :=
  t.pliftOn (fun m h' => m.getKeyGE k (h' ▸ h :))
    (fun _ _ _ _ h => h.getKeyGE_eq)

@[inline, inherit_doc DTreeMap.getKeyGT]
def getKeyGT [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) : α :=
  t.pliftOn (fun m h' => m.getKeyGT k (h' ▸ h :))
    (fun _ _ _ _ h => h.getKeyGT_eq)

@[inline, inherit_doc DTreeMap.getKeyLE]
def getKeyLE [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) : α :=
  t.pliftOn (fun m h' => m.getKeyLE k (h' ▸ h :))
    (fun _ _ _ _ h => h.getKeyLE_eq)

@[inline, inherit_doc DTreeMap.getKeyLT]
def getKeyLT [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) : α :=
  t.pliftOn (fun m h' => m.getKeyLT k (h' ▸ h :))
    (fun _ _ _ _ h => h.getKeyLT_eq)

@[inline, inherit_doc DTreeMap.getKeyGE!]
def getKeyGE! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) (k : α) : α :=
  t.lift (fun m => m.getKeyGE! k) (fun _ _ h => h.getKeyGE!_eq)

@[inline, inherit_doc DTreeMap.getKeyGT!]
def getKeyGT! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) (k : α) : α :=
  t.lift (fun m => m.getKeyGT! k) (fun _ _ h => h.getKeyGT!_eq)

@[inline, inherit_doc DTreeMap.getKeyLE!]
def getKeyLE! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) (k : α) : α :=
  t.lift (fun m => m.getKeyLE! k) (fun _ _ h => h.getKeyLE!_eq)

@[inline, inherit_doc DTreeMap.getKeyLT!]
def getKeyLT! [TransCmp cmp] [Inhabited α] (t : ExtDTreeMap α β cmp) (k : α) : α :=
  t.lift (fun m => m.getKeyLT! k) (fun _ _ h => h.getKeyLT!_eq)

@[inline, inherit_doc DTreeMap.getKeyGED]
def getKeyGED [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α) : α :=
  t.lift (fun m => m.getKeyGED k fallback) (fun _ _ h => h.getKeyGED_eq)

@[inline, inherit_doc DTreeMap.getKeyGTD]
def getKeyGTD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α) : α :=
  t.lift (fun m => m.getKeyGTD k fallback) (fun _ _ h => h.getKeyGTD_eq)

@[inline, inherit_doc DTreeMap.getKeyLED]
def getKeyLED [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α) : α :=
  t.lift (fun m => m.getKeyLED k fallback) (fun _ _ h => h.getKeyLED_eq)

@[inline, inherit_doc DTreeMap.getKeyLTD]
def getKeyLTD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α) : α :=
  t.lift (fun m => m.getKeyLTD k fallback) (fun _ _ h => h.getKeyLTD_eq)

namespace Const

variable {β : Type v}

@[inline, inherit_doc ExtDTreeMap.getThenInsertIfNew?]
def getThenInsertIfNew? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (b : β) :
    Option β × ExtDTreeMap α β cmp :=
  t.lift (fun m => let m' := DTreeMap.Const.getThenInsertIfNew? m a b; (m'.1, mk m'.2))
    (fun m m' h =>
      Prod.ext
        ((DTreeMap.Const.getThenInsertIfNew?_fst (t := m)).symm ▸
          (DTreeMap.Const.getThenInsertIfNew?_fst (t := m')).symm ▸
          h.constGet?_eq)
        (sound <|
          (DTreeMap.Const.getThenInsertIfNew?_snd (t := m)).symm ▸
          (DTreeMap.Const.getThenInsertIfNew?_snd (t := m')).symm ▸
          h.insertIfNew a b))

@[inline, inherit_doc ExtDTreeMap.get?]
def get? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) : Option β :=
  t.lift (fun m => DTreeMap.Const.get? m a)
    (fun _ _ h => h.constGet?_eq)

@[inline, inherit_doc ExtDTreeMap.get]
def get [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (h : a ∈ t) : β :=
  t.pliftOn (fun m h' => DTreeMap.Const.get m a (h' ▸ h :))
    (fun _ _ _ _ h => h.constGet_eq)

@[inline, inherit_doc ExtDTreeMap.get!]
def get! [TransCmp cmp] [Inhabited β] (t : ExtDTreeMap α β cmp) (a : α) : β :=
  t.lift (fun m => DTreeMap.Const.get! m a)
    (fun _ _ h => h.constGet!_eq)

@[inline, inherit_doc ExtDTreeMap.getD]
def getD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (fallback : β) : β :=
  t.lift (fun m => DTreeMap.Const.getD m a fallback)
    (fun _ _ h => h.constGetD_eq)

@[inline, inherit_doc ExtDTreeMap.minEntry?]
def minEntry? [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Option (α × β) :=
  t.lift (fun m => DTreeMap.Const.minEntry? m)
    (fun _ _ h => h.constMinEntry?_eq)

@[inline, inherit_doc ExtDTreeMap.minEntry]
def minEntry [TransCmp cmp] (t : ExtDTreeMap α β cmp) (h : t ≠ ∅) : α × β :=
  t.pliftOn (fun m h' => DTreeMap.Const.minEntry m (h' ▸ isEmpty_eq_false_iff.mpr h :))
    (fun _ _ _ _ h => h.constMinEntry_eq)

@[inline, inherit_doc ExtDTreeMap.minEntry!]
def minEntry! [TransCmp cmp] [Inhabited (α × β)] (t : ExtDTreeMap α β cmp) : α × β :=
  t.lift (fun m => DTreeMap.Const.minEntry! m)
    (fun _ _ h => h.constMinEntry!_eq)

@[inline, inherit_doc ExtDTreeMap.minEntryD]
def minEntryD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (fallback : α × β) : α × β :=
  t.lift (fun m => DTreeMap.Const.minEntryD m fallback)
    (fun _ _ h => h.constMinEntryD_eq)

@[inline, inherit_doc ExtDTreeMap.maxEntry?]
def maxEntry? [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Option (α × β) :=
  t.lift (fun m => DTreeMap.Const.maxEntry? m)
    (fun _ _ h => h.constMaxEntry?_eq)

@[inline, inherit_doc ExtDTreeMap.maxEntry]
def maxEntry [TransCmp cmp] (t : ExtDTreeMap α β cmp) (h : t ≠ ∅) : α × β :=
  t.pliftOn (fun m h' => DTreeMap.Const.maxEntry m (h' ▸ isEmpty_eq_false_iff.mpr h :))
    (fun _ _ _ _ h => h.constMaxEntry_eq)

@[inline, inherit_doc ExtDTreeMap.maxEntry!]
def maxEntry! [TransCmp cmp] [Inhabited (α × β)] (t : ExtDTreeMap α β cmp) : α × β :=
  t.lift (fun m => DTreeMap.Const.maxEntry! m)
    (fun _ _ h => h.constMaxEntry!_eq)

@[inline, inherit_doc ExtDTreeMap.maxEntryD]
def maxEntryD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (fallback : α × β) : α × β :=
  t.lift (fun m => DTreeMap.Const.maxEntryD m fallback)
    (fun _ _ h => h.constMaxEntryD_eq)

@[inline, inherit_doc ExtDTreeMap.entryAtIdx?]
def entryAtIdx? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat) : Option (α × β) :=
  t.lift (fun m => DTreeMap.Const.entryAtIdx? m n)
    (fun _ _ h => h.constEntryAtIdx?_eq)

@[inline, inherit_doc ExtDTreeMap.entryAtIdx]
def entryAtIdx [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat) (h : n < t.size) : α × β :=
  t.pliftOn (fun m h' => DTreeMap.Const.entryAtIdx m n (h' ▸ h :))
    (fun _ _ _ _ h => h.constEntryAtIdx_eq)

@[inline, inherit_doc ExtDTreeMap.entryAtIdx!]
def entryAtIdx! [TransCmp cmp] [Inhabited (α × β)] (t : ExtDTreeMap α β cmp) (n : Nat) : α × β :=
  t.lift (fun m => DTreeMap.Const.entryAtIdx! m n)
    (fun _ _ h => h.constEntryAtIdx!_eq)

@[inline, inherit_doc ExtDTreeMap.entryAtIdxD]
def entryAtIdxD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (n : Nat)
    (fallback : α × β) : α × β :=
  t.lift (fun m => DTreeMap.Const.entryAtIdxD m n fallback)
    (fun _ _ h => h.constEntryAtIdxD_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGE?]
def getEntryGE? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryGE? m k)
    (fun _ _ h => h.constGetEntryGE?_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGT?]
def getEntryGT? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryGT? m k)
    (fun _ _ h => h.constGetEntryGT?_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLE?]
def getEntryLE? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryLE? m k)
    (fun _ _ h => h.constGetEntryLE?_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLT?]
def getEntryLT? [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) : Option (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryLT? m k)
    (fun _ _ h => h.constGetEntryLT?_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGE]
def getEntryGE [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) :
    α × β :=
  t.pliftOn (fun m h' => DTreeMap.Const.getEntryGE m k (h' ▸ h :))
    (fun _ _ _ _ h => h.constGetEntryGE_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGT]
def getEntryGT [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) :
    α × β :=
  t.pliftOn (fun m h' => DTreeMap.Const.getEntryGT m k (h' ▸ h :))
    (fun _ _ _ _ h => h.constGetEntryGT_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLE]
def getEntryLE [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) :
    α × β :=
  t.pliftOn (fun m h' => DTreeMap.Const.getEntryLE m k (h' ▸ h :))
    (fun _ _ _ _ h => h.constGetEntryLE_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLT]
def getEntryLT [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) :
    α × β :=
  t.pliftOn (fun m h' => DTreeMap.Const.getEntryLT m k (h' ▸ h :))
    (fun _ _ _ _ h => h.constGetEntryLT_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGE!]
def getEntryGE! [TransCmp cmp] [Inhabited (α × β)] (t : ExtDTreeMap α β cmp) (k : α) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryGE! m k)
    (fun _ _ h => h.constGetEntryGE!_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGT!]
def getEntryGT! [TransCmp cmp] [Inhabited (α × β)] (t : ExtDTreeMap α β cmp) (k : α) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryGT! m k)
    (fun _ _ h => h.constGetEntryGT!_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLE!]
def getEntryLE! [TransCmp cmp] [Inhabited (α × β)] (t : ExtDTreeMap α β cmp) (k : α) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryLE! m k)
    (fun _ _ h => h.constGetEntryLE!_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLT!]
def getEntryLT! [TransCmp cmp] [Inhabited (α × β)] (t : ExtDTreeMap α β cmp) (k : α) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryLT! m k)
    (fun _ _ h => h.constGetEntryLT!_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGED]
def getEntryGED [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryGED m k fallback)
    (fun _ _ h => h.constGetEntryGED_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryGTD]
def getEntryGTD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryGTD m k fallback)
    (fun _ _ h => h.constGetEntryGTD_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLED]
def getEntryLED [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryLED m k fallback)
    (fun _ _ h => h.constGetEntryLED_eq)

@[inline, inherit_doc ExtDTreeMap.getEntryLTD]
def getEntryLTD [TransCmp cmp] (t : ExtDTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  t.lift (fun m => DTreeMap.Const.getEntryLTD m k fallback)
    (fun _ _ h => h.constGetEntryLTD_eq)

end Const

variable {δ : Type w} {m : Type w → Type w₂} [Monad m] [LawfulMonad m]

@[inline, inherit_doc DTreeMap.filter]
def filter (f : (a : α) → β a → Bool) (t : ExtDTreeMap α β cmp) : ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (m.filter f))
    (fun _ _ h => sound (h.filter f))

@[inline, inherit_doc DTreeMap.filterMap]
def filterMap (f : (a : α) → β a → Option (γ a)) (t : ExtDTreeMap α β cmp) : ExtDTreeMap α γ cmp :=
  t.lift (fun m => mk (m.filterMap f))
    (fun _ _ h => sound (h.filterMap f))

@[inline, inherit_doc DTreeMap.map]
def map (f : (a : α) → β a → γ a) (t : ExtDTreeMap α β cmp) : ExtDTreeMap α γ cmp :=
  t.lift (fun m => mk (m.map f))
    (fun _ _ h => sound (h.map f))

@[inline, inherit_doc DTreeMap.foldlM]
def foldlM [TransCmp cmp] (f : δ → (a : α) → β a → m δ) (init : δ) (t : ExtDTreeMap α β cmp) : m δ :=
  t.lift (fun m => m.foldlM f init) (fun _ _ h => h.foldlM_eq)

@[inline, inherit_doc DTreeMap.foldl]
def foldl [TransCmp cmp] (f : δ → (a : α) → β a → δ) (init : δ) (t : ExtDTreeMap α β cmp) : δ :=
  t.lift (fun m => m.foldl f init) (fun _ _ h => h.foldl_eq)

@[inline, inherit_doc DTreeMap.foldrM]
def foldrM [TransCmp cmp] (f : (a : α) → β a → δ → m δ) (init : δ) (t : ExtDTreeMap α β cmp) : m δ :=
  t.lift (fun m => m.foldrM f init) (fun _ _ h => h.foldrM_eq)

@[inline, inherit_doc DTreeMap.foldr]
def foldr [TransCmp cmp] (f : (a : α) → β a → δ → δ) (init : δ) (t : ExtDTreeMap α β cmp) : δ :=
  t.lift (fun m => m.foldr f init) (fun _ _ h => h.foldr_eq)

@[inline, inherit_doc DTreeMap.partition]
def partition [TransCmp cmp] (f : (a : α) → β a → Bool)
    (t : ExtDTreeMap α β cmp) : ExtDTreeMap α β cmp × ExtDTreeMap α β cmp :=
  t.foldl (init := (∅, ∅)) fun ⟨l, r⟩ a b =>
    if f a b then
      (l.insert a b, r)
    else
      (l, r.insert a b)

@[inline, inherit_doc DTreeMap.forM]
def forM [TransCmp cmp] (f : (a : α) → β a → m PUnit) (t : ExtDTreeMap α β cmp) : m PUnit :=
  t.lift (fun m => m.forM f) (fun _ _ h => h.forM_eq (f := fun x => f x.1 x.2))

@[inline, inherit_doc DTreeMap.forIn]
def forIn [TransCmp cmp] (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : ExtDTreeMap α β cmp) : m δ :=
  t.lift (fun m => m.forIn f init) (fun _ _ h => h.forIn_eq (f := fun x => f x.1 x.2))

instance [TransCmp cmp] [Monad m] [LawfulMonad m] : ForM m (ExtDTreeMap α β cmp) ((a : α) × β a) where
  forM t f := forM (fun a b => f ⟨a, b⟩) t

instance [TransCmp cmp] [Monad m] [LawfulMonad m] : ForIn m (ExtDTreeMap α β cmp) ((a : α) × β a) where
  forIn m init f := forIn (fun a b acc => f ⟨a, b⟩ acc) init m

namespace Const

variable {β : Type v}

/-!
We do not define `ForM` and `ForIn` instances that are specialized to constant `β`. Instead, we
define uncurried versions of `forM` and `forIn` that will be used in the `Const` lemmas and to
define the `ForM` and `ForIn` instances for `ExtDTreeMap`.
-/

@[inline, inherit_doc ExtDTreeMap.forM]
def forMUncurried [TransCmp cmp] (f : α × β → m PUnit) (t : ExtDTreeMap α β cmp) : m PUnit :=
  t.forM fun a b => f ⟨a, b⟩

@[inline, inherit_doc ExtDTreeMap.forIn]
def forInUncurried [TransCmp cmp] (f : α × β → δ → m (ForInStep δ)) (init : δ) (t : ExtDTreeMap α β cmp) : m δ :=
  t.forIn (fun a b acc => f ⟨a, b⟩ acc) init

end Const

@[inline, inherit_doc DTreeMap.any]
def any [TransCmp cmp] (t : ExtDTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool :=
  t.lift (fun m => m.any p) (fun _ _ h => h.any_eq)

@[inline, inherit_doc DTreeMap.all]
def all [TransCmp cmp] (t : ExtDTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool :=
  t.lift (fun m => m.all p) (fun _ _ h => h.all_eq)

@[inline, inherit_doc DTreeMap.keys]
def keys [TransCmp cmp] (t : ExtDTreeMap α β cmp) : List α :=
  t.lift (fun m => m.keys) (fun _ _ h => h.keys_eq)

@[inline, inherit_doc DTreeMap.keysArray]
def keysArray [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Array α :=
  t.lift (fun m => m.keysArray) (fun _ _ h => h.keysArray_eq)

@[inline, inherit_doc DTreeMap.values]
def values [TransCmp cmp] {β : Type v} (t : ExtDTreeMap α β cmp) : List β :=
  t.lift (fun m => m.values) (fun _ _ h => h.values_eq)

@[inline, inherit_doc DTreeMap.valuesArray]
def valuesArray [TransCmp cmp] {β : Type v} (t : ExtDTreeMap α β cmp) : Array β :=
  t.lift (fun m => m.valuesArray) (fun _ _ h => h.valuesArray_eq)

@[inline, inherit_doc DTreeMap.toList]
def toList [TransCmp cmp] (t : ExtDTreeMap α β cmp) : List ((a : α) × β a) :=
  t.lift (fun m => m.toList) (fun _ _ h => h.toList_eq)

@[inline, inherit_doc DTreeMap.ofList]
def ofList (l : List ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) :
    ExtDTreeMap α β cmp :=
  mk (.ofList l cmp)

@[inline, inherit_doc DTreeMap.toArray]
def toArray [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Array ((a : α) × β a) :=
  t.lift (fun m => m.toArray) (fun _ _ h => h.toArray_eq)

@[inline, inherit_doc DTreeMap.ofArray]
def ofArray (a : Array ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) :
    ExtDTreeMap α β cmp :=
  mk (.ofArray a cmp)

@[inline, inherit_doc DTreeMap.modify]
def modify [TransCmp cmp] [LawfulEqCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (f : β a → β a) :
    ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (m.modify a f))
    (fun _ _ h => sound (h.modify a f))

@[inline, inherit_doc DTreeMap.alter]
def alter [TransCmp cmp] [LawfulEqCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (f : Option (β a) → Option (β a)) :
    ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (m.alter a f))
    (fun _ _ h => sound (h.alter a f))

@[inline, inherit_doc DTreeMap.mergeWith]
def mergeWith [TransCmp cmp] [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : ExtDTreeMap α β cmp) :
    ExtDTreeMap α β cmp :=
  t₁.liftOn₂ t₂ (fun m₁ m₂ => mk (m₁.mergeWith mergeFn m₂))
    (fun _ _ _ _ h₁ h₂ => sound (h₁.mergeWith mergeFn h₂))

namespace Const

variable {β : Type v}

@[inline, inherit_doc ExtDTreeMap.toList]
def toList [TransCmp cmp] (t : ExtDTreeMap α β cmp) : List (α × β) :=
  t.lift (fun m => DTreeMap.Const.toList m)
    (fun _ _ h => h.constToList_eq)

@[inline, inherit_doc ExtDTreeMap.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering := by exact compare) : ExtDTreeMap α β cmp :=
  mk (DTreeMap.Const.ofList l cmp)

@[inline, inherit_doc ExtDTreeMap.toArray]
def toArray [TransCmp cmp] (t : ExtDTreeMap α β cmp) : Array (α × β) :=
  t.lift (fun m => DTreeMap.Const.toArray m)
    (fun _ _ h => h.constToArray_eq)

@[inline, inherit_doc ExtDTreeMap.ofList]
def ofArray (a : Array (α × β)) (cmp : α → α → Ordering := by exact compare) : ExtDTreeMap α β cmp :=
  mk (DTreeMap.Const.ofArray a cmp)

@[inline, inherit_doc DTreeMap.Const.unitOfList]
def unitOfList (l : List α) (cmp : α → α → Ordering := by exact compare) : ExtDTreeMap α Unit cmp :=
  mk (DTreeMap.Const.unitOfList l cmp)

@[inline, inherit_doc DTreeMap.Const.unitOfArray]
def unitOfArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : ExtDTreeMap α Unit cmp :=
  mk (DTreeMap.Const.unitOfArray a cmp)

@[inline, inherit_doc ExtDTreeMap.modify]
def modify [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (f : β → β) : ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (DTreeMap.Const.modify m a f))
    (fun _ _ h => sound (h.constModify a f))

@[inline, inherit_doc ExtDTreeMap.alter]
def alter [TransCmp cmp] (t : ExtDTreeMap α β cmp) (a : α) (f : Option β → Option β) : ExtDTreeMap α β cmp :=
  t.lift (fun m => mk (DTreeMap.Const.alter m a f))
    (fun _ _ h => sound (h.constAlter a f))

@[inline, inherit_doc ExtDTreeMap.mergeWith]
def mergeWith [TransCmp cmp] (mergeFn : α → β → β → β) (t₁ t₂ : ExtDTreeMap α β cmp) : ExtDTreeMap α β cmp :=
  t₁.liftOn₂ t₂ (fun m₁ m₂ => mk (DTreeMap.Const.mergeWith mergeFn m₁ m₂))
    (fun _ _ _ _ h₁ h₂ => sound (h₁.constMergeWith mergeFn h₂))

end Const

@[inline, inherit_doc DTreeMap.insertMany]
def insertMany [TransCmp cmp] {ρ} [ForIn Id ρ ((a : α) × β a)] (t : ExtDTreeMap α β cmp) (l : ρ) :
    ExtDTreeMap α β cmp := Id.run do
  let mut acc : { a // ∀ P : _ → Prop, P t → (∀ t a b, P t → P (t.insert a b)) → P a } :=
    ⟨t, fun _ h _ => h⟩
  for ⟨a, b⟩ in l do
    acc := ⟨acc.1.insert a b, fun P h h' => h' acc.1 a b (acc.2 P h h')⟩
  return acc.1

@[inline, inherit_doc DTreeMap.eraseMany]
def eraseMany [TransCmp cmp] {ρ} [ForIn Id ρ α] (t : ExtDTreeMap α β cmp) (l : ρ) :
    ExtDTreeMap α β cmp := Id.run do
  let mut acc : { a // ∀ P : _ → Prop, P t → (∀ t a, P t → P (t.erase a)) → P a } :=
    ⟨t, fun _ h _ => h⟩
  for a in l do
    acc := ⟨acc.1.erase a, fun P h h' => h' acc.1 a (acc.2 P h h')⟩
  return acc.1

namespace Const

variable {β : Type v}

@[inline, inherit_doc ExtDTreeMap.insertMany]
def insertMany [TransCmp cmp] {ρ} [ForIn Id ρ (α × β)] (t : ExtDTreeMap α β cmp) (l : ρ) :
    ExtDTreeMap α β cmp := Id.run do
  let mut acc : { a // ∀ P : _ → Prop, P t → (∀ t a b, P t → P (t.insert a b)) → P a } :=
    ⟨t, fun _ h _ => h⟩
  for ⟨a, b⟩ in l do
    acc := ⟨acc.1.insert a b, fun P h h' => h' acc.1 a b (acc.2 P h h')⟩
  return acc.1

@[inline, inherit_doc DTreeMap.Const.insertManyIfNewUnit]
def insertManyIfNewUnit [TransCmp cmp] {ρ} [ForIn Id ρ α] (t : ExtDTreeMap α Unit cmp) (l : ρ) :
    ExtDTreeMap α Unit cmp := Id.run do
  let mut acc : { a // ∀ P : _ → Prop, P t → (∀ t a, P t → P (t.insertIfNew a ())) → P a } :=
    ⟨t, fun _ h _ => h⟩
  for a in l do
    acc := ⟨acc.1.insertIfNew a (), fun P h h' => h' acc.1 a (acc.2 P h h')⟩
  return acc.1

end Const

@[inline, inherit_doc DTreeMap.union]
def union [TransCmp cmp] (m₁ m₂ : ExtDTreeMap α β cmp) : ExtDTreeMap α β cmp := lift₂ (fun x y : DTreeMap α β cmp => mk (x.union y))
  (fun a b c d equiv₁ equiv₂ => by
    simp only [DTreeMap.union_eq, mk'.injEq]
    apply Quotient.sound
    apply DTreeMap.Equiv.union_congr
    . exact equiv₁
    . exact equiv₂) m₁ m₂

instance [TransCmp cmp] : Union (ExtDTreeMap α β cmp) := ⟨union⟩

@[inline, inherit_doc DTreeMap.union]
def inter [TransCmp cmp] (m₁ m₂ : ExtDTreeMap α β cmp) : ExtDTreeMap α β cmp := lift₂ (fun x y : DTreeMap α β cmp => mk (x.inter y))
  (fun a b c d equiv₁ equiv₂ => by
    simp only [DTreeMap.inter_eq, mk'.injEq]
    apply Quotient.sound
    apply DTreeMap.Equiv.inter_congr
    . exact equiv₁
    . exact equiv₂) m₁ m₂

instance [TransCmp cmp] : Inter (ExtDTreeMap α β cmp) := ⟨inter⟩

instance [LawfulEqCmp cmp] [TransCmp cmp] [∀ k, BEq (β k)] : BEq (ExtDTreeMap α β cmp) where
  beq := lift₂ (fun x y : DTreeMap α β cmp => x.beq y) fun _ _ _ _ => DTreeMap.Equiv.beq_congr

instance [LawfulEqCmp cmp] [TransCmp cmp] [∀ k, BEq (β k)] [∀ k, ReflBEq (β k)] : ReflBEq (ExtDTreeMap α β cmp) where
  rfl {a} := a.inductionOn fun _ => DTreeMap.Equiv.beq <| DTreeMap.Equiv.rfl

instance [LawfulEqCmp cmp] [TransCmp cmp] [∀ k, BEq (β k)] [∀ k, LawfulBEq (β k)] : LawfulBEq (ExtDTreeMap α β cmp) where
  eq_of_beq {a} {b} := a.inductionOn₂ b fun _ _ h => sound <| DTreeMap.equiv_of_beq h

instance {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp] [∀ k, BEq (β k)] [∀ k, LawfulBEq (β k)] : DecidableEq (ExtDTreeMap α β cmp) :=
  fun _ _ => decidable_of_iff _ beq_iff_eq

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.beq]
def beq [TransCmp cmp] [BEq β] (m₁ m₂ : ExtDTreeMap α (fun _ => β) cmp) : Bool := lift₂ (fun x y : DTreeMap α (fun _ => β) cmp => DTreeMap.Const.beq x y)
  (fun _ _ _ _ => DTreeMap.Const.Equiv.beq_congr) m₁ m₂

theorem beq_of_eq [TransCmp cmp] [BEq β] [ReflBEq β] (m₁ m₂ : ExtDTreeMap α (fun _ => β) cmp) : m₁ = m₂ → Const.beq m₁ m₂ :=
  m₁.inductionOn₂ m₂ fun _ _ h => DTreeMap.Const.Equiv.beq <| exact h

theorem eq_of_beq [TransCmp cmp] [LawfulEqCmp cmp] [BEq β] [LawfulBEq β] (m₁ m₂ : ExtDTreeMap α (fun _ => β) cmp) : Const.beq m₁ m₂ → m₁ = m₂ :=
  m₁.inductionOn₂ m₂ fun _ _ h => sound <| DTreeMap.Const.equiv_of_beq h

end Const
@[inline, inherit_doc DTreeMap.diff]
def diff [TransCmp cmp] (m₁ m₂ : ExtDTreeMap α β cmp) : ExtDTreeMap α β cmp := lift₂ (fun x y : DTreeMap α β cmp => mk (x.diff y))
  (fun a b c d equiv₁ equiv₂ => by
    simp only [DTreeMap.diff_eq, mk'.injEq]
    apply Quotient.sound
    apply DTreeMap.Equiv.diff_congr
    . exact equiv₁
    . exact equiv₂) m₁ m₂

instance [TransCmp cmp] : SDiff (ExtDTreeMap α β cmp) := ⟨diff⟩

instance [TransCmp cmp] [Repr α] [(a : α) → Repr (β a)] : Repr (ExtDTreeMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("Std.ExtDTreeMap.ofList " ++ repr m.toList) prec

end ExtDTreeMap

end Std
