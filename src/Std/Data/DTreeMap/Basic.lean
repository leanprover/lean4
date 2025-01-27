/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.Impl

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}

namespace Std

/--
Proof that the equality of a compare function corresponds
to propositional equality.
-/
class EqOfCmp (α : Type u) (cmp : α → α → Ordering) where
  eq_of_cmp {a a' : α} : cmp a a' = .eq → a = a'

export EqOfCmp (eq_of_cmp)

/--
Proof that the equality of a compare function corresponds
to propositional equality and vice versa.
-/
class LawfulCmpEq (α : Type u) (cmp : α → α → Ordering) extends EqOfCmp α cmp where
  cmp_rfl {a : α} : cmp a a = .eq

export LawfulCmpEq (cmp_rfl)

attribute [simp] cmp_rfl

/-- Binary search trees. -/
structure DTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Internal.Impl α β
  /-- Internal implementation detail of the tree map. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DTreeMap

@[inline]
def isEmpty (t : DTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

/-- Creates a new empty tree map. -/
@[inline]
def empty : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

/-- Inserts the mapping `(a, b)` into the tree map. -/
@[inline]
def insert (l : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.insert a b l.wf.balanced).impl, .insert l.wf⟩

/-- Returns `true` if the given key is present in the map. -/
@[inline]
def contains (l : DTreeMap α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; l.inner.contains a

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

universe w in
@[inline, inherit_doc DHashMap.fold] def fold {γ : Type w}
    (f : γ → (a : α) → β a → γ) (init : γ) (b : DTreeMap α β cmp) : γ :=
  b.inner.foldl f init

@[inline] def fromArray (l : Array ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) empty

@[inline] def get? [i : LawfulCmpEq α cmp] (l : DTreeMap α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩
  haveI : ReflOrd α := ⟨i.cmp_rfl⟩
  haveI : LawfulEqOrd α := ⟨i.eq_of_cmp⟩
  Std.DTreeMap.Internal.Impl.get? a l.inner

@[inline] def find? [i : LawfulCmpEq α cmp] (l : DTreeMap α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩
  haveI : ReflOrd α := ⟨i.cmp_rfl⟩
  haveI : LawfulEqOrd α := ⟨i.eq_of_cmp⟩
  Std.DTreeMap.Internal.Impl.get? a l.inner

universe w in
@[inline, inherit_doc DHashMap.forIn] def forIn {m : Type w → Type w} [Monad m]
    {γ : Type w} (f : (a : α) → β a → γ → m (ForInStep γ)) (init : γ) (b : DTreeMap α β cmp) : m γ :=
  b.inner.forIn (fun c a b => f a b c) init

universe w in
instance {m : Type w → Type w} : ForIn m (DTreeMap α β cmp) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

instance : Inhabited (DTreeMap α β cmp) := ⟨empty⟩

instance : Repr (DTreeMap α β cmp) where
  reprPrec _ _ := Format.nil

instance : EmptyCollection (DTreeMap α β cmp) := ⟨empty⟩

end DTreeMap

end Std
