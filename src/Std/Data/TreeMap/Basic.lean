/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Basic
import Std.Data.DTreeMap.Internal.Impl.Operations

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

@[inherit_doc DTreeMap]
structure TreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap α (fun _ => β) cmp

namespace TreeMap

@[inline, inherit_doc DTreeMap.empty]
def empty : TreeMap α β cmp :=
  ⟨DTreeMap.empty⟩

@[inline, inherit_doc DTreeMap.isEmpty]
def isEmpty (t : TreeMap α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.insert]
def insert (l : TreeMap α β cmp) (a : α) (b : β) : TreeMap α β cmp :=
  ⟨l.inner.insert a b⟩

@[inline, inherit_doc DTreeMap.contains]
def contains (l : TreeMap α β cmp) (a : α) : Bool :=
  l.inner.contains a

universe w in
@[inline, inherit_doc DHashMap.fold] def fold {γ : Type w}
    (f : γ → α → β → γ) (init : γ) (b : TreeMap α β cmp) : γ :=
  b.inner.inner.foldl f init

@[inline] def fromArray (l : Array (α × β)) (cmp : α → α → Ordering) : TreeMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) empty

@[inline] def get? (l : TreeMap α β cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩
  Std.DTreeMap.Internal.Impl.Const.Const.get? a l.inner.inner

universe w in
@[inline, inherit_doc DHashMap.forIn] def forIn {m : Type w → Type w} [Monad m]
    {γ : Type w} (f : (a : α) → β → γ → m (ForInStep γ)) (init : γ) (b : TreeMap α β cmp) : m γ :=
  b.inner.inner.forIn (fun c a b => f a b c) init

universe w in
instance {m : Type w → Type w} : ForIn m (TreeMap α β cmp) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f (a, b) acc) init

instance : Membership α (TreeMap α β cmp) where
  mem m a := m.contains a

instance : Inhabited (TreeMap α β cmp) := ⟨empty⟩

instance : Repr (TreeMap α β cmp) where
  reprPrec _ _ := Format.nil

instance : EmptyCollection (TreeMap α β cmp) := ⟨empty⟩

end TreeMap

end Std
