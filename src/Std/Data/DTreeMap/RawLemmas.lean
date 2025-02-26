/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.Lemmas
import Std.Data.DTreeMap.Raw
import Std.Data.DTreeMap.AdditionalOperations

/-!
# Dependent tree map lemmas

This file contains lemmas about `Std.Data.DTreeMap.Raw`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v

namespace Std.DTreeMap.Raw

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap.Raw α β cmp}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

namespace WF

variable {t : Raw α β cmp}

theorem empty : (empty : Raw α β cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.empty⟩

theorem emptyc : (∅ : Raw α β cmp).WF :=
  empty

theorem erase [TransCmp cmp] {a} (h : t.WF) : WF (t.erase a) :=
  ⟨h.out.erase!⟩

theorem insert [TransCmp cmp] {a b} (h : t.WF) : WF (t.insert a b) :=
  ⟨h.out.insert!⟩

theorem insertIfNew [TransCmp cmp] {a b} (h : t.WF) : WF (t.insertIfNew a b) :=
  ⟨h.out.insertIfNew!⟩

theorem containsThenInsert [TransCmp cmp] {a b} (h : t.WF) : WF (t.containsThenInsert a b).2 :=
  ⟨h.out.containsThenInsert!⟩

theorem containsThenInsertIfNew [TransCmp cmp] {a b} (h : t.WF) : WF (t.containsThenInsertIfNew a b).2 :=
  ⟨h.out.containsThenInsertIfNew!⟩

theorem getThenInsertIfNew? [TransCmp cmp] [LawfulEqCmp cmp] {a b} (h : t.WF) :
    WF (t.getThenInsertIfNew? a b).2 :=
  ⟨h.out.getThenInsertIfNew?!⟩

theorem filter! [TransCmp cmp] {f} (h : t.WF) :
    WF (t.filter f) :=
  ⟨h.out.filter!⟩

theorem filterMap! [TransCmp cmp] {f : (a : α) → β a → Option (β a)} (h : t.WF) :
    WF (t.filterMap f) :=
  ⟨h.out.filterMap!⟩

-- Const, partition, insertMany, of, alter, modify, erase

#exit

theorem insertIfNew {a : α} {b : β a} : Unit :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNew! a b⟩

@[inline, inherit_doc DTreeMap.containsThenInsert]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β a) : Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert! a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.containsThenInsertIfNew]
def containsThenInsertIfNew (t : Raw α β cmp) (a : α) (b : β a) :
    Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew! a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.getThenInsertIfNew?]
def getThenInsertIfNew? [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (b : β a) :
    Option (β a) × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.getThenInsertIfNew?! a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.contains]
def contains (t : Raw α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; t.inner.contains a

instance : Membership α (Raw α β cmp) where
  mem t a := t.contains a

instance {t : Raw α β cmp} {a : α} : Decidable (a ∈ t) :=
  inferInstanceAs <| Decidable (t.contains a)

@[inline, inherit_doc DTreeMap.size]
def size (t : Raw α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc DTreeMap.isEmpty]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.erase]
def erase (t : Raw α β cmp) (a : α) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.erase! a⟩

@[inline, inherit_doc DTreeMap.get?]
def get? [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.get? a

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) : Option (β a) :=
  t.get? a

@[inline, inherit_doc DTreeMap.get]
def get [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (h : a ∈ t) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get a h

@[inline, inherit_doc DTreeMap.get!]
def get! [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get! a

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  t.get! a

@[inline, inherit_doc DTreeMap.getD]
def getD [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (fallback : β a) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.getD a fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (fallback : β a) : β a :=
  t.getD a fallback

@[inline, inherit_doc DTreeMap.getKey?]
def getKey? (t : Raw α β cmp) (a : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKey? a

@[inline, inherit_doc DTreeMap.getKey]
def getKey (t : Raw α β cmp) (a : α) (h : a ∈ t) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKey a h

@[inline, inherit_doc DTreeMap.getKey!]
def getKey! [Inhabited α] (t : Raw α β cmp) (a : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKey! a

@[inline, inherit_doc DTreeMap.getKeyD]
def getKeyD (t : Raw α β cmp) (a : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyD a fallback

@[inline, inherit_doc DTreeMap.min?]
def min? (t : Raw α β cmp) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.min?

/-!
We do not provide `min` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.min!]
def min! [Inhabited ((a : α) × β a)] (t : Raw α β cmp) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.min!

@[inline, inherit_doc DTreeMap.minD]
def minD (t : Raw α β cmp) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.minD fallback

@[inline, inherit_doc DTreeMap.max?]
def max? (t : Raw α β cmp) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.max?

/-!
We do not provide `max` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.max!]
def max! [Inhabited ((a : α) × β a)] (t : Raw α β cmp) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.max!

@[inline, inherit_doc DTreeMap.maxD]
def maxD (t : Raw α β cmp) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxD fallback

@[inline, inherit_doc DTreeMap.minKey?]
def minKey? (t : Raw α β cmp) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.minKey?

/-!
We do not provide `minKey` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.minKeyD]
def minKeyD (t : Raw α β cmp) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.minKeyD fallback

@[inline, inherit_doc DTreeMap.minKey!]
def minKey! [Inhabited α] (t : Raw α β cmp) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.minKey!

@[inline, inherit_doc DTreeMap.maxKey?]
def maxKey? (t : Raw α β cmp) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxKey?

/-!
We do not provide `maxKey` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.maxKey!]
def maxKey! [Inhabited α] (t : Raw α β cmp) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxKey!

@[inline, inherit_doc DTreeMap.maxKeyD]
def maxKeyD (t : Raw α β cmp) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxKeyD fallback

@[inline, inherit_doc DTreeMap.entryAtIdx?]
def entryAtIdx? (t : Raw α β cmp) (n : Nat) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.entryAtIdx? n

/-!
We do not provide `entryAtIdx` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.entryAtIdx!]
def entryAtIdx! [Inhabited ((a : α) × β a)] (t : Raw α β cmp) (n : Nat) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.entryAtIdx! n

@[inline, inherit_doc DTreeMap.entryAtIdxD]
def entryAtIdxD (t : Raw α β cmp) (n : Nat) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.entryAtIdxD n fallback

@[inline, inherit_doc DTreeMap.keyAtIndex?]
def keyAtIndex? (t : Raw α β cmp) (n : Nat) : Option α :=
  letI : Ord α := ⟨cmp⟩; Impl.keyAtIndex? t.inner n

/-!
We do not provide `keyAtIndex` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.keyAtIndex!]
def keyAtIndex! [Inhabited α] (t : Raw α β cmp) (n : Nat) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.keyAtIndex! n

@[inline, inherit_doc DTreeMap.keyAtIndexD]
def keyAtIndexD (t : Raw α β cmp) (n : Nat) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.keyAtIndexD n fallback

@[inline, inherit_doc DTreeMap.getEntryGE?]
def getEntryGE? (t : Raw α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGE? k t.inner

@[inline, inherit_doc DTreeMap.getEntryGT?]
def getEntryGT? (t : Raw α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGT? k t.inner

@[inline, inherit_doc DTreeMap.getEntryLE?]
def getEntryLE? (t : Raw α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLE? k t.inner

@[inline, inherit_doc DTreeMap.getEntryLT?]
def getEntryLT? (t : Raw α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLT? k t.inner

/-!
We do not provide `getEntryGE`, `getEntryGT`, `getEntryLE`, `getEntryLT` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.getEntryGE!]
def getEntryGE! [Inhabited ((a : α) × β a)] (t : Raw α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGE! k t.inner

@[inline, inherit_doc DTreeMap.getEntryGT!]
def getEntryGT! [Inhabited ((a : α) × β a)] (t : Raw α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGT! k t.inner

@[inline, inherit_doc DTreeMap.getEntryLE!]
def getEntryLE! [Inhabited ((a : α) × β a)] (t : Raw α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLE! k t.inner

@[inline, inherit_doc DTreeMap.getEntryLT!]
def getEntryLT! [Inhabited ((a : α) × β a)] (t : Raw α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLT! k t.inner

@[inline, inherit_doc DTreeMap.getEntryGED]
def getEntryGED (t : Raw α β cmp) (k : α) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGED k t.inner fallback

@[inline, inherit_doc DTreeMap.getEntryGTD]
def getEntryGTD (t : Raw α β cmp) (k : α) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGTD k t.inner fallback

@[inline, inherit_doc DTreeMap.getEntryLED]
def getEntryLED (t : Raw α β cmp) (k : α) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLED k t.inner fallback

@[inline, inherit_doc DTreeMap.getEntryLTD]
def getEntryLTD (t : Raw α β cmp) (k : α) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLTD k t.inner fallback

@[inline, inherit_doc DTreeMap.getKeyGE?]
def getKeyGE? (t : Raw α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyGE? k

@[inline, inherit_doc DTreeMap.getKeyGT?]
def getKeyGT? (t : Raw α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyGT? k

@[inline, inherit_doc DTreeMap.getKeyLE?]
def getKeyLE? (t : Raw α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyLE? k

@[inline, inherit_doc DTreeMap.getKeyLT?]
def getKeyLT? (t : Raw α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyLT? k

/-!
We do not provide `getKeyGE`, `getKeyGT`, `getKeyLE`, `getKeyLT` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.getKeyGE!]
def getKeyGE! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGE! k t.inner

@[inline, inherit_doc DTreeMap.getKeyGT!]
def getKeyGT! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGT! k t.inner

@[inline, inherit_doc DTreeMap.getKeyLE!]
def getKeyLE! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLE! k t.inner

@[inline, inherit_doc DTreeMap.getKeyLT!]
def getKeyLT! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLT! k t.inner

@[inline, inherit_doc DTreeMap.getKeyGED]
def getKeyGED (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGED k t.inner fallback

@[inline, inherit_doc DTreeMap.getKeyGTD]
def getKeyGTD (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGTD k t.inner fallback

@[inline, inherit_doc DTreeMap.getKeyLED]
def getKeyLED (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLED k t.inner fallback

@[inline, inherit_doc DTreeMap.getKeyLTD]
def getKeyLTD (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLTD k t.inner fallback

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.Const.getThenInsertIfNew?]
def getThenInsertIfNew? (t : Raw α β cmp) (a : α) (b : β) : Option β × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := Impl.Const.getThenInsertIfNew?! a b t.inner
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Const.get?]
def get? (t : Raw α β cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get? t.inner a

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? (t : Raw α β cmp) (a : α) : Option β :=
  get? t a

@[inline, inherit_doc DTreeMap.Const.get]
def get (t : Raw α β cmp) (a : α) (h : a ∈ t) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get t.inner a h

@[inline, inherit_doc DTreeMap.Const.get!]
def get! (t : Raw α β cmp) (a : α) [Inhabited β] : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get! t.inner a

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! (t : Raw α β cmp) (a : α) [Inhabited β] : β :=
  get! t a

@[inline, inherit_doc DTreeMap.Const.getD]
def getD (t : Raw α β cmp) (a : α) (fallback : β) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getD t.inner a fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD (t : Raw α β cmp) (a : α) (fallback : β) : β :=
  getD t a fallback

@[inline, inherit_doc DTreeMap.Const.min?]
def min? (t : Raw α β cmp) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.min? t.inner

/-!
We do not provide `min` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Const.min!]
def min! [Inhabited (α × β)] (t : Raw α β cmp) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.min! t.inner

@[inline, inherit_doc DTreeMap.Const.minD]
def minD (t : Raw α β cmp) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.minD t.inner fallback

@[inline, inherit_doc DTreeMap.Const.max?]
def max? (t : Raw α β cmp) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.max? t.inner

@[inline, inherit_doc DTreeMap.Const.max!]
def max! [Inhabited (α × β)] (t : Raw α β cmp) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.max! t.inner

@[inline, inherit_doc DTreeMap.Const.maxD]
def maxD (t : Raw α β cmp) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.maxD t.inner fallback

@[inline, inherit_doc DTreeMap.Const.entryAtIdx?]
def entryAtIdx? (t : Raw α β cmp) (n : Nat) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.entryAtIdx? t.inner n

/-!
We do not provide `entryAtIdx` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Const.entryAtIdx!]
def entryAtIdx! [Inhabited (α × β)] (t : Raw α β cmp) (n : Nat) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.entryAtIdx! t.inner n

@[inline, inherit_doc DTreeMap.Const.entryAtIdxD]
def entryAtIdxD (t : Raw α β cmp) (n : Nat)
    (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.entryAtIdxD t.inner n fallback

@[inline, inherit_doc DTreeMap.Const.getEntryGE?]
def getEntryGE? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGE? k t.inner

@[inline, inherit_doc DTreeMap.Const.getEntryGT?]
def getEntryGT? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGT? k t.inner

@[inline, inherit_doc DTreeMap.Const.getEntryLE?]
def getEntryLE? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLE? k t.inner

@[inline, inherit_doc DTreeMap.Const.getEntryLT?]
def getEntryLT? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLT? k t.inner

/-!
We do not provide `getEntryGE`, `getEntryGT`, `getEntryLE`, `getEntryLT` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Const.getEntryGE!]
def getEntryGE! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGE! k t.inner

@[inline, inherit_doc DTreeMap.Const.getEntryGT!]
def getEntryGT! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGT! k t.inner

@[inline, inherit_doc DTreeMap.Const.getEntryLE!]
def getEntryLE! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLE! k t.inner

@[inline, inherit_doc DTreeMap.Const.getEntryLT!]
def getEntryLT! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLT! k t.inner

@[inline, inherit_doc DTreeMap.Const.getEntryGED]
def getEntryGED (t : Raw α β cmp) (k : α) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGED k t.inner fallback

@[inline, inherit_doc DTreeMap.Const.getEntryGTD]
def getEntryGTD (t : Raw α β cmp) (k : α) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGTD k t.inner fallback

@[inline, inherit_doc DTreeMap.Const.getEntryLED]
def getEntryLED (t : Raw α β cmp) (k : α) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLED k t.inner fallback

@[inline, inherit_doc DTreeMap.Const.getEntryLTD]
def getEntryLTD (t : Raw α β cmp) (k : α) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLTD k t.inner fallback

end Const

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc DTreeMap.filter]
def filter (f : (a : α) → β a → Bool) (t : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filter! f⟩

@[inline, inherit_doc DTreeMap.foldlM]
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc foldlM, deprecated foldlM (since := "2025-02-12")]
def foldM (f : δ → (a : α) → β a → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.foldlM f init

@[inline, inherit_doc DTreeMap.foldl]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc foldl, deprecated foldl (since := "2025-02-12")]
def fold (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.foldl f init

@[inline, inherit_doc DTreeMap.foldrM]
def foldrM (f : δ → (a : α) → β a → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldrM f init

@[inline, inherit_doc DTreeMap.foldr]
def foldr (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.inner.foldr f init

@[inline, inherit_doc foldr, deprecated foldr (since := "2025-02-12")]
def revFold (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  foldr f init t

@[inline, inherit_doc DTreeMap.partition]
def partition (f : (a : α) → β a → Bool) (t : Raw α β cmp) : Raw α β cmp × Raw α β cmp :=
  t.foldl (init := (∅, ∅)) fun ⟨l, r⟩ a b =>
    if f a b then
      (l.insert a b, r)
    else
      (l, r.insert a b)

@[inline, inherit_doc DTreeMap.forM]
def forM (f : (a : α) → β a → m PUnit) (t : Raw α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc DTreeMap.forIn]
def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.forIn (fun c a b => f a b c) init

instance : ForM m (Raw α β cmp) ((a : α) × β a) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β cmp) ((a : α) × β a) where
  forIn t init f := t.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc DTreeMap.any]
def any (t : Raw α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b then return true
  return false

@[inline, inherit_doc DTreeMap.all]
def all (t : Raw α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b = false then return false
  return true

@[inline, inherit_doc DTreeMap.keys]
def keys (t : Raw α β cmp) : List α :=
  t.inner.keys

@[inline, inherit_doc DTreeMap.keysArray]
def keysArray (t : Raw α β cmp) : Array α :=
  t.inner.keysArray

@[inline, inherit_doc DTreeMap.values]
def values {β : Type v} (t : Raw α β cmp) : List β :=
  t.inner.values

@[inline, inherit_doc DTreeMap.valuesArray]
def valuesArray {β : Type v} (t : Raw α β cmp) : Array β :=
  t.inner.valuesArray

@[inline, inherit_doc DTreeMap.toList]
def toList (t : Raw α β cmp) : List ((a : α) × β a) :=
  t.inner.toList

/-- Transforms a list of mappings into a tree map. -/
@[inline]
def ofList (l : List ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.ofList l⟩

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-12")]
def fromList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofList l cmp

@[inline, inherit_doc DTreeMap.toArray]
def toArray (t : Raw α β cmp) : Array ((a : α) × β a) :=
  t.inner.toArray

/-- Transforms an array of mappings into a tree map. -/
@[inline]
def ofArray (a : Array ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.ofArray a⟩

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-12")]
def fromArray (a : Array ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofArray a cmp

@[inline, inherit_doc DTreeMap.modify]
def modify [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (f : β a → β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.modify a f⟩

@[inline, inherit_doc DTreeMap.alter]
def alter [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (f : Option (β a) → Option (β a)) :
    Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.alter! a f⟩

@[inline, inherit_doc DTreeMap.mergeWith]
def mergeWith [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : Raw α β cmp) :
    Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t₁.inner.mergeWith! mergeFn t₂.inner⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : Raw α β cmp) :
    Raw α β cmp :=
  mergeWith mergeFn t₁ t₂

namespace Const
open Internal (Impl)

variable {β : Type v}

@[inline, inherit_doc DTreeMap.Const.toList]
def toList (t : Raw α β cmp) : List (α × β) :=
  Impl.Const.toList t.inner

@[inline, inherit_doc DTreeMap.Const.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.ofList l⟩

@[inline, inherit_doc DTreeMap.Const.unitOfList]
def unitOfList (l : List α) (cmp : α → α → Ordering := by exact compare) : Raw α Unit cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.unitOfList l⟩

@[inline, inherit_doc DTreeMap.Const.toArray]
def toArray (t : Raw α β cmp) : Array (α × β) :=
  Impl.Const.toArray t.inner

@[inline, inherit_doc DTreeMap.Const.ofArray]
def ofArray (a : Array (α × β)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.ofArray a⟩

@[inline, inherit_doc DTreeMap.Const.ofArray]
def unitOfArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : Raw α Unit cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.unitOfArray a⟩

@[inline, inherit_doc DTreeMap.Const.modify]
def modify (t : Raw α β cmp) (a : α) (f : β → β) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.modify a f t.inner⟩

@[inline, inherit_doc DTreeMap.Const.alter]
def alter (t : Raw α β cmp) (a : α) (f : Option β → Option β) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.alter! a f t.inner⟩

@[inline, inherit_doc DTreeMap.Const.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.mergeWith! mergeFn t₁.inner t₂.inner⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  mergeWith mergeFn t₁ t₂

end Const

@[inline, inherit_doc DTreeMap.insertMany]
def insertMany {ρ} [ForIn Id ρ ((a : α) × β a)] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertMany! l⟩

@[inline, inherit_doc DTreeMap.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.eraseMany! l⟩

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.Const.insertMany]
def insertMany {ρ} [ForIn Id ρ (α × β)] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.insertMany! t.inner l⟩

@[inline, inherit_doc DTreeMap.Const.insertManyIfNewUnit]
def insertManyIfNewUnit {ρ} [ForIn Id ρ α] (t : Raw α Unit cmp) (l : ρ) : Raw α Unit cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.insertManyIfNewUnit! t.inner l⟩

end Const

end WF

private theorem ext {t t' : Raw α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : DTreeMap.Raw α β cmp).isEmpty :=
  Impl.isEmpty_empty

@[simp]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).isEmpty = false :=
  Impl.isEmpty_insert! h

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr h hab

@[simp]
theorem contains_emptyc {k : α} : (∅ : Raw α β cmp).contains k = false :=
  Impl.contains_empty

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : Raw α β cmp) :=
  Impl.not_mem_empty

theorem contains_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → t.contains a = false :=
  Impl.contains_of_isEmpty h

theorem not_mem_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → a ∉ t :=
  Impl.not_mem_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  Impl.isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  Impl.isEmpty_eq_false_iff_exists_mem h

theorem isEmpty_iff_forall_contains [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  Impl.isEmpty_iff_forall_contains h

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  Impl.isEmpty_iff_forall_not_mem h

@[simp]
theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : Raw α β cmp).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insert! h

@[simp]
theorem mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insert! h

theorem contains_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).contains k :=
  Impl.contains_insert!_self h

theorem mem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insert k v :=
  Impl.mem_insert!_self h

theorem contains_of_contains_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insert! h

theorem mem_of_mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.mem_of_mem_insert! h

@[simp]
theorem size_emptyc : (∅ : Raw α β cmp).size = 0 :=
  Impl.size_empty

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  Impl.isEmpty_eq_size_eq_zero h.out

theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  Impl.size_insert! h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert k v).size :=
  Impl.size_le_size_insert! h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size ≤ t.size + 1 :=
  Impl.size_insert!_le h

@[simp]
theorem erase_emptyc {k : α} :
    (∅ : Raw α β cmp).erase k = ∅ :=
  ext <| Impl.erase!_empty (instOrd := ⟨cmp⟩) (k := k)

@[simp]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  Impl.isEmpty_erase! h

@[simp]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  Impl.contains_erase! h

@[simp]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  Impl.mem_erase! h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  Impl.contains_of_contains_erase! h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  Impl.mem_of_mem_erase! h

theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  Impl.size_erase! h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  Impl.size_erase!_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  Impl.size_le_size_erase! h

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).1 = t.contains k :=
  Impl.containsThenInsert!_fst h

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| Impl.containsThenInsert!_snd h

@[simp]
theorem containsThenInsertIfNew_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  Impl.containsThenInsertIfNew!_fst h

@[simp]
theorem containsThenInsertIfNew_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| Impl.containsThenInsertIfNew!_snd h

@[simp]
theorem get?_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (∅ : DTreeMap α β cmp).get? a = none :=
  Impl.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none :=
  Impl.get?_of_isEmpty h

theorem get?_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v).get? a =
      if h : cmp k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a :=
  Impl.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get? k = some v :=
  Impl.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome :=
  Impl.contains_eq_isSome_get? h

theorem mem_iff_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  Impl.mem_iff_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none :=
  Impl.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  Impl.get?_eq_none h

theorem get?_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  Impl.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).get? k = none :=
  Impl.get?_erase!_self h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem get?_emptyc [TransCmp cmp] {a : α} :
    get? (∅ : Raw α β cmp) a = none :=
  Impl.Const.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → get? t a = none :=
  Impl.Const.get?_of_isEmpty h

theorem get?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert k v) a =
      if cmp k a = .eq then some v else get? t a :=
  Impl.Const.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get? (t.insert k v) k = some v :=
  Impl.Const.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (get? t a).isSome :=
  Impl.Const.contains_eq_isSome_get? h

theorem mem_iff_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (get? t a).isSome :=
  Impl.Const.mem_iff_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → get? t a = none :=
  Impl.Const.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → get? t a = none :=
  Impl.Const.get?_eq_none h

theorem get?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    get? (t.erase k) a = if cmp k a = .eq then none else get? t a :=
  Impl.Const.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    get? (t.erase k) k = none :=
  Impl.Const.get?_erase!_self h

theorem get?_eq_get? [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {a : α} : get? t a = t.get? a :=
  Impl.Const.get?_eq_get? h

theorem get?_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get? t a = get? t b :=
  Impl.Const.get?_congr h hab

end Const

theorem get_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v).get a h₁ =
      if h₂ : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (mem_of_mem_insert h h₁ h₂) :=
  Impl.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get k (mem_insert_self h) = v :=
  Impl.get_insert!_self h

@[simp]
theorem get_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h h') :=
  Impl.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  Impl.get?_eq_some_get h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem get_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert k v) a h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (mem_of_mem_insert h h₁ h₂) :=
  Impl.Const.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get (t.insert k v) k (mem_insert_self h) = v :=
  Impl.Const.get_insert!_self h

@[simp]
theorem get_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    get (t.erase k) a h' = get t a (mem_of_mem_erase h h') :=
  Impl.Const.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    get? t a = some (get t a h') :=
  Impl.Const.get?_eq_some_get h

theorem get_eq_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    get t a h' = t.get a h' :=
  Impl.Const.get_eq_get h

theorem get_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) {h'} :
    get t a h' = get t b ((mem_congr h hab).mp h') :=
  Impl.Const.get_congr h hab

end Const

@[simp]
theorem get!_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.isEmpty = true → t.get! a = default :=
  Impl.get!_of_isEmpty h

theorem get!_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)]
    {v : β k} : (t.insert k v).get! a =
      if h : cmp k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a :=
  Impl.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)]
    {b : β a} : (t.insert a b).get! a = b :=
  Impl.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default :=
  Impl.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default :=
  Impl.get!_eq_default h

theorem get!_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  Impl.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase k).get! k = default :=
  Impl.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = true → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get!_of_contains h

theorem get?_eq_some_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! :=
  Impl.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] {h'} :
    t.get a h' = t.get! a :=
  Impl.get_eq_get! h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem get!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.Const.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → get! t a = default :=
  Impl.Const.get!_of_isEmpty h

theorem get!_insert [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert k v) a = if cmp k a = .eq then v else get! t a :=
  Impl.Const.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} {v : β} :
    get! (t.insert k v) k = v :=
  Impl.Const.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → get! t a = default :=
  Impl.Const.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → get! t a = default :=
  Impl.Const.get!_eq_default h

theorem get!_erase [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase k) a = if cmp k a = .eq then default else get! t a :=
  Impl.Const.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase k) k = default :=
  Impl.Const.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = true → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    a ∈ t → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = (get? t a).get! :=
  Impl.Const.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} {h'} :
    get t a h' = get! t a :=
  Impl.Const.get_eq_get! h

theorem get!_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = t.get! a :=
  Impl.Const.get!_eq_get! h

theorem get!_congr [TransCmp cmp] [Inhabited β] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get! t a = get! t b :=
  Impl.Const.get!_congr h hab

end Const

@[simp]
theorem getD_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    (∅ : DTreeMap α β cmp).getD a fallback = fallback :=
  Impl.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  Impl.getD_of_isEmpty h

theorem getD_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v).getD a fallback =
      if h : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback :=
  Impl.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert a b).getD a fallback = b :=
  Impl.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = false → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback h

theorem getD_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase k).getD a fallback = if cmp k a = .eq then fallback else t.getD a fallback :=
  Impl.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase k).getD k fallback = fallback :=
  Impl.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    {fallback : β a} : t.contains a = true → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback :=
  Impl.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} {h'} :
    t.get a h' = t.getD a fallback :=
  Impl.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default :=
  Impl.get!_eq_getD_default h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : Raw α β cmp) a fallback = fallback :=
  Impl.Const.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  Impl.Const.getD_of_isEmpty h

theorem getD_insert [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  Impl.Const.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  Impl.Const.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback h

theorem getD_erase [TransCmp cmp] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  Impl.Const.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  Impl.Const.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback :=
  Impl.Const.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} {h'} :
    get t a h' = getD t a fallback :=
  Impl.Const.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = getD t a default :=
  Impl.Const.get!_eq_getD_default h

theorem getD_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback :=
  Impl.Const.getD_eq_getD h

theorem getD_congr [TransCmp cmp] (h : t.WF) {a b : α} {fallback : β} (hab : cmp a b = .eq) :
    getD t a fallback = getD t b fallback :=
  Impl.Const.getD_congr h hab

end Const

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : DTreeMap α β cmp).getKey? a = none :=
  Impl.getKey?_empty

theorem getKey?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  Impl.getKey?_of_isEmpty h

theorem getKey?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  Impl.getKey?_insert! h

@[simp]
theorem getKey?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).getKey? k = some k :=
  Impl.getKey?_insert!_self h

theorem contains_eq_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  Impl.contains_eq_isSome_getKey? h

theorem mem_iff_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  Impl.mem_iff_isSome_getKey? h

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey? a = none :=
  Impl.getKey?_eq_none_of_contains_eq_false h

theorem getKey?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  Impl.getKey?_eq_none h

theorem getKey?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  Impl.getKey?_erase! h

@[simp]
theorem getKey?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).getKey? k = none :=
  Impl.getKey?_erase!_self h

theorem getKey_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then
        k
      else
        t.getKey a (mem_of_mem_insert h h₁ h₂) :=
  Impl.getKey_insert! h

@[simp]
theorem getKey_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).getKey k (mem_insert_self h) = k :=
  Impl.getKey_insert!_self h

@[simp]
theorem getKey_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h h') :=
  Impl.getKey_erase! h

theorem getKey?_eq_some_getKey [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') :=
  Impl.getKey?_eq_some_getKey h

@[simp]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : DTreeMap α β cmp).getKey! a = default :=
  Impl.getKey!_empty

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  Impl.getKey!_of_isEmpty h

theorem getKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  Impl.getKey!_insert! h

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {b : β a} :
    (t.insert a b).getKey! a = a :=
  Impl.getKey!_insert!_self h

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey! a = default :=
  Impl.getKey!_eq_default_of_contains_eq_false h

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  Impl.getKey!_eq_default h

theorem getKey!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  Impl.getKey!_erase! h

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase k).getKey! k = default :=
  Impl.getKey!_erase!_self h

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey!_of_contains h

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey! h

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  Impl.getKey!_eq_get!_getKey? h

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {h'} :
    t.getKey a h' = t.getKey! a :=
  Impl.getKey_eq_getKey! h

@[simp]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : DTreeMap α β cmp).getKeyD a fallback = fallback :=
  Impl.getKeyD_empty

theorem getKeyD_of_isEmpty [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_of_isEmpty h

theorem getKeyD_insert [TransCmp cmp] (h : t.WF) {k a fallback : α} {v : β k} :
    (t.insert k v).getKeyD a fallback = if cmp k a = .eq then k else t.getKeyD a fallback :=
  Impl.getKeyD_insert! h

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] (h : t.WF) {a fallback : α} {b : β a} :
    (t.insert a b).getKeyD a fallback = a :=
  Impl.getKeyD_insert!_self h

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback_of_contains_eq_false h

theorem getKeyD_eq_fallback [TransCmp cmp] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback h

theorem getKeyD_erase [TransCmp cmp] (h : t.WF) {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  Impl.getKeyD_erase! h

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] (h : t.WF) {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  Impl.getKeyD_erase!_self h

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD_of_contains h

theorem getKey?_eq_some_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} :
    a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD h

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  Impl.getKeyD_eq_getD_getKey? h

theorem getKey_eq_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} {h'} :
    t.getKey a h' = t.getKeyD a fallback :=
  Impl.getKey_eq_getKeyD h

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = t.getKeyD a default :=
  Impl.getKey!_eq_getKeyD_default h

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).isEmpty = false :=
  Impl.isEmpty_insertIfNew! h

@[simp]
theorem contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insertIfNew! h

@[simp]
theorem mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insertIfNew! h

theorem contains_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).contains k :=
  Impl.contains_insertIfNew!_self h

theorem mem_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insertIfNew k v :=
  Impl.mem_insertIfNew!_self h

theorem contains_of_contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insertIfNew! h

theorem mem_of_mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.contains_of_contains_insertIfNew! h

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  Impl.mem_of_mem_insertIfNew!' h

theorem size_insertIfNew [TransCmp cmp] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  Impl.size_insertIfNew! h

theorem size_le_size_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v).size :=
  Impl.size_le_size_insertIfNew! h

theorem size_insertIfNew_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  Impl.size_insertIfNew!_le h

theorem get?_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).get? a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a :=
  Impl.get?_insertIfNew! h

theorem get_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.get_insertIfNew! h

theorem get!_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew k v).get! a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a :=
  Impl.get!_insertIfNew! h

theorem getD_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew k v).getD a fallback =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback :=
  Impl.getD_insertIfNew! h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem get?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    get? (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else get? t a :=
  Impl.Const.get?_insertIfNew! h

theorem get_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insertIfNew k v) a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        v
      else
        get t a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.Const.get_insertIfNew! h

theorem get!_insertIfNew [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else get! t a :=
  Impl.Const.get!_insertIfNew! h

theorem getD_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  Impl.Const.getD_insertIfNew! h

end Const

theorem getKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  Impl.getKey?_insertIfNew! h

theorem getKey_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.getKey_insertIfNew! h

theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  Impl.getKey!_insertIfNew! h

theorem getKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k a fallback : α}
    {v : β k} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  Impl.getKeyD_insertIfNew! h

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] [LawfulEqCmp cmp] (_ : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).1 = t.get? k :=
  Impl.getThenInsertIfNew?!_fst

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).2 = t.insertIfNew k v :=
  ext <| Impl.getThenInsertIfNew?!_snd h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] (_ : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  Impl.Const.getThenInsertIfNew?!_fst

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| Impl.Const.getThenInsertIfNew?!_snd h

end Const

end Std.DTreeMap.Raw
