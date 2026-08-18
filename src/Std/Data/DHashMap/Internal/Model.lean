/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Std.Data.DHashMap.Basic
import all Std.Data.DHashMap.Internal.Defs
public import Std.Data.DHashMap.Internal.HashesTo
public import Std.Data.DHashMap.Internal.AssocList.Lemmas
import Init.Data.List.Impl

@[expose] public section

/-!
This internal file provides stable model names for the linear-probing implementation.

The verification boundary remains `toListModel`: the physical table is exposed to proofs as one
associative list inside a singleton array. The model operations below intentionally delegate to the
executable operations. `Internal.WF` proves their list semantics independently of probing and
array-update details.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {δ : α → Type w}

namespace Std.DHashMap.Internal.Raw₀

/-! # Model operations -/

/-- Internal implementation detail of the hash map. -/
def replaceₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  m.insert a b

/-- Internal implementation detail of the hash map. -/
def consₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  m.insert a b

/-- Internal implementation detail of the hash map. -/
def get?ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  m.get? a

/-- Internal implementation detail of the hash map. -/
def getKey?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option α :=
  m.getKey? a

/-- Internal implementation detail of the hash map. -/
@[implicit_reducible] def containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  m.contains a

/-- Internal implementation detail of the hash map. -/
def getₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : m.containsₘ a) : β a :=
  m.get a h

/-- Internal implementation detail of the hash map. -/
def getEntryₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : m.containsₘ a) : (k : α) × β k :=
  m.getEntry a h

/-- Internal implementation detail of the hash map. -/
def getEntry?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option ((k : α) × β k) :=
  m.getEntry? a

/-- Internal implementation detail of the hash map. -/
def getEntryDₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (fallback : (k : α) × β k) : (k : α) × β k :=
  m.getEntryD a fallback

/-- Internal implementation detail of the hash map. -/
def getEntry!ₘ [BEq α] [Hashable α] [Inhabited ((k : α) × β k)] (m : Raw₀ α β)
    (a : α) : (k : α) × β k :=
  m.getEntry! a

/-- Internal implementation detail of the hash map. -/
def getDₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : β a) :
    β a :=
  m.getD a fallback

/-- Internal implementation detail of the hash map. -/
def get!ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    [Inhabited (β a)] : β a :=
  m.get! a

/-- Internal implementation detail of the hash map. -/
def getKeyₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (h : m.containsₘ a) : α :=
  m.getKey a h

/-- Internal implementation detail of the hash map. -/
def getKeyDₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a fallback : α) : α :=
  m.getKeyD a fallback

/-- Internal implementation detail of the hash map. -/
def getKey!ₘ [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (a : α) : α :=
  m.getKey! a

/-- Internal implementation detail of the hash map. -/
def insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  m.insert a b

/-- Internal implementation detail of the hash map. -/
def insertIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  m.insertIfNew a b

/-- Internal implementation detail of the hash map. -/
def eraseₘaux [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  m.erase a

/-- Internal implementation detail of the hash map. -/
def eraseₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  m.erase a

/-- Internal implementation detail of the hash map. -/
def alterₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : Option (β a) → Option (β a)) : Raw₀ α β :=
  m.alter a f

/-- Internal implementation detail of the hash map. -/
def modifyₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : β a → β a) : Raw₀ α β :=
  m.modify a f

namespace Const

variable {β : Type v}

/-- Internal implementation detail of the hash map. -/
def alterₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : Option β → Option β) : Raw₀ α (fun _ => β) :=
  Const.alter m a f

/-- Internal implementation detail of the hash map. -/
def modifyₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (f : β → β) :
    Raw₀ α (fun _ => β) :=
  Const.modify m a f

/-- Internal implementation detail of the hash map. -/
def get?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  Const.get? m a

/-- Internal implementation detail of the hash map. -/
def getₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (h : m.containsₘ a) : β :=
  Const.get m a h

/-- Internal implementation detail of the hash map. -/
def getDₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (fallback : β) : β :=
  Const.getD m a fallback

/-- Internal implementation detail of the hash map. -/
def get!ₘ [BEq α] [Hashable α] [Inhabited β] (m : Raw₀ α (fun _ => β)) (a : α) : β :=
  Const.get! m a

end Const

/-- Internal implementation detail of the hash map. -/
def filterMapₘ (m : Raw₀ α β) (f : (a : α) → β a → Option (δ a)) : Raw₀ α δ :=
  m.filterMap f

/-- Internal implementation detail of the hash map. -/
def mapₘ (m : Raw₀ α β) (f : (a : α) → β a → δ a) : Raw₀ α δ :=
  m.map f

/-- Internal implementation detail of the hash map. -/
def filterₘ (m : Raw₀ α β) (f : (a : α) → β a → Bool) : Raw₀ α β :=
  m.filter f

/-- Internal implementation detail of the hash map. -/
def insertListₘ [BEq α] [Hashable α] (m : Raw₀ α β) (l : List ((a : α) × β a)) :
    Raw₀ α β :=
  l.foldl (fun m p => m.insert p.1 p.2) m

/-- Internal implementation detail of the hash map. -/
def eraseListₘ [BEq α] [Hashable α] (m : Raw₀ α β) (l : List α) : Raw₀ α β :=
  l.foldl Raw₀.erase m

/-- Internal implementation detail of the hash map. -/
def insertListIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β)
    (l : List ((a : α) × β a)) : Raw₀ α β :=
  l.foldl (fun m p => m.insertIfNew p.1 p.2) m

/-- Internal implementation detail of the hash map. -/
def diffₘ [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) : Raw₀ α β :=
  m₁.diff m₂

/-- Internal implementation detail of the hash map. -/
def unionₘ [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) : Raw₀ α β :=
  m₁.union m₂

/-- Internal implementation detail of the hash map. -/
def interSmallerFnₘ [BEq α] [Hashable α] (m sofar : Raw₀ α β) (k : α) : Raw₀ α β :=
  interSmallerFn m sofar k

namespace Const

variable {β : Type v}

/-- Internal implementation detail of the hash map. -/
def insertListₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (l : List (α × β)) :
    Raw₀ α (fun _ => β) :=
  l.foldl (fun m p => m.insert p.1 p.2) m

/-- Internal implementation detail of the hash map. -/
def insertListIfNewUnitₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => Unit))
    (l : List α) : Raw₀ α (fun _ => Unit) :=
  l.foldl (fun m a => m.insertIfNew a ()) m

end Const

/-! # Equality with executable operations -/

theorem get?_eq_get?ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    get? m a = get?ₘ m a := rfl

theorem get_eq_getₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : m.contains a) : get m a h = getₘ m a h := rfl

theorem getEntry_eq_getEntryₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : m.contains a) : getEntry m a h = getEntryₘ m a h := rfl

theorem getEntry?_eq_getEntry?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    getEntry? m a = getEntry?ₘ m a := rfl

theorem getEntryD_eq_getEntryDₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (fallback : (a : α) × β a) : getEntryD m a fallback = getEntryDₘ m a fallback := rfl

theorem getEntry!_eq_getEntry!ₘ [BEq α] [Hashable α] [Inhabited ((a : α) × β a)]
    (m : Raw₀ α β) (a : α) : getEntry! m a = getEntry!ₘ m a := rfl

theorem getD_eq_getDₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (fallback : β a) : getD m a fallback = getDₘ m a fallback := rfl

theorem get!_eq_get!ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    [Inhabited (β a)] : get! m a = get!ₘ m a := rfl

theorem getKey?_eq_getKey?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    getKey? m a = getKey?ₘ m a := rfl

theorem getKey_eq_getKeyₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (h : m.contains a) : getKey m a h = getKeyₘ m a h := rfl

theorem getKeyD_eq_getKeyDₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a fallback : α) :
    getKeyD m a fallback = getKeyDₘ m a fallback := rfl

theorem getKey!_eq_getKey!ₘ [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (a : α) :
    getKey! m a = getKey!ₘ m a := rfl

theorem contains_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    m.contains a = m.containsₘ a := rfl

theorem insert_eq_insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.insert a b = m.insertₘ a b := rfl

theorem alter_eq_alterₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : Option (β a) → Option (β a)) : m.alter a f = m.alterₘ a f := rfl

theorem modify_eq_modifyₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : β a → β a) : m.modify a f = m.modifyₘ a f := rfl

namespace Const

variable {β : Type v}

theorem alter_eq_alterₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : Option β → Option β) : Const.alter m a f = Const.alterₘ m a f := rfl

theorem modify_eq_modifyₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : β → β) : Const.modify m a f = Const.modifyₘ m a f := rfl

end Const

theorem containsThenInsert_eq_insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : (m.containsThenInsert a b).2 = m.insertₘ a b := by
  simp [containsThenInsert, insertₘ]

theorem containsThenInsert_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : (m.containsThenInsert a b).1 = m.containsₘ a := by
  simp [containsThenInsert, containsₘ]

theorem containsThenInsertIfNew_eq_insertIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β)
    (a : α) (b : β a) : (m.containsThenInsertIfNew a b).2 = m.insertIfNewₘ a b := by
  cases hc : m.contains a <;>
    simp [containsThenInsertIfNew, insertIfNewₘ, insertIfNew, hc]

theorem containsThenInsertIfNew_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β)
    (a : α) (b : β a) : (m.containsThenInsertIfNew a b).1 = m.containsₘ a := by
  cases hc : m.contains a <;> simp [containsThenInsertIfNew, containsₘ, hc]

theorem insertIfNew_eq_insertIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : m.insertIfNew a b = m.insertIfNewₘ a b := rfl

theorem getThenInsertIfNew?_eq_insertIfNewₘ [BEq α] [Hashable α] [LawfulBEq α]
    (m : Raw₀ α β) (a : α) (b : β a) :
    (m.getThenInsertIfNew? a b).2 = m.insertIfNewₘ a b := by
  simp [getThenInsertIfNew?, insertIfNewₘ]

theorem getThenInsertIfNew?_eq_get?ₘ [BEq α] [Hashable α] [LawfulBEq α]
    (m : Raw₀ α β) (a : α) (b : β a) : (m.getThenInsertIfNew? a b).1 = m.get?ₘ a := by
  simp [getThenInsertIfNew?, get?ₘ]

theorem erase_eq_eraseₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    m.erase a = m.eraseₘ a := rfl

theorem filterMap_eq_filterMapₘ (m : Raw₀ α β) (f : (a : α) → β a → Option (δ a)) :
    m.filterMap f = m.filterMapₘ f := rfl

theorem map_eq_mapₘ (m : Raw₀ α β) (f : (a : α) → β a → δ a) :
    m.map f = m.mapₘ f := rfl

theorem filter_eq_filterₘ (m : Raw₀ α β) (f : (a : α) → β a → Bool) :
    m.filter f = m.filterₘ f := rfl

theorem insertMany_eq_insertListₘ [BEq α] [Hashable α] (m : Raw₀ α β)
    (l : List ((a : α) × β a)) : insertMany m l = insertListₘ m l := by
  simp only [insertMany, Id.run_pure, pure_bind, List.forIn_pure_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' : Raw₀ α β} {a : α} {b : β a}, P m'' → P (m''.insert a b)) → P m → P m' }),
      (List.foldl (fun m' p =>
        ⟨m'.val.insert p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
        t.val.insertListₘ l from this _
  intro t
  induction l generalizing m with
  | nil => simp [insertListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, insertListₘ]
    apply ih

theorem eraseManyEntries_eq_eraseListₘ [BEq α] [Hashable α] (m : Raw₀ α β)
    (l : List ((a : α) × β a)) : eraseManyEntries m l = eraseListₘ m (l.map (·.1)) := by
  simp only [eraseManyEntries, Id.run_pure, pure_bind, List.forIn_pure_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' : Raw₀ α β} {a : α}, P m'' → P (m''.erase a)) → P m → P m' }),
      (List.foldl (fun m' p =>
        ⟨m'.val.erase p.1, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
        t.val.eraseListₘ (l.map (·.1)) from this _
  intro t
  induction l generalizing m with
  | nil => simp [eraseListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih

theorem insertManyIfNew_eq_insertListIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β)
    (l : List ((a : α) × β a)) : insertManyIfNew m l = insertListIfNewₘ m l := by
  simp only [insertManyIfNew, Id.run_pure, pure_bind, List.forIn_pure_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' : Raw₀ α β} {a : α} {b : β a}, P m'' → P (m''.insertIfNew a b)) → P m → P m' }),
      (List.foldl (fun m' p =>
        ⟨m'.val.insertIfNew p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
        t.val.insertListIfNewₘ l from this _
  intro t
  induction l generalizing m with
  | nil => simp [insertListIfNewₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, insertListIfNewₘ]
    apply ih

theorem interSmallerFn_eq_interSmallerFnₘ [BEq α] [Hashable α] (m sofar : Raw₀ α β)
    (k : α) : interSmallerFn m sofar k = interSmallerFnₘ m sofar k := rfl

namespace Const

variable {β : Type v}

theorem get?_eq_get?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) :
    Const.get? m a = Const.get?ₘ m a := rfl

theorem get_eq_getₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (h : m.contains a) : Const.get m a h = Const.getₘ m a h := rfl

theorem getD_eq_getDₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (fallback : β) : Const.getD m a fallback = Const.getDₘ m a fallback := rfl

theorem get!_eq_get!ₘ [BEq α] [Hashable α] [Inhabited β] (m : Raw₀ α (fun _ => β))
    (a : α) : Const.get! m a = Const.get!ₘ m a := rfl

theorem getThenInsertIfNew?_eq_insertIfNewₘ [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => β)) (a : α) (b : β) :
    (Const.getThenInsertIfNew? m a b).2 = m.insertIfNewₘ a b := by
  simp [Const.getThenInsertIfNew?, insertIfNewₘ]

theorem getThenInsertIfNew?_eq_get?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β))
    (a : α) (b : β) : (Const.getThenInsertIfNew? m a b).1 = Const.get?ₘ m a := by
  simp [Const.getThenInsertIfNew?, Const.get?ₘ]

theorem insertMany_eq_insertListₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β))
    (l : List (α × β)) : (Const.insertMany m l).1 = Const.insertListₘ m l := by
  simp only [Const.insertMany, Id.run_pure, pure_bind, List.forIn_pure_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α (fun _ => β) → Prop),
      (∀ {m'' : Raw₀ α (fun _ => β)} {a : α} {b : β}, P m'' → P (m''.insert a b)) →
        P m → P m' }),
      (List.foldl (fun m' p =>
        ⟨m'.val.insert p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
        Const.insertListₘ t.val l from this _
  intro t
  induction l generalizing m with
  | nil => simp [Const.insertListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, Const.insertListₘ]
    apply ih

theorem insertManyIfNewUnit_eq_insertListIfNewUnitₘ [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => Unit)) (l : List α) :
    (Const.insertManyIfNewUnit m l).1 = Const.insertListIfNewUnitₘ m l := by
  simp only [Const.insertManyIfNewUnit, Id.run_pure, pure_bind, List.forIn_pure_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α (fun _ => Unit) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m' }),
      (List.foldl (fun m' p =>
        ⟨m'.val.insertIfNew p (), fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
        Const.insertListIfNewUnitₘ t.val l from this _
  intro t
  induction l generalizing m with
  | nil => simp [Const.insertListIfNewUnitₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, Const.insertListIfNewUnitₘ]
    apply ih

end Const

end Std.DHashMap.Internal.Raw₀
