/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
prelude
import Init.NotationExtra

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: Operations on associative lists
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe w v u

namespace Std.DHashMap.Internal

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w} [Monad m]

/--
`AssocList α β` is "the same as" `List (α × β)`, but flattening the structure
leads to one fewer pointer indirection (in the current code generator).
-/
inductive AssocList (α : Type u) (β : α → Type v) where
  /-- Internal implementation detail of the hash map -/
  | nil
  /-- Internal implementation detail of the hash map -/
  | cons (key : α) (value : β key) (tail : AssocList α β)
  deriving Inhabited

namespace AssocList

/-- Internal implementation detail of the hash map -/
@[specialize] def foldlM (f : δ → (a : α) → β a → m δ) : (init : δ) → AssocList α β → m δ
  | d, nil         => pure d
  | d, cons a b es => do
    let d ← f d a b
    foldlM f d es

/-- Internal implementation detail of the hash map -/
@[inline] def foldl (f : δ → (α : α) → β α → δ) (init : δ) (as : AssocList α β) : δ :=
  Id.run (foldlM f init as)

/-- Internal implementation detail of the hash map -/
@[inline] def forM (f : (a : α) → β a → m PUnit) (as : AssocList α β) : m PUnit :=
  as.foldlM (fun _ => f) ⟨⟩

/-- Internal implementation detail of the hash map -/
@[inline] def forInStep (as : AssocList α β) (init : δ) (f : (a : α) → β a → δ → m (ForInStep δ)) :
    m (ForInStep δ) :=
  go as init
where @[specialize] go : AssocList α β → δ → m (ForInStep δ)
  | .nil, acc => pure (ForInStep.yield acc)
  | .cons k v t, acc => do
    match ← f k v acc with
    | ForInStep.done d => pure (ForInStep.done d)
    | ForInStep.yield d => go t d

/-- Internal implementation detail of the hash map -/
def toList : AssocList α β → List ((a : α) × β a)
  | nil => []
  | cons a b es => ⟨a, b⟩ :: es.toList

/-- Internal implementation detail of the hash map -/
def length (l : AssocList α β) : Nat :=
  l.foldl (fun n _ _ => n + 1) 0

section

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def get? [BEq α] (a : α) : AssocList α (fun _ => β) → Option β
  | nil => none
  | cons k v es => bif k == a then some v else get? a es

end

/-- Internal implementation detail of the hash map -/
def getCast? [BEq α] [LawfulBEq α] (a : α) : AssocList α β → Option (β a)
  | nil => none
  | cons k v es => if h : k == a then some (cast (congrArg β (eq_of_beq h)) v)
      else es.getCast? a

/-- Internal implementation detail of the hash map -/
def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil => false
  | cons k _ l => k == a || l.contains a

/-- Internal implementation detail of the hash map -/
def get {β : Type v} [BEq α] (a : α) : (l : AssocList α (fun _ => β)) → l.contains a → β
  | cons k v es, h => if hka : k == a then v else get a es
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

/-- Internal implementation detail of the hash map -/
def getCast [BEq α] [LawfulBEq α] (a : α) : (l : AssocList α β) → l.contains a → β a
  | cons k v es, h => if hka : k == a then cast (congrArg β (eq_of_beq hka)) v
      else es.getCast a (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

/-- Internal implementation detail of the hash map -/
def getKey [BEq α] (a : α) : (l : AssocList α β) → l.contains a → α
  | cons k _ es, h => if hka : k == a then k
      else es.getKey a (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

/-- Internal implementation detail of the hash map -/
def getCast! [BEq α] [LawfulBEq α] (a : α) [Inhabited (β a)] : AssocList α β → β a
  | nil => panic! "key is not present in hash table"
  | cons k v es => if h : k == a then cast (congrArg β (eq_of_beq h)) v else es.getCast! a

/-- Internal implementation detail of the hash map -/
def getKey? [BEq α] (a : α) : AssocList α β → Option α
  | nil => none
  | cons k _ es => if k == a then some k else es.getKey? a

/-- Internal implementation detail of the hash map -/
def get! {β : Type v} [BEq α] [Inhabited β] (a : α) : AssocList α (fun _ => β) → β
  | nil => panic! "key is not present in hash table"
  | cons k v es => bif k == a then v else es.get! a

/-- Internal implementation detail of the hash map -/
def getKey! [BEq α] [Inhabited α] (a : α) : AssocList α β → α
  | nil => panic! "key is not present in hash table"
  | cons k _ es => if k == a then k else es.getKey! a

/-- Internal implementation detail of the hash map -/
def getCastD [BEq α] [LawfulBEq α] (a : α) (fallback : β a) : AssocList α β → β a
  | nil => fallback
  | cons k v es => if h : k == a then cast (congrArg β (eq_of_beq h)) v
      else es.getCastD a fallback

/-- Internal implementation detail of the hash map -/
def getD {β : Type v} [BEq α] (a : α) (fallback : β) : AssocList α (fun _ => β) → β
  | nil => fallback
  | cons k v es => bif k == a then v else es.getD a fallback

/-- Internal implementation detail of the hash map -/
def getKeyD [BEq α] (a : α) (fallback : α) : AssocList α β → α
  | nil => fallback
  | cons k _ es => if k == a then k else es.getKeyD a fallback

/-- Internal implementation detail of the hash map -/
def replace [BEq α] (a : α) (b : β a) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then cons a b l else cons k v (replace a b l)

/-- Internal implementation detail of the hash map -/
def erase [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then l else cons k v (l.erase a)

/-- Internal implementation detail of the hash map -/
@[inline] def filterMap (f : (a : α) → β a → Option (γ a)) :
    AssocList α β → AssocList α γ :=
  go .nil
where
  @[specialize] go (acc : AssocList α γ) : AssocList α β → AssocList α γ
  | nil => acc
  | cons k v t => match f k v with
    | none => go acc t
    | some v' => go (cons k v' acc) t

/-- Internal implementation detail of the hash map -/
@[inline] def map (f : (a : α) → β a → γ a) : AssocList α β → AssocList α γ :=
  go .nil
where
  @[specialize] go (acc : AssocList α γ) : AssocList α β → AssocList α γ
  | nil => acc
  | cons k v t => go (cons k (f k v) acc) t

/-- Internal implementation detail of the hash map -/
@[inline] def filter (f : (a : α) → β a → Bool) : AssocList α β → AssocList α β :=
  go .nil
where
  @[specialize] go (acc : AssocList α β) : AssocList α β → AssocList α β
  | nil => acc
  | cons k v t => bif f k v then go (cons k v acc) t else go acc t

end AssocList

end Std.DHashMap.Internal
