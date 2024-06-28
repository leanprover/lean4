/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
prelude
import Init.NotationExtra

set_option autoImplicit false

universe w v u

namespace Std.DHashMap.Internal

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w} [Monad m]

/--
`AssocList α β` is "the same as" `List (α × β)`, but flattening the structure
leads to one fewer pointer indirection (in the current code generator).
-/
inductive AssocList (α : Type u) (β : α → Type v) where
  | nil
  | cons (key : α) (value : β key) (tail : AssocList α β)
  deriving Inhabited

namespace AssocList

@[specialize] def foldlM (f : δ → (a : α) → β a → m δ) : (init : δ) → AssocList α β → m δ
  | d, nil         => pure d
  | d, cons a b es => do
    let d ← f d a b
    foldlM f d es

@[inline] def foldl (f : δ → (α : α) → β α → δ) (init : δ) (as : AssocList α β) : δ :=
  Id.run (foldlM f init as)

@[inline] def forM (f : (a : α) → β a → m PUnit) (as : AssocList α β) : m PUnit :=
  as.foldlM (fun _ => f) ⟨⟩

@[inline] def forInStep (as : AssocList α β) (init : δ) (f : (a : α) → β a → δ → m (ForInStep δ)) : m (ForInStep δ) :=
  go as init
where @[specialize] go : AssocList α β → δ → m (ForInStep δ)
  | .nil, acc => pure (ForInStep.yield acc)
  | .cons k v t, acc => do
    match ← f k v acc with
    | ForInStep.done d => pure (ForInStep.done d)
    | ForInStep.yield d => go t d

def toList : AssocList α β → List (Σ a, β a)
  | nil => []
  | cons a b es => ⟨a, b⟩ :: es.toList

def length (l : AssocList α β) : Nat :=
  l.foldl (fun n _ _ => n + 1) 0

section

variable {β : Type v}

def get? [BEq α] (a : α) : AssocList α (fun _ => β) → Option β
  | nil => none
  | cons k v es => bif a == k then some v else get? a es

end

def getCast? [BEq α] [LawfulBEq α] (a : α) : AssocList α β → Option (β a)
  | nil => none
  | cons k v es => if h : a == k then some (cast (congrArg β (eq_of_beq h).symm) v) else es.getCast? a

def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil => false
  | cons k _ l => a == k || l.contains a

def get {β : Type v} [BEq α] (a : α) : (l : AssocList α (fun _ => β)) → l.contains a → β
  | cons k v es, h => if hka : a == k then v else get a es
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def getCast [BEq α] [LawfulBEq α] (a : α) : (l : AssocList α β) → l.contains a → β a
  | cons k v es, h => if hka : a == k then cast (congrArg β (eq_of_beq hka).symm) v else es.getCast a
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def getCast! [BEq α] [LawfulBEq α] (a : α) [Inhabited (β a)] : AssocList α β → β a
  | nil => panic! "key is not present in hash table"
  | cons k v es => if h : a == k then cast (congrArg β (eq_of_beq h).symm) v else es.getCast! a

def get! {β : Type v} [BEq α] [Inhabited β] (a : α) : AssocList α (fun _ => β) → β
  | nil => panic! "key is not present in hash table"
  | cons k v es => bif a == k then v else es.get! a

def getCastD [BEq α] [LawfulBEq α] (a : α) (fallback : β a) : AssocList α β → β a
  | nil => fallback
  | cons k v es => if h : a == k then cast (congrArg β (eq_of_beq h).symm) v else es.getCastD a fallback

def getD {β : Type v} [BEq α] (a : α) (fallback : β) : AssocList α (fun _ => β) → β
  | nil => fallback
  | cons k v es => bif a == k then v else es.getD a fallback

def replace [BEq α] (a : α) (b : β a) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif a == k then cons a b l else cons k v (replace a b l)

def remove [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif a == k then l else cons k v (l.remove a)

@[inline] def filterMap (f : (a : α) → β a → Option (γ a)) :
    AssocList α β → AssocList α γ :=
  go .nil
where
  @[specialize] go (acc : AssocList α γ) : AssocList α β → AssocList α γ
  | nil => acc
  | cons k v t => match f k v with
    | none => go acc t
    | some v' => go (cons k v' acc) t

@[inline] def map (f : (a : α) → β a → γ a) : AssocList α β → AssocList α γ :=
  go .nil
where
  @[specialize] go (acc : AssocList α γ) : AssocList α β → AssocList α γ
  | nil => acc
  | cons k v t => go (cons k (f k v) acc) t

@[inline] def filter (f : (a : α) → β a → Bool) : AssocList α β → AssocList α β :=
  go .nil
where
  @[specialize] go (acc : AssocList α β) : AssocList α β → AssocList α β
  | nil => acc
  | cons k v t => bif f k v then go (cons k v acc) t else go acc t

end AssocList

end Std.DHashMap.Internal
