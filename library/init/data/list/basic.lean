/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.core init.data.nat.basic
open decidable list

universes u v w

instance (α : Type u) : inhabited (list α) :=
⟨list.nil⟩

variables {α : Type u} {β : Type v} {γ : Type w}

namespace list

protected def hasDecEq [decidableEq α] : Π a b : list α, decidable (a = b)
| []      []      := isTrue rfl
| (a::as) []      := isFalse (λ h, list.noConfusion h)
| []      (b::bs) := isFalse (λ h, list.noConfusion h)
| (a::as) (b::bs) :=
  match decEq a b with
  | isTrue hab  :=
    (match hasDecEq as bs with
     | isTrue habs  := isTrue (eq.subst hab (eq.subst habs rfl))
     | isFalse nabs := isFalse (λ h, list.noConfusion h (λ _ habs, absurd habs nabs)))
  | isFalse nab := isFalse (λ h, list.noConfusion h (λ hab _, absurd hab nab))

instance [decidableEq α] : decidableEq (list α) :=
{decEq := list.hasDecEq}

def reverseCore : list α → list α → list α
| []     r := r
| (a::l) r := reverseCore l (a::r)

local infix `**`:66 := reverseCore

def reverse : list α → list α :=
λ l, reverseCore l []

protected def append (as bs : list α) : list α :=
reverseCore as.reverse bs

instance : hasAppend (list α) :=
⟨list.append⟩

theorem reverseCoreReverseCoreNil : ∀ (as bs : list α), (as ** bs) ** [] = bs ** as
| []  bs     := rfl
| (a::as) bs :=
  show reverseCore (reverseCore as (a::bs)) [] = reverseCore bs (a::as), from
  reverseCoreReverseCoreNil as (a::bs)

theorem nilAppend (as : list α) : [] ++ as = as :=
rfl

theorem appendNil (as : list α) : as ++ [] = as :=
show (as ** []) ** [] = as, from
reverseCoreReverseCoreNil as []

theorem reverseCoreReverseCore : ∀ (as bs cs : list α), (as ** bs) ** cs = bs ** ((as ** []) ** cs)
| []      bs cs := rfl
| (a::as) bs cs :=
  show (as ** a::bs) ** cs = bs ** ((as ** [a]) ** cs), from
  have h₁ : (as ** a::bs) ** cs = bs ** a::((as ** []) ** cs),       from reverseCoreReverseCore as (a::bs) cs,
  have h₂ : ((as ** [a]) ** cs) = a::((as ** []) ** cs),             from reverseCoreReverseCore as [a] cs,
  have h₃ : bs ** a::((as ** []) ** cs) = bs ** ((as ** [a]) ** cs), from congrArg (λ b, bs ** b) h₂.symm,
  eq.trans h₁ h₃

theorem consAppend (a : α) (as bs : list α) : (a::as) ++ bs = a::(as ++ bs) :=
reverseCoreReverseCore as [a] bs

theorem appendAssoc : ∀ (as bs cs : list α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
| []      bs cs := rfl
| (a::as) bs cs :=
  show ((a::as) ++ bs) ++ cs = (a::as) ++ (bs ++ cs),      from
  have h₁ : ((a::as) ++ bs) ++ cs = a::(as++bs) ++ cs,     from congrArg (++ cs) (consAppend a as bs),
  have h₂ : a::(as++bs) ++ cs     = a::((as++bs) ++ cs),   from consAppend a (as++bs) cs,
  have h₃ : a::((as++bs) ++ cs)   = a::(as ++ (bs ++ cs)), from congrArg (λ as, a::as) (appendAssoc as bs cs),
  have h₄ : a::(as ++ (bs ++ cs)) = (a::as ++ (bs ++ cs)), from (consAppend a as (bs++cs)).symm,
  eq.trans (eq.trans (eq.trans h₁ h₂) h₃) h₄

protected def mem : α → list α → Prop
| a []       := false
| a (b :: l) := a = b ∨ mem a l

instance : hasMem α (list α) :=
⟨list.mem⟩

instance decidableMem [decidableEq α] (a : α) : ∀ (l : list α), decidable (a ∈ l)
| []     := isFalse notFalse
| (b::l) :=
  if h₁ : a = b then isTrue (or.inl h₁)
  else match decidableMem l with
       | isTrue  h₂ := isTrue (or.inr h₂)
       | isFalse h₂ := isFalse (notOr h₁ h₂)

instance : hasEmptyc (list α) :=
⟨list.nil⟩

protected def erase {α} [decidableEq α] : list α → α → list α
| []     b := []
| (a::l) b := if a = b then l else a :: erase l b

protected def bagInter {α} [decidableEq α] : list α → list α → list α
| []      _   := []
| _       []  := []
| (a::l₁) l₂  := if a ∈ l₂ then a :: bagInter l₁ (l₂.erase a) else bagInter l₁ l₂

protected def diff {α} [decidableEq α] : list α → list α → list α
| l      []      := l
| l₁     (a::l₂) := if a ∈ l₁ then diff (l₁.erase a) l₂ else diff l₁ l₂

def lengthAux : list α → nat → nat
| []      n := n
| (a::as) n := lengthAux as (n+1)

def length (as : list α) : nat :=
lengthAux as 0

def empty : list α → bool
| []       := tt
| (_ :: _) := ff

open option nat

def nth : list α → nat → option α
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

def head [inhabited α] : list α → α
| []       := default α
| (a :: l) := a

def tail : list α → list α
| []       := []
| (a :: l) := l

@[specialize] def map (f : α → β) : list α → list β
| []       := []
| (a :: l) := f a :: map l

@[specialize] def map₂ (f : α → β → γ) : list α → list β → list γ
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

def join : list (list α) → list α
| []        := []
| (l :: ls) := l ++ join ls

def filterMap (f : α → option β) : list α → list β
| []     := []
| (a::l) :=
  match f a with
  | none   := filterMap l
  | some b := b :: filterMap l

def filter (p : α → Prop) [decidablePred p] : list α → list α
| []     := []
| (a::l) := if p a then a :: filter l else filter l

def partition (p : α → Prop) [decidablePred p] : list α → list α × list α
| []     := ([], [])
| (a::l) := let (l₁, l₂) := partition l in if p a then (a :: l₁, l₂) else (l₁, a :: l₂)

def dropWhile (p : α → Prop) [decidablePred p] : list α → list α
| []     := []
| (a::l) := if p a then dropWhile l else a::l

def span (p : α → Prop) [decidablePred p] : list α → list α × list α
| []      := ([], [])
| (a::xs) := if p a then let (l, r) := span xs in (a :: l, r) else ([], a::xs)

def findIndex (p : α → Prop) [decidablePred p] : list α → nat
| []     := 0
| (a::l) := if p a then 0 else succ (findIndex l)

def indexOf [decidableEq α] (a : α) (l : list α) : nat :=
findIndex (eq a) l

def assoc [decidableEq α] : list (α × β) → α → option β
| []         _  := none
| ((a,b)::l) a' := if a = a' then some b else assoc l a'

def removeAll [decidableEq α] (xs ys : list α) : list α :=
filter (∉ ys) xs

def updateNth : list α → ℕ → α → list α
| (x::xs) 0     a := a :: xs
| (x::xs) (i+1) a := x :: updateNth xs i a
| []      _     _ := []

def removeNth : list α → ℕ → list α
| []      _     := []
| (x::xs) 0     := xs
| (x::xs) (i+1) := x :: removeNth xs i

def drop : ℕ → list α → list α
| 0        a      := a
| (succ n) []     := []
| (succ n) (x::r) := drop n r

def take : ℕ → list α → list α
| 0        a        := []
| (succ n) []       := []
| (succ n) (x :: r) := x :: take n r

@[specialize] def foldl (f : α → β → α) : α → list β → α
| a []       := a
| a (b :: l) := foldl (f a b) l

@[specialize] def foldr (f : α → β → β) (b : β) : list α → β
| []       := b
| (a :: l) := f a (foldr l)

@[specialize] def foldr1 (f : α → α → α) : Π (xs : list α), xs ≠ [] → α
| []              nem := false.elim (nem rfl)
| [a]             nem := a
| (a :: l@(_::_)) nem := f a (foldr1 l (λ eq, list.noConfusion eq))

@[specialize] def foldr1Opt (f : α → α → α) : list α → option α
| []       := none
| (a :: l) := some $ foldr1 f (a :: l) (λ eq, list.noConfusion eq)

@[inline] def any (l : list α) (p : α → bool) : bool :=
foldr (λ a r, p a || r) ff l

@[inline] def all (l : list α) (p : α → bool) : bool :=
foldr (λ a r, p a && r) tt l

def bor  (l : list bool) : bool := any l id

def band (l : list bool) : bool := all l id

def zipWith (f : α → β → γ) : list α → list β → list γ
| (x::xs) (y::ys) := f x y :: zipWith xs ys
| _       _       := []

def zip : list α → list β → list (prod α β) :=
zipWith prod.mk

def unzip : list (α × β) → list α × list β
| []            := ([], [])
| ((a, b) :: t) := match unzip t with | (al, bl) := (a::al, b::bl)

protected def insert [decidableEq α] (a : α) (l : list α) : list α :=
if a ∈ l then l else a :: l

instance [decidableEq α] : hasInsert α (list α) :=
⟨list.insert⟩

protected def union [decidableEq α] (l₁ l₂ : list α) : list α :=
foldr insert l₂ l₁

instance [decidableEq α] : hasUnion (list α) :=
⟨list.union⟩

protected def inter [decidableEq α] (l₁ l₂ : list α) : list α :=
filter (∈ l₂) l₁

instance [decidableEq α] : hasInter (list α) :=
⟨list.inter⟩

def repeat (a : α) (n : ℕ) : list α :=
n.repeat (λ _ xs, a :: xs) []

def rangeCore : ℕ → list ℕ → list ℕ
| 0        l := l
| (succ n) l := rangeCore n (n :: l)

def range (n : ℕ) : list ℕ :=
rangeCore n []

def iota : ℕ → list ℕ
| 0        := []
| (succ n) := succ n :: iota n

def enumFrom : ℕ → list α → list (ℕ × α)
| n [] := nil
| n (x :: xs) := (n, x) :: enumFrom (n + 1) xs

def enum : list α → list (ℕ × α) := enumFrom 0

def last : Π l : list α, l ≠ [] → α
| []        h := absurd rfl h
| [a]       h := a
| (a::b::l) h := last (b::l) (λ h, list.noConfusion h)

def ilast [inhabited α] : list α → α
| []        := arbitrary α
| [a]       := a
| [a, b]    := b
| (a::b::l) := ilast l

def init : list α → list α
| []     := []
| [a]    := []
| (a::l) := a::init l

def intersperse (sep : α) : list α → list α
| []      := []
| [x]     := [x]
| (x::xs) := x::sep::intersperse xs

def intercalate (sep : list α) (xs : list (list α)) : list α :=
join (intersperse sep xs)

@[inline] protected def bind {α : Type u} {β : Type v} (a : list α) (b : α → list β) : list β :=
join (map b a)

@[inline] protected def ret {α : Type u} (a : α) : list α :=
[a]

protected def lt [hasLt α] : list α → list α → Prop
| []      []      := false
| []      (b::bs) := true
| (a::as) []      := false
| (a::as) (b::bs) := a < b ∨ (¬ b < a ∧ lt as bs)

instance [hasLt α] : hasLt (list α) :=
⟨list.lt⟩

instance hasDecidableLt [hasLt α] [h : decidableRel ((<) : α → α → Prop)] : Π l₁ l₂ : list α, decidable (l₁ < l₂)
| []      []      := isFalse notFalse
| []      (b::bs) := isTrue trivial
| (a::as) []      := isFalse notFalse
| (a::as) (b::bs) :=
  match h a b with
  | isTrue h₁  := isTrue (or.inl h₁)
  | isFalse h₁ :=
    match h b a with
    | isTrue h₂  := isFalse (λ h, or.elim h (λ h, absurd h h₁) (λ ⟨h, _⟩, absurd h₂ h))
    | isFalse h₂ :=
      match hasDecidableLt as bs with
      | isTrue h₃  := isTrue (or.inr ⟨h₂, h₃⟩)
      | isFalse h₃ := isFalse (λ h, or.elim h (λ h, absurd h h₁) (λ ⟨_, h⟩, absurd h h₃))

@[reducible] protected def le [hasLt α] (a b : list α) : Prop :=
¬ b < a

instance [hasLt α] : hasLe (list α) :=
⟨list.le⟩

instance hasDecidableLe [hasLt α] [h : decidableRel ((<) : α → α → Prop)] : Π l₁ l₂ : list α, decidable (l₁ ≤ l₂) :=
λ a b, not.decidable

lemma leEqNotGt [hasLt α] : ∀ l₁ l₂ : list α, (l₁ ≤ l₂) = ¬ (l₂ < l₁) :=
λ l₁ l₂, rfl

lemma ltEqNotGe [hasLt α] [decidableRel ((<) : α → α → Prop)] : ∀ l₁ l₂ : list α, (l₁ < l₂) = ¬ (l₂ ≤ l₁) :=
λ l₁ l₂,
  show (l₁ < l₂) = ¬ ¬ (l₁ < l₂), from
  eq.subst (propext (notNotIff (l₁ < l₂))).symm rfl

/--  `isPrefixOf l₁ l₂` returns `tt` iff `l₁` is a prefix of `l₂`. -/
def isPrefixOf [decidableEq α] : list α → list α → bool
| []      _       := tt
| _       []      := ff
| (a::as) (b::bs) := toBool (a = b) && isPrefixOf as bs

/--  `isSuffixOf l₁ l₂` returns `tt` iff `l₁` is a suffix of `l₂`. -/
def isSuffixOf [decidableEq α] (l₁ l₂ : list α) : bool :=
isPrefixOf l₁.reverse l₂.reverse

end list

namespace binTree
private def toListAux : binTree α → list α → list α
| empty      as := as
| (leaf a)   as := a::as
| (node l r) as := toListAux l (toListAux r as)

def toList (t : binTree α) : list α :=
toListAux t []
end binTree
