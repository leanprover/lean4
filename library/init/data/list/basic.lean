/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.core init.data.nat.basic
open Decidable List

universes u v w

instance (α : Type u) : Inhabited (List α) :=
⟨List.nil⟩

variables {α : Type u} {β : Type v} {γ : Type w}

namespace List

protected def hasDecEq [DecidableEq α] : Π a b : List α, Decidable (a = b)
| []      []      := isTrue rfl
| (a::as) []      := isFalse (λ h, List.noConfusion h)
| []      (b::bs) := isFalse (λ h, List.noConfusion h)
| (a::as) (b::bs) :=
  match decEq a b with
  | isTrue hab  :=
    (match hasDecEq as bs with
     | isTrue habs  := isTrue (Eq.subst hab (Eq.subst habs rfl))
     | isFalse nabs := isFalse (λ h, List.noConfusion h (λ _ habs, absurd habs nabs)))
  | isFalse nab := isFalse (λ h, List.noConfusion h (λ hab _, absurd hab nab))

instance [DecidableEq α] : DecidableEq (List α) :=
{decEq := List.hasDecEq}

def reverseCore : List α → List α → List α
| []     r := r
| (a::l) r := reverseCore l (a::r)

local infix `**`:66 := reverseCore

def reverse : List α → List α :=
λ l, reverseCore l []

protected def append (as bs : List α) : List α :=
reverseCore as.reverse bs

instance : HasAppend (List α) :=
⟨List.append⟩

theorem reverseCoreReverseCoreNil : ∀ (as bs : List α), (as ** bs) ** [] = bs ** as
| []  bs     := rfl
| (a::as) bs :=
  show reverseCore (reverseCore as (a::bs)) [] = reverseCore bs (a::as), from
  reverseCoreReverseCoreNil as (a::bs)

theorem nilAppend (as : List α) : [] ++ as = as :=
rfl

theorem appendNil (as : List α) : as ++ [] = as :=
show (as ** []) ** [] = as, from
reverseCoreReverseCoreNil as []

theorem reverseCoreReverseCore : ∀ (as bs cs : List α), (as ** bs) ** cs = bs ** ((as ** []) ** cs)
| []      bs cs := rfl
| (a::as) bs cs :=
  show (as ** a::bs) ** cs = bs ** ((as ** [a]) ** cs), from
  have h₁ : (as ** a::bs) ** cs = bs ** a::((as ** []) ** cs),       from reverseCoreReverseCore as (a::bs) cs,
  have h₂ : ((as ** [a]) ** cs) = a::((as ** []) ** cs),             from reverseCoreReverseCore as [a] cs,
  have h₃ : bs ** a::((as ** []) ** cs) = bs ** ((as ** [a]) ** cs), from congrArg (λ b, bs ** b) h₂.symm,
  Eq.trans h₁ h₃

theorem consAppend (a : α) (as bs : List α) : (a::as) ++ bs = a::(as ++ bs) :=
reverseCoreReverseCore as [a] bs

theorem appendAssoc : ∀ (as bs cs : List α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
| []      bs cs := rfl
| (a::as) bs cs :=
  show ((a::as) ++ bs) ++ cs = (a::as) ++ (bs ++ cs),      from
  have h₁ : ((a::as) ++ bs) ++ cs = a::(as++bs) ++ cs,     from congrArg (++ cs) (consAppend a as bs),
  have h₂ : a::(as++bs) ++ cs     = a::((as++bs) ++ cs),   from consAppend a (as++bs) cs,
  have h₃ : a::((as++bs) ++ cs)   = a::(as ++ (bs ++ cs)), from congrArg (λ as, a::as) (appendAssoc as bs cs),
  have h₄ : a::(as ++ (bs ++ cs)) = (a::as ++ (bs ++ cs)), from (consAppend a as (bs++cs)).symm,
  Eq.trans (Eq.trans (Eq.trans h₁ h₂) h₃) h₄

protected def mem : α → List α → Prop
| a []       := False
| a (b :: l) := a = b ∨ mem a l

instance : HasMem α (List α) :=
⟨List.mem⟩

instance decidableMem [DecidableEq α] (a : α) : ∀ (l : List α), Decidable (a ∈ l)
| []     := isFalse notFalse
| (b::l) :=
  if h₁ : a = b then isTrue (Or.inl h₁)
  else match decidableMem l with
       | isTrue  h₂ := isTrue (Or.inr h₂)
       | isFalse h₂ := isFalse (notOr h₁ h₂)

instance : HasEmptyc (List α) :=
⟨List.nil⟩

protected def erase {α} [DecidableEq α] : List α → α → List α
| []     b := []
| (a::l) b := if a = b then l else a :: erase l b

protected def bagInter {α} [DecidableEq α] : List α → List α → List α
| []      _   := []
| _       []  := []
| (a::l₁) l₂  := if a ∈ l₂ then a :: bagInter l₁ (l₂.erase a) else bagInter l₁ l₂

protected def diff {α} [DecidableEq α] : List α → List α → List α
| l      []      := l
| l₁     (a::l₂) := if a ∈ l₁ then diff (l₁.erase a) l₂ else diff l₁ l₂

def lengthAux : List α → Nat → Nat
| []      n := n
| (a::as) n := lengthAux as (n+1)

def length (as : List α) : Nat :=
lengthAux as 0

def empty : List α → Bool
| []       := true
| (_ :: _) := false

open Option Nat

def nth : List α → Nat → Option α
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

def head [Inhabited α] : List α → α
| []       := default α
| (a :: l) := a

def tail : List α → List α
| []       := []
| (a :: l) := l

@[specialize] def map (f : α → β) : List α → List β
| []       := []
| (a :: l) := f a :: map l

@[specialize] def map₂ (f : α → β → γ) : List α → List β → List γ
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

def join : List (List α) → List α
| []        := []
| (l :: ls) := l ++ join ls

def filterMap (f : α → Option β) : List α → List β
| []     := []
| (a::l) :=
  match f a with
  | none   := filterMap l
  | some b := b :: filterMap l

def filter (p : α → Prop) [DecidablePred p] : List α → List α
| []     := []
| (a::l) := if p a then a :: filter l else filter l

def partition (p : α → Prop) [DecidablePred p] : List α → List α × List α
| []     := ([], [])
| (a::l) := let (l₁, l₂) := partition l in if p a then (a :: l₁, l₂) else (l₁, a :: l₂)

def dropWhile (p : α → Prop) [DecidablePred p] : List α → List α
| []     := []
| (a::l) := if p a then dropWhile l else a::l

def span (p : α → Prop) [DecidablePred p] : List α → List α × List α
| []      := ([], [])
| (a::xs) := if p a then let (l, r) := span xs in (a :: l, r) else ([], a::xs)

def findIndex (p : α → Prop) [DecidablePred p] : List α → Nat
| []     := 0
| (a::l) := if p a then 0 else succ (findIndex l)

def indexOf [DecidableEq α] (a : α) (l : List α) : Nat :=
findIndex (Eq a) l

def assoc [DecidableEq α] : List (α × β) → α → Option β
| []         _  := none
| ((a,b)::l) a' := if a = a' then some b else assoc l a'

def removeAll [DecidableEq α] (xs ys : List α) : List α :=
filter (∉ ys) xs

def updateNth : List α → ℕ → α → List α
| (x::xs) 0     a := a :: xs
| (x::xs) (i+1) a := x :: updateNth xs i a
| []      _     _ := []

def removeNth : List α → ℕ → List α
| []      _     := []
| (x::xs) 0     := xs
| (x::xs) (i+1) := x :: removeNth xs i

def drop : ℕ → List α → List α
| 0        a      := a
| (succ n) []     := []
| (succ n) (x::r) := drop n r

def take : ℕ → List α → List α
| 0        a        := []
| (succ n) []       := []
| (succ n) (x :: r) := x :: take n r

@[specialize] def foldl (f : α → β → α) : α → List β → α
| a []       := a
| a (b :: l) := foldl (f a b) l

@[specialize] def foldr (f : α → β → β) (b : β) : List α → β
| []       := b
| (a :: l) := f a (foldr l)

@[specialize] def foldr1 (f : α → α → α) : Π (xs : List α), xs ≠ [] → α
| []              nem := False.elim (nem rfl)
| [a]             nem := a
| (a :: l@(_::_)) nem := f a (foldr1 l (λ Eq, List.noConfusion Eq))

@[specialize] def foldr1Opt (f : α → α → α) : List α → Option α
| []       := none
| (a :: l) := some $ foldr1 f (a :: l) (λ Eq, List.noConfusion Eq)

@[inline] def any (l : List α) (p : α → Bool) : Bool :=
foldr (λ a r, p a || r) false l

@[inline] def all (l : List α) (p : α → Bool) : Bool :=
foldr (λ a r, p a && r) true l

def bor  (l : List Bool) : Bool := any l id

def band (l : List Bool) : Bool := all l id

def zipWith (f : α → β → γ) : List α → List β → List γ
| (x::xs) (y::ys) := f x y :: zipWith xs ys
| _       _       := []

def zip : List α → List β → List (Prod α β) :=
zipWith Prod.mk

def unzip : List (α × β) → List α × List β
| []            := ([], [])
| ((a, b) :: t) := match unzip t with | (al, bl) := (a::al, b::bl)

protected def insert [DecidableEq α] (a : α) (l : List α) : List α :=
if a ∈ l then l else a :: l

instance [DecidableEq α] : HasInsert α (List α) :=
⟨List.insert⟩

protected def union [DecidableEq α] (l₁ l₂ : List α) : List α :=
foldr insert l₂ l₁

instance [DecidableEq α] : HasUnion (List α) :=
⟨List.union⟩

protected def inter [DecidableEq α] (l₁ l₂ : List α) : List α :=
filter (∈ l₂) l₁

instance [DecidableEq α] : HasInter (List α) :=
⟨List.inter⟩

def repeat (a : α) (n : ℕ) : List α :=
n.repeat (λ _ xs, a :: xs) []

def rangeCore : ℕ → List ℕ → List ℕ
| 0        l := l
| (succ n) l := rangeCore n (n :: l)

def range (n : ℕ) : List ℕ :=
rangeCore n []

def iota : ℕ → List ℕ
| 0        := []
| (succ n) := succ n :: iota n

def enumFrom : ℕ → List α → List (ℕ × α)
| n [] := nil
| n (x :: xs) := (n, x) :: enumFrom (n + 1) xs

def enum : List α → List (ℕ × α) := enumFrom 0

def last : Π l : List α, l ≠ [] → α
| []        h := absurd rfl h
| [a]       h := a
| (a::b::l) h := last (b::l) (λ h, List.noConfusion h)

def ilast [Inhabited α] : List α → α
| []        := arbitrary α
| [a]       := a
| [a, b]    := b
| (a::b::l) := ilast l

def init : List α → List α
| []     := []
| [a]    := []
| (a::l) := a::init l

def intersperse (sep : α) : List α → List α
| []      := []
| [x]     := [x]
| (x::xs) := x::sep::intersperse xs

def intercalate (sep : List α) (xs : List (List α)) : List α :=
join (intersperse sep xs)

@[inline] protected def bind {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β :=
join (map b a)

@[inline] protected def ret {α : Type u} (a : α) : List α :=
[a]

protected def lt [HasLt α] : List α → List α → Prop
| []      []      := False
| []      (b::bs) := True
| (a::as) []      := False
| (a::as) (b::bs) := a < b ∨ (¬ b < a ∧ lt as bs)

instance [HasLt α] : HasLt (List α) :=
⟨List.lt⟩

instance hasDecidableLt [HasLt α] [h : DecidableRel ((<) : α → α → Prop)] : Π l₁ l₂ : List α, Decidable (l₁ < l₂)
| []      []      := isFalse notFalse
| []      (b::bs) := isTrue trivial
| (a::as) []      := isFalse notFalse
| (a::as) (b::bs) :=
  match h a b with
  | isTrue h₁  := isTrue (Or.inl h₁)
  | isFalse h₁ :=
    match h b a with
    | isTrue h₂  := isFalse (λ h, Or.elim h (λ h, absurd h h₁) (λ ⟨h, _⟩, absurd h₂ h))
    | isFalse h₂ :=
      match hasDecidableLt as bs with
      | isTrue h₃  := isTrue (Or.inr ⟨h₂, h₃⟩)
      | isFalse h₃ := isFalse (λ h, Or.elim h (λ h, absurd h h₁) (λ ⟨_, h⟩, absurd h h₃))

@[reducible] protected def le [HasLt α] (a b : List α) : Prop :=
¬ b < a

instance [HasLt α] : HasLe (List α) :=
⟨List.le⟩

instance hasDecidableLe [HasLt α] [h : DecidableRel ((<) : α → α → Prop)] : Π l₁ l₂ : List α, Decidable (l₁ ≤ l₂) :=
λ a b, Not.Decidable

lemma leEqNotGt [HasLt α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬ (l₂ < l₁) :=
λ l₁ l₂, rfl

lemma ltEqNotGe [HasLt α] [DecidableRel ((<) : α → α → Prop)] : ∀ l₁ l₂ : List α, (l₁ < l₂) = ¬ (l₂ ≤ l₁) :=
λ l₁ l₂,
  show (l₁ < l₂) = ¬ ¬ (l₁ < l₂), from
  Eq.subst (propext (notNotIff (l₁ < l₂))).symm rfl

/--  `isPrefixOf l₁ l₂` returns `true` Iff `l₁` is a prefix of `l₂`. -/
def isPrefixOf [DecidableEq α] : List α → List α → Bool
| []      _       := true
| _       []      := false
| (a::as) (b::bs) := toBool (a = b) && isPrefixOf as bs

/--  `isSuffixOf l₁ l₂` returns `true` Iff `l₁` is a suffix of `l₂`. -/
def isSuffixOf [DecidableEq α] (l₁ l₂ : List α) : Bool :=
isPrefixOf l₁.reverse l₂.reverse

end List

namespace BinTree
private def toListAux : BinTree α → List α → List α
| empty      as := as
| (leaf a)   as := a::as
| (node l r) as := toListAux l (toListAux r as)

def toList (t : BinTree α) : List α :=
toListAux t []
end BinTree
