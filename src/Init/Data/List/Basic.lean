/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Data.Nat.Basic
open Decidable List

universes u v w

instance (α : Type u) : Inhabited (List α) :=
⟨List.nil⟩

variables {α : Type u} {β : Type v} {γ : Type w}

namespace List

protected def hasDecEq [DecidableEq α] : ∀ (a b : List α), Decidable (a = b)
| [],    []    => isTrue rfl
| a::as, []    => isFalse (fun h => List.noConfusion h)
| [],    b::bs => isFalse (fun h => List.noConfusion h)
| a::as, b::bs =>
  match decEq a b with
  | isTrue hab  =>
    match hasDecEq as bs with
    | isTrue habs  => isTrue (Eq.subst hab (Eq.subst habs rfl))
    | isFalse nabs => isFalse (fun h => List.noConfusion h (fun _ habs => absurd habs nabs))
  | isFalse nab => isFalse (fun h => List.noConfusion h (fun hab _ => absurd hab nab))

instance [DecidableEq α] : DecidableEq (List α) :=
List.hasDecEq

def reverseAux : List α → List α → List α
| [],   r => r
| a::l, r => reverseAux l (a::r)

def reverse : List α → List α :=
fun l => reverseAux l []

protected def append (as bs : List α) : List α :=
reverseAux as.reverse bs

instance : HasAppend (List α) :=
⟨List.append⟩

theorem reverseAuxReverseAuxNil : ∀ (as bs : List α), reverseAux (reverseAux as bs) [] = reverseAux bs as
| [], bs     => rfl
| a::as,  bs =>
  show reverseAux (reverseAux as (a::bs)) [] = reverseAux bs (a::as) from
  reverseAuxReverseAuxNil as (a::bs)

theorem nilAppend (as : List α) : [] ++ as = as :=
rfl

theorem appendNil (as : List α) : as ++ [] = as :=
show reverseAux (reverseAux as []) [] = as from
reverseAuxReverseAuxNil as []

theorem reverseAuxReverseAux : ∀ (as bs cs : List α), reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as []) cs)
| [],    bs, cs => rfl
| a::as, bs, cs =>
  Eq.trans
    (reverseAuxReverseAux as (a::bs) cs)
    (congrArg (fun b => reverseAux bs b) (reverseAuxReverseAux as [a] cs).symm)

theorem consAppend (a : α) (as bs : List α) : (a::as) ++ bs = a::(as ++ bs) :=
reverseAuxReverseAux as [a] bs

theorem appendAssoc : ∀ (as bs cs : List α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
| [],    bs, cs => rfl
| a::as, bs, cs =>
  show ((a::as) ++ bs) ++ cs = (a::as) ++ (bs ++ cs)      from
  have h₁ : ((a::as) ++ bs) ++ cs = a::(as++bs) ++ cs     from congrArg (fun ds => ds ++ cs) (consAppend a as bs);
  have h₂ : a::(as++bs) ++ cs     = a::((as++bs) ++ cs)   from consAppend a (as++bs) cs;
  have h₃ : a::((as++bs) ++ cs)   = a::(as ++ (bs ++ cs)) from congrArg (fun as => a::as) (appendAssoc as bs cs);
  have h₄ : a::(as ++ (bs ++ cs)) = (a::as ++ (bs ++ cs)) from (consAppend a as (bs++cs)).symm;
  Eq.trans (Eq.trans (Eq.trans h₁ h₂) h₃) h₄

instance : HasEmptyc (List α) :=
⟨List.nil⟩

protected def erase {α} [HasBeq α] : List α → α → List α
| [],    b => []
| a::as, b => match a == b with
  | true  => as
  | false => a :: erase as b

def eraseIdx : List α → Nat → List α
| [],    _   => []
| a::as, 0   => as
| a::as, n+1 => a :: eraseIdx as n

def lengthAux : List α → Nat → Nat
| [],    n => n
| a::as, n => lengthAux as (n+1)

def length (as : List α) : Nat :=
lengthAux as 0

def isEmpty : List α → Bool
| []     => true
| _ :: _ => false

def set : List α → Nat → α → List α
| a::as, 0,   b => b::as
| a::as, n+1, b => a::(set as n b)
| [],    _,   _ => []

@[specialize] def map (f : α → β) : List α → List β
| []    => []
| a::as => f a :: map as

@[specialize] def map₂ (f : α → β → γ) : List α → List β → List γ
| [],    _     => []
| _,     []    => []
| a::as, b::bs => f a b :: map₂ as bs

def join : List (List α) → List α
| []      => []
| a :: as => a ++ join as

@[specialize] def filterMap (f : α → Option β) : List α → List β
| []   => []
| a::as =>
  match f a with
  | none   => filterMap as
  | some b => b :: filterMap as

@[specialize] def filterAux (p : α → Bool) : List α → List α → List α
| [],    rs => rs.reverse
| a::as, rs => match p a with
   | true  => filterAux as (a::rs)
   | false => filterAux as rs

@[inline] def filter (p : α → Bool) (as : List α) : List α :=
filterAux p as []

@[specialize] def partitionAux (p : α → Bool) : List α → List α × List α → List α × List α
| [],    (bs, cs) => (bs.reverse, cs.reverse)
| a::as, (bs, cs) =>
  match p a with
  | true  => partitionAux as (a::bs, cs)
  | false => partitionAux as (bs, a::cs)

@[inline] def partition (p : α → Bool) (as : List α) : List α × List α :=
partitionAux p as ([], [])

def dropWhile (p : α → Bool) : List α → List α
| []   => []
| a::l => match p a with
  | true  => dropWhile l
  | false =>  a::l

def find (p : α → Bool) : List α → Option α
| []    => none
| a::as => match p a with
  | true  => some a
  | false => find as

def findSome? (f : α → Option β) : List α → Option β
| []    => none
| a::as => match f a with
  | some b => some b
  | none   => findSome? as

def elem [HasBeq α] (a : α) : List α → Bool
| []    => false
| b::bs => match a == b with
  | true  => true
  | false => elem bs

def notElem [HasBeq α] (a : α) (as : List α) : Bool :=
!(as.elem a)

abbrev contains [HasBeq α] (as : List α) (a : α) : Bool :=
elem a as

def eraseDupsAux {α} [HasBeq α] : List α → List α → List α
| [],    bs => bs.reverse
| a::as, bs => match bs.elem a with
  | true  => eraseDupsAux as bs
  | false => eraseDupsAux as (a::bs)

def eraseDups {α} [HasBeq α] (as : List α) : List α :=
eraseDupsAux as []

@[specialize] def spanAux (p : α → Bool) : List α → List α → List α × List α
| [],    rs => (rs.reverse, [])
| a::as, rs => match p a with
  | true  => spanAux as (a::rs)
  | false => (rs.reverse, a::as)

@[inline] def span (p : α → Bool) (as : List α) : List α × List α :=
spanAux p as []

def lookup [HasBeq α] : α → List (α × β) → Option β
| _, []        => none
| a, (k,b)::es => match a == k with
  | true  => some b
  | false => lookup a es

def removeAll [HasBeq α] (xs ys : List α) : List α :=
xs.filter (fun x => ys.notElem x)

def drop : Nat → List α → List α
| 0,   a     => a
| n+1, []    => []
| n+1, a::as => drop n as

def take : Nat → List α → List α
| 0,   a     => []
| n+1, []    => []
| n+1, a::as => a :: take n as

@[specialize] def foldl (f : α → β → α) : α → List β → α
| a, []     => a
| a, b :: l => foldl (f a b) l

@[specialize] def foldr (f : α → β → β) (b : β) : List α → β
| []     => b
| a :: l => f a (foldr l)

@[specialize] def foldr1 (f : α → α → α) : ∀ (xs : List α), xs ≠ [] → α
| [],             h => absurd rfl h
| [a],            _ => a
| a :: as@(_::_), _ => f a (foldr1 as (fun h => List.noConfusion h))

@[specialize] def foldr1Opt (f : α → α → α) : List α → Option α
| []      => none
| a :: as => some $ foldr1 f (a :: as) (fun h => List.noConfusion h)

@[inline] def any (l : List α) (p : α → Bool) : Bool :=
foldr (fun a r => p a || r) false l

@[inline] def all (l : List α) (p : α → Bool) : Bool :=
foldr (fun a r => p a && r) true l

def or  (bs : List Bool) : Bool := bs.any id

def and (bs : List Bool) : Bool := bs.all id

def zipWith (f : α → β → γ) : List α → List β → List γ
| x::xs, y::ys => f x y :: zipWith xs ys
| _,     _     => []

def zip : List α → List β → List (Prod α β) :=
zipWith Prod.mk

def unzip : List (α × β) → List α × List β
| []          => ([], [])
| (a, b) :: t => match unzip t with | (al, bl) => (a::al, b::bl)

def replicate (n : Nat) (a : α) : List α :=
n.repeat (fun xs => a :: xs) []

def rangeAux : Nat → List Nat → List Nat
| 0,   ns => ns
| n+1, ns => rangeAux n (n::ns)

def range (n : Nat) : List Nat :=
rangeAux n []

def iota : Nat → List Nat
| 0       => []
| m@(n+1) => m :: iota n

def enumFrom : Nat → List α → List (Nat × α)
| n, [] => nil
| n, x :: xs   => (n, x) :: enumFrom (n + 1) xs

def enum : List α → List (Nat × α) := enumFrom 0

def init : List α → List α
| []   => []
| [a]  => []
| a::l => a::init l

def intersperse (sep : α) : List α → List α
| []    => []
| [x]   => [x]
| x::xs => x::sep::intersperse xs

def intercalate (sep : List α) (xs : List (List α)) : List α :=
join (intersperse sep xs)

@[inline] protected def bind {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β :=
join (map b a)

@[inline] protected def pure {α : Type u} (a : α) : List α :=
[a]

inductive Less [HasLess α] : List α → List α → Prop
| nil  (b : α) (bs : List α) : Less [] (b::bs)
| head {a : α} (as : List α) {b : α} (bs : List α) : a < b → Less (a::as) (b::bs)
| tail {a : α} {as : List α} {b : α} {bs : List α} : ¬ a < b → ¬ b < a → Less as bs → Less (a::as) (b::bs)

instance [HasLess α] : HasLess (List α) :=
⟨List.Less⟩

instance hasDecidableLt [HasLess α] [h : DecidableRel HasLess.Less] : ∀ (l₁ l₂ : List α), Decidable (l₁ < l₂)
| [],    []    => isFalse (fun h => nomatch h)
| [],    b::bs => isTrue (Less.nil _ _)
| a::as, []    => isFalse (fun h => nomatch h)
| a::as, b::bs =>
  match h a b with
  | isTrue h₁  => isTrue (Less.head _ _ h₁)
  | isFalse h₁ =>
    match h b a with
    | isTrue h₂  => isFalse (fun h => match h with
       | Less.head _ _ h₁' => absurd h₁' h₁
       | Less.tail _ h₂' _ => absurd h₂ h₂')
    | isFalse h₂ =>
      match hasDecidableLt as bs with
      | isTrue h₃  => isTrue (Less.tail h₁ h₂ h₃)
      | isFalse h₃ => isFalse (fun h => match h with
         | Less.head _ _ h₁' => absurd h₁' h₁
         | Less.tail _ _ h₃' => absurd h₃' h₃)

@[reducible] protected def LessEq [HasLess α] (a b : List α) : Prop :=
¬ b < a

instance [HasLess α] : HasLessEq (List α) :=
⟨List.LessEq⟩

instance hasDecidableLe [HasLess α] [h : DecidableRel (HasLess.Less : α → α → Prop)] : ∀ (l₁ l₂ : List α), Decidable (l₁ ≤ l₂) :=
fun a b => Not.Decidable

/--  `isPrefixOf l₁ l₂` returns `true` Iff `l₁` is a prefix of `l₂`. -/
def isPrefixOf [HasBeq α] : List α → List α → Bool
| [],    _     => true
| _,     []    => false
| a::as, b::bs => a == b && isPrefixOf as bs

/--  `isSuffixOf l₁ l₂` returns `true` Iff `l₁` is a suffix of `l₂`. -/
def isSuffixOf [HasBeq α] (l₁ l₂ : List α) : Bool :=
isPrefixOf l₁.reverse l₂.reverse

@[specialize] def isEqv : List α → List α → (α → α → Bool) → Bool
| [],    [],    _   => true
| a::as, b::bs, eqv => eqv a b && isEqv as bs eqv
| _,     _,     eqv => false

protected def beq [HasBeq α] : List α → List α → Bool
| [],    []    => true
| a::as, b::bs => a == b && beq as bs
| _,     _     => false

instance [HasBeq α] : HasBeq (List α) := ⟨List.beq⟩

end List
