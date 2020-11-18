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

instance (α : Type u) : Inhabited (List α) := ⟨List.nil⟩

variables {α : Type u} {β : Type v} {γ : Type w}

namespace List

def reverseAux : List α → List α → List α
  | [],   r => r
  | a::l, r => reverseAux l (a::r)

def reverse (as : List α) :List α :=
  reverseAux as []

protected def append (as bs : List α) : List α :=
  reverseAux as.reverse bs

instance : Append (List α) := ⟨List.append⟩

theorem reverseAuxReverseAuxNil : ∀ (as bs : List α), reverseAux (reverseAux as bs) [] = reverseAux bs as
  | [], bs     => rfl
  | a::as,  bs =>
    show reverseAux (reverseAux as (a::bs)) [] = reverseAux bs (a::as) from
    reverseAuxReverseAuxNil as (a::bs)

theorem nilAppend (as : List α) : [] ++ as = as := rfl

theorem appendNil (as : List α) : as ++ [] = as :=
  show reverseAux (reverseAux as []) [] = as from
  reverseAuxReverseAuxNil as []

theorem reverseAuxReverseAux : ∀ (as bs cs : List α), reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as []) cs)
  | [],    bs, cs => rfl
  | a::as, bs, cs => by
    rw [reverseAuxReverseAux as (a::bs) cs, reverseAuxReverseAux as [a] cs]
    exact rfl

theorem consAppend (a : α) (as bs : List α) : (a::as) ++ bs = a::(as ++ bs) :=
  reverseAuxReverseAux as [a] bs

theorem appendAssoc : ∀ (as bs cs : List α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
  | [],    bs, cs => rfl
  | a::as, bs, cs => by
    show ((a::as) ++ bs) ++ cs = (a::as) ++ (bs ++ cs)
    rw [consAppend, consAppend, appendAssoc, consAppend]
    exact rfl

instance : EmptyCollection (List α) := ⟨List.nil⟩

protected def erase {α} [BEq α] : List α → α → List α
  | [],    b => []
  | a::as, b => match a == b with
    | true  => as
    | false => a :: List.erase as b

def eraseIdx : List α → Nat → List α
  | [],    _   => []
  | a::as, 0   => as
  | a::as, n+1 => a :: eraseIdx as n

def isEmpty : List α → Bool
  | []     => true
  | _ :: _ => false

def set : List α → Nat → α → List α
  | a::as, 0,   b => b::as
  | a::as, n+1, b => a::(set as n b)
  | [],    _,   _ => []

@[specialize] def map (f : α → β) : List α → List β
  | []    => []
  | a::as => f a :: map f as

@[specialize] def map₂ (f : α → β → γ) : List α → List β → List γ
  | [],    _     => []
  | _,     []    => []
  | a::as, b::bs => f a b :: map₂ f as bs

def join : List (List α) → List α
  | []      => []
  | a :: as => a ++ join as

@[specialize] def filterMap (f : α → Option β) : List α → List β
  | []   => []
  | a::as =>
    match f a with
    | none   => filterMap f as
    | some b => b :: filterMap f as

@[specialize] def filterAux (p : α → Bool) : List α → List α → List α
  | [],    rs => rs.reverse
  | a::as, rs => match p a with
     | true  => filterAux p as (a::rs)
     | false => filterAux p as rs

@[inline] def filter (p : α → Bool) (as : List α) : List α :=
  filterAux p as []

@[specialize] def partitionAux (p : α → Bool) : List α → List α × List α → List α × List α
  | [],    (bs, cs) => (bs.reverse, cs.reverse)
  | a::as, (bs, cs) =>
    match p a with
    | true  => partitionAux p as (a::bs, cs)
    | false => partitionAux p as (bs, a::cs)

@[inline] def partition (p : α → Bool) (as : List α) : List α × List α :=
  partitionAux p as ([], [])

def dropWhile (p : α → Bool) : List α → List α
  | []   => []
  | a::l => match p a with
    | true  => dropWhile p l
    | false =>  a::l

def find? (p : α → Bool) : List α → Option α
  | []    => none
  | a::as => match p a with
    | true  => some a
    | false => find? p as

def findSome? (f : α → Option β) : List α → Option β
  | []    => none
  | a::as => match f a with
    | some b => some b
    | none   => findSome? f as

def replace [BEq α] : List α → α → α → List α
  | [],    _, _ => []
  | a::as, b, c => match a == b with
    | true  => c::as
    | flase => a :: (replace as b c)

def elem [BEq α] (a : α) : List α → Bool
  | []    => false
  | b::bs => match a == b with
    | true  => true
    | false => elem a bs

def notElem [BEq α] (a : α) (as : List α) : Bool :=
  !(as.elem a)

abbrev contains [BEq α] (as : List α) (a : α) : Bool :=
  elem a as

def eraseDupsAux {α} [BEq α] : List α → List α → List α
  | [],    bs => bs.reverse
  | a::as, bs => match bs.elem a with
    | true  => eraseDupsAux as bs
    | false => eraseDupsAux as (a::bs)

def eraseDups {α} [BEq α] (as : List α) : List α :=
  eraseDupsAux as []

def eraseRepsAux {α} [BEq α] : α → List α → List α → List α
  | a, [], rs => (a::rs).reverse
  | a, a'::as, rs => match a == a' with
    | true  => eraseRepsAux a as rs
    | false => eraseRepsAux a' as (a::rs)

/-- Erase repeated adjacent elements. -/
def eraseReps {α} [BEq α] : List α → List α
  | []    => []
  | a::as => eraseRepsAux a as []

@[specialize] def spanAux (p : α → Bool) : List α → List α → List α × List α
  | [],    rs => (rs.reverse, [])
  | a::as, rs => match p a with
    | true  => spanAux p as (a::rs)
    | false => (rs.reverse, a::as)

@[inline] def span (p : α → Bool) (as : List α) : List α × List α :=
  spanAux p as []

@[specialize] def groupByAux (eq : α → α → Bool) : List α → List (List α) → List (List α)
  | a::as, (ag::g)::gs => match eq a ag with
    | true  => groupByAux eq as ((a::ag::g)::gs)
    | false => groupByAux eq as ([a]::(ag::g).reverse::gs)
  | _, gs => gs.reverse

@[specialize] def groupBy (p : α → α → Bool) : List α → List (List α)
  | []    => []
  | a::as => groupByAux p as [[a]]

def lookup [BEq α] : α → List (α × β) → Option β
  | _, []        => none
  | a, (k,b)::es => match a == k with
    | true  => some b
    | false => lookup a es

def removeAll [BEq α] (xs ys : List α) : List α :=
  xs.filter (fun x => ys.notElem x)

def drop : Nat → List α → List α
  | 0,   a     => a
  | n+1, []    => []
  | n+1, a::as => drop n as

def take : Nat → List α → List α
  | 0,   a     => []
  | n+1, []    => []
  | n+1, a::as => a :: take n as

@[specialize] def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => f a (foldr f init l)

@[inline] def any (l : List α) (p : α → Bool) : Bool :=
  foldr (fun a r => p a || r) false l

@[inline] def all (l : List α) (p : α → Bool) : Bool :=
  foldr (fun a r => p a && r) true l

def or  (bs : List Bool) : Bool := bs.any id

def and (bs : List Bool) : Bool := bs.all id

def zipWith (f : α → β → γ) : List α → List β → List γ
  | x::xs, y::ys => f x y :: zipWith f xs ys
  | _,     _     => []

def zip : List α → List β → List (Prod α β) :=
  zipWith Prod.mk

def unzip : List (α × β) → List α × List β
  | []          => ([], [])
  | (a, b) :: t => match unzip t with | (al, bl) => (a::al, b::bl)

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
  | x::xs => x :: sep :: intersperse sep xs

def intercalate (sep : List α) (xs : List (List α)) : List α :=
  join (intersperse sep xs)

@[inline] protected def bind {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β := join (map b a)

@[inline] protected def pure {α : Type u} (a : α) : List α := [a]

inductive List.Less [HasLess α] : List α → List α → Prop
  | nil  (b : α) (bs : List α) : Less [] (b::bs)
  | head {a : α} (as : List α) {b : α} (bs : List α) : a < b → Less (a::as) (b::bs)
  | tail {a : α} {as : List α} {b : α} {bs : List α} : ¬ a < b → ¬ b < a → Less as bs → Less (a::as) (b::bs)

instance less [HasLess α] : HasLess (List α) := ⟨List.Less⟩

instance hasDecidableLt [HasLess α] [h : DecidableRel (α:=α) (·<·)] : (l₁ l₂ : List α) → Decidable (l₁ < l₂)
  | [],    []    => isFalse (fun h => nomatch h)
  | [],    b::bs => isTrue (List.Less.nil _ _)
  | a::as, []    => isFalse (fun h => nomatch h)
  | a::as, b::bs =>
    match h a b with
    | isTrue h₁  => isTrue (List.Less.head _ _ h₁)
    | isFalse h₁ =>
      match h b a with
      | isTrue h₂  => isFalse (fun h => match h with
         | List.Less.head _ _ h₁' => absurd h₁' h₁
         | List.Less.tail _ h₂' _ => absurd h₂ h₂')
      | isFalse h₂ =>
        match hasDecidableLt as bs with
        | isTrue h₃  => isTrue (List.Less.tail h₁ h₂ h₃)
        | isFalse h₃ => isFalse (fun h => match h with
           | List.Less.head _ _ h₁' => absurd h₁' h₁
           | List.Less.tail _ _ h₃' => absurd h₃' h₃)

@[reducible] protected def LessEq [HasLess α] (a b : List α) : Prop := ¬ b < a

instance lessEq [HasLess α] : HasLessEq (List α) := ⟨List.LessEq⟩

instance [HasLess α] [h : DecidableRel ((· < ·) : α → α → Prop)] : (l₁ l₂ : List α) → Decidable (l₁ ≤ l₂) :=
  fun a b => inferInstanceAs (Decidable (Not _))

/--  `isPrefixOf l₁ l₂` returns `true` Iff `l₁` is a prefix of `l₂`. -/
def isPrefixOf [BEq α] : List α → List α → Bool
  | [],    _     => true
  | _,     []    => false
  | a::as, b::bs => a == b && isPrefixOf as bs

/--  `isSuffixOf l₁ l₂` returns `true` Iff `l₁` is a suffix of `l₂`. -/
def isSuffixOf [BEq α] (l₁ l₂ : List α) : Bool :=
  isPrefixOf l₁.reverse l₂.reverse

@[specialize] def isEqv : List α → List α → (α → α → Bool) → Bool
  | [],    [],    _   => true
  | a::as, b::bs, eqv => eqv a b && isEqv as bs eqv
  | _,     _,     eqv => false

protected def beq [BEq α] : List α → List α → Bool
  | [],    []    => true
  | a::as, b::bs => a == b && List.beq as bs
  | _,     _     => false

instance [BEq α] : BEq (List α) := ⟨List.beq⟩

def replicate {α : Type u} (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0, as => as
    | n+1, as => loop n (a::as)
  loop n []

def dropLast {α} : List α → List α
  | []    => []
  | [a]   => []
  | a::as => a :: dropLast as

def lengthReplicateEq {α} (n : Nat) (a : α) : (replicate n a).length = n :=
  let rec aux (n : Nat) (as : List α) : (replicate.loop a n as).length = n + as.length := by
    induction n generalizing as
    | zero => rw [Nat.zeroAdd]; rfl
    | succ n ih =>
      show length (replicate.loop a n (a::as)) = Nat.succ n + length as
      rw [ih, lengthConsEq, Nat.addSucc, Nat.succAdd]
      rfl
  aux n []

def lengthConcatEq {α} (as : List α) (a : α) : (concat as a).length = as.length + 1 := by
  induction as
  | nil => rfl
  | cons x xs ih =>
    show length (x :: concat xs a) = length (x :: xs) + 1
    rw [lengthConsEq, lengthConsEq, ih]
    rfl

def lengthSetEq {α} (as : List α) (i : Nat) (a : α) : (as.set i a).length = as.length := by
  induction as generalizing i
  | nil => rfl
  | cons x xs ih =>
    cases i
    | zero => rfl
    | succ i =>
      show length (x :: set xs i a) = length (x :: xs)
      rw [lengthConsEq, lengthConsEq, ih]
      rfl

def lengthDropLast {α} (as : List α) : as.dropLast.length = as.length - 1 := by
  match as with
  | []       => rfl
  | [a]      => rfl
  | a::b::as =>
    have ih := lengthDropLast (b::as)
    show (a :: dropLast (b::as)).length = (a::b::as).length - 1
    rw [lengthConsEq, ih, lengthConsEq, lengthConsEq, lengthConsEq]
    rfl

end List
