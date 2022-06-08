/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.Data.Nat.Basic
open Decidable List

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

theorem length_add_eq_lengthTRAux (as : List α) (n : Nat) : as.length + n = as.lengthTRAux n := by
  induction as generalizing n with
  | nil  => simp [length, lengthTRAux]
  | cons a as ih =>
    simp [length, lengthTRAux, ← ih, Nat.succ_add]
    rfl

@[csimp] theorem length_eq_lengthTR : @List.length = @List.lengthTR := by
  apply funext; intro α; apply funext; intro as
  simp [lengthTR, ← length_add_eq_lengthTRAux]

@[simp] theorem length_nil : length ([] : List α) = 0 :=
  rfl

def reverseAux : List α → List α → List α
  | [],   r => r
  | a::l, r => reverseAux l (a::r)

def reverse (as : List α) :List α :=
  reverseAux as []

theorem reverseAux_reverseAux_nil (as bs : List α) : reverseAux (reverseAux as bs) [] = reverseAux bs as := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih]

theorem reverseAux_reverseAux (as bs cs : List α) : reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as []) cs) := by
  induction as generalizing bs cs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih (a::bs), ih [a]]

@[simp] theorem reverse_reverse (as : List α) : as.reverse.reverse = as := by
  simp [reverse]; rw [reverseAux_reverseAux_nil]; rfl

protected def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: List.append as bs

def appendTR (as bs : List α) : List α :=
  reverseAux as.reverse bs

@[csimp] theorem append_eq_appendTR : @List.append = @appendTR := by
  apply funext; intro α; apply funext; intro as; apply funext; intro bs
  simp [appendTR, reverse]
  induction as with
  | nil  => rfl
  | cons a as ih =>
    simp [reverseAux, List.append, ih, reverseAux_reverseAux]

instance : Append (List α) := ⟨List.append⟩

@[simp] theorem nil_append (as : List α) : [] ++ as = as := rfl
@[simp] theorem append_nil (as : List α) : as ++ [] = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp_all [HAppend.hAppend, Append.append, List.append]

@[simp] theorem cons_append (a : α) (as bs : List α) : (a::as) ++ bs = a::(as ++ bs) := rfl

@[simp] theorem List.append_eq (as bs : List α) : List.append as bs = as ++ bs := rfl

theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem append_cons (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

instance : EmptyCollection (List α) := ⟨List.nil⟩

protected def erase {α} [BEq α] : List α → α → List α
  | [],    _ => []
  | a::as, b => match a == b with
    | true  => as
    | false => a :: List.erase as b

def eraseIdx : List α → Nat → List α
  | [],    _   => []
  | _::as, 0   => as
  | a::as, n+1 => a :: eraseIdx as n

def isEmpty : List α → Bool
  | []     => true
  | _ :: _ => false

@[specialize] def map (f : α → β) : List α → List β
  | []    => []
  | a::as => f a :: map f as

@[specialize] def mapTRAux (f : α → β) : List α → List β → List β
  | [],    bs => bs.reverse
  | a::as, bs => mapTRAux f as (f a :: bs)

@[inline] def mapTR (f : α → β) (as : List α) : List β :=
  mapTRAux f as []

theorem reverseAux_eq_append (as bs : List α) : reverseAux as bs = reverseAux as [] ++ bs := by
  induction as generalizing bs with
  | nil => simp [reverseAux]
  | cons a as ih =>
    simp [reverseAux]
    rw [ih (a :: bs), ih [a], append_assoc]
    rfl

@[simp] theorem reverse_nil : reverse ([] : List α) = [] :=
  rfl

@[simp] theorem reverse_cons (a : α) (as : List α) : reverse (a :: as) = reverse as ++ [a] := by
  simp [reverse, reverseAux]
  rw [← reverseAux_eq_append]

@[simp] theorem reverse_append (as bs : List α) : (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih => simp [ih]; rw [append_assoc]

theorem mapTRAux_eq (f : α → β) (as : List α) (bs : List β) : mapTRAux f as bs =  bs.reverse ++ map f as := by
  induction as generalizing bs with
  | nil => simp [mapTRAux, map]
  | cons a as ih =>
    simp [mapTRAux, map]
    rw [ih (f a :: bs), reverse_cons, append_assoc]
    rfl

@[csimp] theorem map_eq_mapTR : @map = @mapTR := by
  apply funext; intro α; apply funext; intro β; apply funext; intro f; apply funext; intro as
  simp [mapTR, mapTRAux_eq]

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
    | false => a :: (replace as b c)

def elem [BEq α] (a : α) : List α → Bool
  | []    => false
  | b::bs => match a == b with
    | true  => true
    | false => elem a bs

def notElem [BEq α] (a : α) (as : List α) : Bool :=
  !(as.elem a)

abbrev contains [BEq α] (as : List α) (a : α) : Bool :=
  elem a as

inductive Mem : α → List α → Prop
  | head (a : α) (as : List α) : Mem a (a::as)
  | tail (a : α) {b : α} {as : List α} : Mem b as → Mem b (a::as)

instance : Membership α (List α) where
  mem := Mem

theorem mem_of_elem_eq_true [DecidableEq α] {a : α} {as : List α} : elem a as = true → a ∈ as := by
  match as with
  | [] => simp [elem]
  | a'::as =>
    simp [elem]
    split
    next h => intros; simp [BEq.beq] at h; subst h; apply Mem.head
    next _ => intro h; exact Mem.tail _ (mem_of_elem_eq_true h)

theorem elem_eq_true_of_mem [DecidableEq α] {a : α} {as : List α} (h : a ∈ as) : elem a as = true := by
  induction h with
  | head _ => simp [elem]
  | tail _ _ ih => simp [elem]; split; rfl; assumption

instance [DecidableEq α] (a : α) (as : List α) : Decidable (a ∈ as) :=
  decidable_of_decidable_of_iff (Iff.intro mem_of_elem_eq_true elem_eq_true_of_mem)

theorem mem_append_of_mem_left {a : α} {as : List α} (bs : List α) : a ∈ as → a ∈ as ++ bs := by
  intro h
  induction h with
  | head => apply Mem.head
  | tail => apply Mem.tail; assumption

theorem mem_append_of_mem_right {b : α} {bs : List α} (as : List α) : b ∈ bs → b ∈ as ++ bs := by
  intro h
  induction as with
  | nil  => simp [h]
  | cons => apply Mem.tail; assumption

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
  | _+1, []    => []
  | n+1, _::as => drop n as

def take : Nat → List α → List α
  | 0,   _     => []
  | _+1, []    => []
  | n+1, a::as => a :: take n as

def takeWhile (p : α → Bool) : List α → List α
  | []       => []
  | hd :: tl => match p hd with
   | true  => hd :: takeWhile p tl
   | false => []

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

def iotaTR (n : Nat) : List Nat :=
  let rec go : Nat → List Nat → List Nat
    | 0, r => r.reverse
    | m@(n+1), r => go n (m::r)
  go n []

@[csimp]
theorem iota_eq_iotaTR : @iota = @iotaTR :=
  have aux (n : Nat) (r : List Nat) : iotaTR.go n r = r.reverse ++ iota n := by
    induction n generalizing r with
    | zero => simp [iota, iotaTR.go]
    | succ n ih => simp [iota, iotaTR.go, ih, append_assoc]
  funext fun n => by simp [iotaTR, aux]

def enumFrom : Nat → List α → List (Nat × α)
  | _, [] => nil
  | n, x :: xs   => (n, x) :: enumFrom (n + 1) xs

def enum : List α → List (Nat × α) := enumFrom 0

def init : List α → List α
  | []   => []
  | [_]  => []
  | a::l => a::init l

def intersperse (sep : α) : List α → List α
  | []    => []
  | [x]   => [x]
  | x::xs => x :: sep :: intersperse sep xs

def intercalate (sep : List α) (xs : List (List α)) : List α :=
  join (intersperse sep xs)

@[inline] protected def bind {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β := join (map b a)

@[inline] protected def pure {α : Type u} (a : α) : List α := [a]

inductive lt [LT α] : List α → List α → Prop where
  | nil  (b : α) (bs : List α) : lt [] (b::bs)
  | head {a : α} (as : List α) {b : α} (bs : List α) : a < b → lt (a::as) (b::bs)
  | tail {a : α} {as : List α} {b : α} {bs : List α} : ¬ a < b → ¬ b < a → lt as bs → lt (a::as) (b::bs)

instance [LT α] : LT (List α) := ⟨List.lt⟩

instance hasDecidableLt [LT α] [h : DecidableRel (α:=α) (·<·)] : (l₁ l₂ : List α) → Decidable (l₁ < l₂)
  | [],    []    => isFalse (fun h => nomatch h)
  | [],    _::_  => isTrue (List.lt.nil _ _)
  | _::_, []     => isFalse (fun h => nomatch h)
  | a::as, b::bs =>
    match h a b with
    | isTrue h₁  => isTrue (List.lt.head _ _ h₁)
    | isFalse h₁ =>
      match h b a with
      | isTrue h₂  => isFalse (fun h => match h with
         | List.lt.head _ _ h₁' => absurd h₁' h₁
         | List.lt.tail _ h₂' _ => absurd h₂ h₂')
      | isFalse h₂ =>
        match hasDecidableLt as bs with
        | isTrue h₃  => isTrue (List.lt.tail h₁ h₂ h₃)
        | isFalse h₃ => isFalse (fun h => match h with
           | List.lt.head _ _ h₁' => absurd h₁' h₁
           | List.lt.tail _ _ h₃' => absurd h₃' h₃)

@[reducible] protected def le [LT α] (a b : List α) : Prop := ¬ b < a

instance [LT α] : LE (List α) := ⟨List.le⟩

instance [LT α] [DecidableRel ((· < ·) : α → α → Prop)] : (l₁ l₂ : List α) → Decidable (l₁ ≤ l₂) :=
  fun _ _ => inferInstanceAs (Decidable (Not _))

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
  | _,     _,     _   => false

protected def beq [BEq α] : List α → List α → Bool
  | [],    []    => true
  | a::as, b::bs => a == b && List.beq as bs
  | _,     _     => false

instance [BEq α] : BEq (List α) := ⟨List.beq⟩

@[simp] def replicate : (n : Nat) → (a : α) → List α
  | 0,   _ => []
  | n+1, a => a :: replicate n a

def replicateTR {α : Type u} (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0, as => as
    | n+1, as => loop n (a::as)
  loop n []

theorem replicateTR_loop_replicate_eq (a : α) (m n : Nat) :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n generalizing m with simp [replicateTR.loop]
  | succ n ih => simp [Nat.succ_add]; exact ih (m+1)

@[csimp] theorem replicate_eq_replicateTR : @List.replicate = @List.replicateTR := by
  apply funext; intro α; apply funext; intro n; apply funext; intro a
  exact (replicateTR_loop_replicate_eq _ 0 n).symm

def dropLast {α} : List α → List α
  | []    => []
  | [_]   => []
  | a::as => a :: dropLast as

@[simp] theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  induction n <;> simp_all

@[simp] theorem length_concat (as : List α) (a : α) : (concat as a).length = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons _ xs ih => simp [concat, ih]

@[simp] theorem length_set (as : List α) (i : Nat) (a : α) : (as.set i a).length = as.length := by
  induction as generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [set, ih]

@[simp] theorem length_dropLast_cons (a : α) (as : List α) : (a :: as).dropLast.length = as.length := by
  match as with
  | []       => rfl
  | b::bs =>
    have ih := length_dropLast_cons b bs
    simp[dropLast, ih]

@[simp] theorem length_append (as bs : List α) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp
  | cons _ as ih => simp [ih, Nat.succ_add]

@[simp] theorem length_map (as : List α) (f : α → β) : (as.map f).length = as.length := by
  induction as with
  | nil => simp [List.map]
  | cons _ as ih => simp [List.map, ih]

@[simp] theorem length_reverse (as : List α) : (as.reverse).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

def maximum? [LT α] [DecidableRel (@LT.lt α _)] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl max a

def minimum? [LE α] [DecidableRel (@LE.le α _)] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl min a

instance [BEq α] [LawfulBEq α] : LawfulBEq (List α) where
  eq_of_beq as bs := by
    induction as generalizing bs with
    | nil => intro h; cases bs <;> first | rfl | contradiction
    | cons a as ih =>
      cases bs with
      | nil => intro h; contradiction
      | cons b bs =>
        simp [BEq.beq, List.beq]
        intro ⟨h₁, h₂⟩
        exact ⟨eq_of_beq h₁, ih _ h₂⟩
  rfl as := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [BEq.beq, List.beq, LawfulBEq.rfl]; exact ih

theorem of_concat_eq_concat {as bs : List α} {a b : α} (h : as.concat a = bs.concat b) : as = bs ∧ a = b := by
  match as, bs with
  | [], [] => simp [concat] at h; simp [h]
  | [_], [] => simp [concat] at h
  | _::_::_, [] => simp [concat] at h
  | [], [_] => simp [concat] at h
  | [], _::_::_ => simp [concat] at h
  | _::_, _::_ => simp [concat] at h; simp [h]; apply of_concat_eq_concat h.2

end List
