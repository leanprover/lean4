/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
universes u v w

inductive LazyList (α : Type u)
| nil {}                        : LazyList
| cons (hd : α) (tl : LazyList) : LazyList
| delayed (t : Thunk LazyList)  : LazyList

@[extern cpp inline "#2"]
def List.toLazy {α : Type u} : List α → LazyList α
| []     := LazyList.nil
| (h::t) := LazyList.cons h (List.toLazy t)

namespace LazyList
variable {α : Type u} {β : Type v} {δ : Type w}

instance : Inhabited (LazyList α) :=
⟨nil⟩

@[inline] protected def pure : α → LazyList α
| a := cons a nil

partial def get : LazyList α → LazyList α
| (delayed as) := get as.get
| other        := other

partial def isEmpty : LazyList α → Bool
| nil          := true
| (cons _ _)   := false
| (delayed as) := isEmpty as.get

partial def toList : LazyList α → List α
| nil          := []
| (cons a as)  := a :: toList as
| (delayed as) := toList as.get

partial def head [Inhabited α] : LazyList α → α
| nil          := default α
| (cons a as)  := a
| (delayed as) := head as.get

partial def tail : LazyList α → LazyList α
| nil          := nil
| (cons a as)  := as
| (delayed as) := tail as.get

partial def append : LazyList α → LazyList α → LazyList α
| nil          bs := bs
| (cons a as)  bs := cons a (delayed (append as bs))
| (delayed as) bs := append as.get bs

instance : Append (LazyList α) :=
⟨LazyList.append⟩

partial def interleave : LazyList α → LazyList α → LazyList α
| nil          bs  := bs
| (cons a as)  bs  := cons a (delayed (interleave bs as))
| (delayed as) bs  := interleave as.get bs

@[specialize] partial def map (f : α → β) : LazyList α → LazyList β
| nil          := nil
| (cons a as)  := cons (f a) (delayed (map as))
| (delayed as) := map as.get

@[specialize] partial def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
| nil          _            := nil
| _            nil          := nil
| (cons a as)  (cons b bs)  := cons (f a b) (delayed (map₂ as bs))
| (delayed as) bs           := map₂ as.get bs
| as           (delayed bs) := map₂ as bs.get

@[inline] def zip : LazyList α → LazyList β → LazyList (α × β) :=
map₂ Prod.mk

partial def join : LazyList (LazyList α) → LazyList α
| nil          := nil
| (cons a as)  := append a (delayed (join as))
| (delayed as) := join as.get

@[inline] protected partial def bind (x : LazyList α) (f : α → LazyList β) : LazyList β :=
join (x.map f)

instance isMonad : Monad LazyList :=
{ pure := @LazyList.pure, bind := @LazyList.bind, map := @LazyList.map }

instance : Alternative LazyList :=
{ failure := λ _, nil,
  orelse  := @LazyList.append,
  .. LazyList.isMonad }

partial def approx : Nat → LazyList α → List α
| 0     as           := []
| _     nil          := []
| (i+1) (cons a as)  := a :: approx i as
| (i+1) (delayed as) := approx (i+1) as.get

@[specialize] partial def iterate (f : α → α) : α → LazyList α
| x := cons x (delayed (iterate (f x)))

@[specialize] partial def iterate₂ (f : α → α → α) : α → α → LazyList α
| x y := cons x (delayed (iterate₂ y (f x y)))

@[specialize] partial def filter (p : α → Bool) : LazyList α → LazyList α
| nil          := nil
| (cons a as)  := if p a then cons a (delayed (filter as)) else filter as
| (delayed as) := filter as.get

partial def cycle : LazyList α → LazyList α
| xs := xs ++ delayed (cycle xs)

partial def repeat : α → LazyList α
| a := cons a (delayed (repeat a))

partial def inits : LazyList α → LazyList (LazyList α)
| nil          := cons nil nil
| (cons a as)  := cons nil (delayed (map (λ as, cons a as) (inits as)))
| (delayed as) := inits as.get

private def addOpenBracket (s : String) : String :=
if s.isEmpty then "[" else s

partial def approxToStringAux [ToString α] : Nat → LazyList α → String → String
| _     nil          r := (if r.isEmpty then "[" else r) ++ "]"
| 0     _            r := (if r.isEmpty then "[" else r) ++ ", ..]"
| (n+1) (cons a as)  r := approxToStringAux n as ((if r.isEmpty then "[" else r ++ ", ") ++ toString a)
| n     (delayed as) r := approxToStringAux n as.get r

def approxToString [ToString α] (as : LazyList α) (n : Nat := 10) : String :=
as.approxToStringAux n ""

instance [ToString α] : ToString (LazyList α) :=
⟨approxToString⟩

end LazyList

def fib : LazyList Nat :=
LazyList.iterate₂ (+) 0 1

def tst : LazyList String :=
do x ← [1, 2, 3].toLazy,
   y ← [2, 3, 4].toLazy,
   -- dbgTrace (toString x ++ " " ++ toString y) $ λ _,
   guard (x + y > 5),
   pure (toString x ++ " + " ++ toString y ++ " = " ++ toString (x+y))

open LazyList

def iota (i : UInt32 := 0) : LazyList UInt32 :=
iterate (+1) i

set_option pp.implicit true
set_option trace.compiler.ir.result true

partial def sieve : LazyList UInt32 → LazyList UInt32
| nil          := nil
| (cons a as)  := cons a (delayed (sieve (filter (λ b, b % a != 0) as)))
| (delayed as) := sieve as.get

partial def primes : LazyList UInt32 :=
sieve (iota 2)

def main : IO Unit :=
do let n := 10,
   -- IO.println $ tst.isEmpty,
   -- IO.println $ [1, 2, 3].toLazy.cycle,
   -- IO.println $ [1, 2, 3].toLazy.cycle.inits,
   -- IO.println $ ((iota.filter (λ v, v % 5 == 0)).approx 50000).foldl (+) 0,
   IO.println $ (primes.approx 2000).foldl (+) 0,
   -- IO.println $ tst.head,
   -- IO.println $ fib.interleave (iota.map (+100)),
   -- IO.println $ ((iota.map (+10)).filter (λ v, v % 2 == 0)),
   pure ()
