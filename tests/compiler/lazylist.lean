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

@[extern c inline "#2"]
def List.toLazy {α : Type u} : List α → LazyList α
| []     => LazyList.nil
| h::t   => LazyList.cons h (List.toLazy t)

namespace LazyList
variables {α : Type u} {β : Type v} {δ : Type w}

instance : Inhabited (LazyList α) :=
⟨nil⟩

@[inline] def pure : α → LazyList α
| a => cons a nil

partial def isEmpty : LazyList α → Bool
| nil          => true
| cons _ _     => false
| delayed as   => isEmpty as.get

partial def toList : LazyList α → List α
| nil          => []
| cons a as    => a :: toList as
| delayed as   => toList as.get

partial def head [Inhabited α] : LazyList α → α
| nil          => default α
| cons a as    => a
| delayed as   => head as.get

partial def tail : LazyList α → LazyList α
| nil          => nil
| cons a as    => as
| delayed as   => tail as.get

partial def append : LazyList α → LazyList α → LazyList α
| nil,          bs => bs
| cons a as,    bs => delayed (cons a (append as bs))
| delayed as,   bs => delayed (append as.get bs)

instance : HasAppend (LazyList α) :=
⟨LazyList.append⟩

partial def interleave : LazyList α → LazyList α → LazyList α
| nil,          bs  => bs
| cons a as,    bs  => delayed (cons a (interleave bs as))
| delayed as,   bs  => delayed (interleave as.get bs)

partial def map (f : α → β) : LazyList α → LazyList β
| nil          => nil
| cons a as    => delayed (cons (f a) (map as))
| delayed as   => delayed (map as.get)

partial def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
| nil,          _            => nil
| _,            nil          => nil
| cons a as,    cons b bs    => delayed (cons (f a b) (map₂ as bs))
| delayed as,   bs           => delayed (map₂ as.get bs)
| as,           delayed bs   => delayed (map₂ as bs.get)

@[inline] def zip : LazyList α → LazyList β → LazyList (α × β) :=
map₂ Prod.mk

partial def join : LazyList (LazyList α) → LazyList α
| nil          => nil
| cons a as    => delayed (append a (join as))
| delayed as   => delayed (join as.get)

@[inline] partial def bind (x : LazyList α) (f : α → LazyList β) : LazyList β :=
join (x.map f)

instance isMonad : Monad LazyList :=
{ pure := @LazyList.pure, bind := @LazyList.bind, map := @LazyList.map }

instance : Alternative LazyList :=
{ failure := fun _ => nil,
  orelse  := @LazyList.append,
  .. LazyList.isMonad }

partial def approx : Nat → LazyList α → List α
| 0,     as           => []
| _,     nil          => []
| i+1,   cons a as    => a :: approx i as
| i+1,   delayed as   => approx (i+1) as.get

partial def iterate (f : α → α) : α → LazyList α
| x => cons x (delayed (iterate (f x)))

partial def iterate₂ (f : α → α → α) : α → α → LazyList α
| x, y => cons x (delayed (iterate₂ y (f x y)))

partial def filter (p : α → Bool) : LazyList α → LazyList α
| nil          => nil
| cons a as    => delayed (if p a then cons a (filter as) else filter as)
| delayed as   => delayed (filter as.get)

end LazyList

def fib : LazyList Nat :=
LazyList.iterate₂ Nat.add 0 1

def iota (i : Nat := 0) : LazyList Nat :=
LazyList.iterate Nat.succ i

def tst : LazyList String :=
do x ← [1, 2, 3].toLazy;
   y ← [2, 3, 4].toLazy;
   guard (x + y > 5);
   pure (toString x ++ " + " ++ toString y ++ " = " ++ toString (x+y))

def main : IO Unit :=
do let n := 40;
   IO.println $ tst.isEmpty;
   IO.println $ tst.head;
   IO.println $ (fib.interleave (iota.map (fun a => a + 100))).approx n;
   IO.println $ (((iota.map (fun a => a + 10)).filter (fun v => v % 2 == 0)).approx n)
