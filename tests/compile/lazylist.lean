/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

universe u v w

inductive LazyList (α : Type u) where
  | nil                               : LazyList α
  | cons (hd : α) (tl : LazyList α)   : LazyList α
  | delayed (t : Thunk $ LazyList α)  : LazyList α

def List.toLazy {α : Type u} : List α → LazyList α
  | []     => LazyList.nil
  | h::t   => LazyList.cons h (toLazy t)

namespace LazyList
variable {α : Type u} {β : Type v} {δ : Type w}

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
  | nil          => default
  | cons a as    => a
  | delayed as   => head as.get

partial def tail : LazyList α → LazyList α
  | nil          => nil
  | cons a as    => as
  | delayed as   => tail as.get

partial def append : LazyList α → (Unit → LazyList α) → LazyList α
  | nil,          bs => bs ()
  | cons a as,    bs => delayed (cons a (append as bs))
  | delayed as,   bs => delayed (append as.get bs)

instance : Append (LazyList α) where
  append a b := LazyList.append a (fun _ => b)

partial def interleave : LazyList α → LazyList α → LazyList α
  | nil,          bs  => bs
  | cons a as,    bs  => delayed (cons a (interleave bs as))
  | delayed as,   bs  => delayed (interleave as.get bs)

partial def map (f : α → β) : LazyList α → LazyList β
  | nil          => nil
  | cons a as    => delayed (cons (f a) (map f as))
  | delayed as   => delayed (map f as.get)

partial def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
  | nil,          _            => nil
  | _,            nil          => nil
  | cons a as,    cons b bs    => delayed (cons (f a b) (map₂ f as bs))
  | delayed as,   bs           => delayed (map₂ f as.get bs)
  | as,           delayed bs   => delayed (map₂ f as bs.get)

@[inline] def zip : LazyList α → LazyList β → LazyList (α × β) :=
  map₂ Prod.mk

partial def join : LazyList (LazyList α) → LazyList α
  | nil          => nil
  | cons a as    => delayed (append a fun _ => join as)
  | delayed as   => delayed (join as.get)

@[inline] partial def bind (x : LazyList α) (f : α → LazyList β) : LazyList β :=
  join (x.map f)

instance isMonad : Monad LazyList where
  pure := LazyList.pure
  bind := LazyList.bind
  map  := LazyList.map

instance : Alternative LazyList where
  failure := nil
  orElse  := LazyList.append

partial def approx : Nat → LazyList α → List α
  | 0,     as           => []
  | _,     nil          => []
  | i+1,   cons a as    => a :: approx i as
  | i+1,   delayed as   => approx (i+1) as.get

partial def iterate (f : α → α) : α → LazyList α
  | x => cons x (delayed (iterate f (f x)))

partial def iterate₂ (f : α → α → α) : α → α → LazyList α
  | x, y => cons x (delayed (iterate₂ f y (f x y)))

partial def filter (p : α → Bool) : LazyList α → LazyList α
  | nil          => nil
  | cons a as    => delayed (if p a then cons a (filter p as) else filter p as)
  | delayed as   => delayed (filter p as.get)

end LazyList

def fib : LazyList Nat :=
  LazyList.iterate₂ (· + ·) 0 1

def iota (i : Nat := 0) : LazyList Nat :=
  LazyList.iterate Nat.succ i

def tst : LazyList String := do
  let x ← [1, 2, 3].toLazy
  let y ← [2, 3, 4].toLazy
  guard (x + y > 5)
  pure s!"{x} + {y} = {x+y}"

def main : IO Unit := do
  let n := 40
  IO.println tst.isEmpty
  IO.println tst.head
  IO.println <| fib.interleave (iota.map (· + 100)) |>.approx n
  IO.println <| iota.map (· + 10) |>.filter (· % 2 == 0) |>.approx n
