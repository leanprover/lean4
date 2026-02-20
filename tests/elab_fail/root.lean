namespace Foo

def y := 10

def _root_.Bla.f (x : Nat) := x + y

#check Bla.f

example : Bla.f 5 = 15 := rfl

def _root_.g (x : Nat) :=
  match x with
  | 0 => 1
  | x+1 => 2*g x

def _root_.Boo.g (x : Nat) :=
  match x with
  | 0 => 1
  | x+1 => 3 * Boo.g x

protected def _root_.h (x : Nat) := x -- Error

example : g 3 = 8 := rfl

example : Boo.g 2 = 9 := rfl

end Foo

def _root_ (y : Nat) := y + 1 -- Error

def _root_._root_ (y : Nat) := y -- Error

def _root_.f._root_ (y : Nat) := y -- Error

protected def _root_.h (x : Nat) := x -- Error

protected def _root_.Boo.h (x : Nat) := x

example : Boo.h x = x := rfl

#check h -- Error

#check f -- Error

open Bla

#check f -- Ok

namespace Test

mutual

  def _root_.isEven (x : Nat) :=
    match x with
    | 0 => true
    | x+1 => isOdd x

  def _root_.isOdd (x : Nat) :=
    match x with
    | 0 => false
    | x+1 => isEven x

end

private def _root_.prv (x : Nat) := x + x + x

example : prv 5 = 15 := rfl

end Test

example : isEven 0  = true := by simp! [isOdd, isEven]
example : isOdd 1   = true := by simp! [isOdd, isEven]
example : isEven 2  = true := by simp! [isOdd, isEven]

example : prv 5 = 15 := rfl

set_option pp.raw true in
#check prv

namespace Ex

@[scoped simp] theorem _root_.isEven_of_isOdd (x : Nat) : isEven (x+1) = isOdd x := by simp [isEven]

@[scoped simp] theorem _root_.isOdd_of_isEven (x : Nat) : isOdd (x+1) = isEven x := by simp [isOdd]

example : isEven (x+1+1) = isEven x := by simp -- Ok

end Ex

example : isEven (x+1+1) = isEven x := by simp (config := { failIfUnchanged := false }); done -- Error

open Ex in
example : isEven (x+1+1) = isEven x := by simp -- Ok

example : isEven (x+1+1) = isEven x := by simp (config := { failIfUnchanged := false }); done -- Error

namespace Foo

def _root_.Bla.g (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | .succ x => h x + g x
where
  h (x : Nat) :=
    match x with
    | 0 => 2
    | .succ x => 2 * g x


def _root_.Bla.g' (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | .succ x => g' x

end Foo
