/-!
This module tests various mis-uses of termination_by and decreasing_by:
* use in non-recursive functions
* that all or none of a recursive group have termination_by.
-/

def nonRecursive1 (n : Nat) : Nat := n
  termination_by n -- Error

def nonRecursive2 (n : Nat) : Nat := n
  decreasing_by sorry -- Error

def nonRecursive3 (n : Nat) : Nat := n
  termination_by n -- Error
  decreasing_by sorry

partial def partial1 (n : Nat) : Nat := partial1 n
  termination_by n -- Error

partial def partial2 (n : Nat) : Nat := partial2 n
  decreasing_by sorry -- Error

partial def partial3 (n : Nat) : Nat := partial3 n
  termination_by n -- Error
  decreasing_by sorry

unsafe def unsafe1 (n : Nat) : Nat := unsafe1 n
termination_by n -- Error

unsafe def unsafe2 (n : Nat) : Nat := unsafe2 n
  decreasing_by sorry -- Error

unsafe def unsafe3 (n : Nat) : Nat := unsafe3 n
  termination_by x -- Error
  decreasing_by sorry

unsafe def withWhere (n : Nat) : Nat := foo n
  where foo (n : Nat) := n
    termination_by n -- Error

unsafe def withLetRec (n : Nat) : Nat :=
  let rec foo (n : Nat) := n
    termination_by n -- Error
  foo n

mutual
  def rec : Nat → Nat
    | 0 => 0
    | n+1 => rec n + notrec n
  termination_by x => x

  def notrec (n : Nat) : Nat := n
  termination_by n -- Error
end


mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  termination_by x => x

  def isOdd : Nat → Bool -- Error
    | 0 => false
    | n+1 => isEven n
end

namespace Test
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n+1, a, b => g n a b |>.1
  termination_by n _ _ => n

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)
  termination_by n _ _ => n

  def h : Nat → α → α → α -- Error
    | 0, a, b => b
    | n+1, a, b => f n a b
end

end Test
