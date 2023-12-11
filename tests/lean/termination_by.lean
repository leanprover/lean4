/-!
This module tests various mis-uses of termination_by,
in particular that all or none of a recursive group have it.
-/

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
  termination_by n => n

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)
  termination_by n => n

  def h : Nat → α → α → α -- Error
    | 0, a, b => b
    | n+1, a, b => f n a b
end

end Test
