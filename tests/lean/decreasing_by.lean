mutual
  inductive Even : Nat → Prop
    | base : Even 0
    | step : Odd n → Even (n+1)
  inductive Odd : Nat → Prop
    | step : Even n → Odd (n+1)
end
decreasing_by assumption

mutual
 def f (n : Nat) :=
   if n == 0 then 0 else f (n / 2) + 1
 decreasing_by assumption
end

def g' (n : Nat) :=
  match n with
  | 0 => 1
  | n+1 => g' n * 3
decreasing_by
  h => assumption

namespace Test
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n+1, a, b => g n a b |>.1

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)

  def h : Nat → α → α → α
    | 0, a, b => b
    | n+1, a, b => f n a b
end
decreasing_by
  f => assumption
  g => assumption

end Test
