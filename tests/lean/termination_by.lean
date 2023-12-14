mutual
  inductive Even : Nat → Prop
    | base : Even 0
    | step : Odd n → Even (n+1)
  inductive Odd : Nat → Prop
    | step : Even n → Odd (n+1)
end
termination_by _ n => n -- Error

mutual
 def f (n : Nat) :=
   if n == 0 then 0 else f (n / 2) + 1
 termination_by _ => n -- Error
end

mutual
 def f (n : Nat) :=
   if n == 0 then 0 else f (n / 2) + 1
end
termination_by n => n -- Error


def g' (n : Nat) :=
  match n with
  | 0 => 1
  | n+1 => g' n * 3
termination_by
  h' n => n -- Error

def g' (n : Nat) :=
  match n with
  | 0 => 1
  | n+1 => g' n * 3
termination_by
  g' n => n
  _ n => n -- Error

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by
   isEven x => x -- Error

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by
   isEven x => x
   isOd x => x -- Error

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by
   isEven x => x
   isEven y => y -- Error

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by
   isEven x => x
   _ x => x
   _ x => x + 1 -- Error


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
termination_by
  f n => n -- Error
  g n => n

end Test
