mutual
  inductive Even : Nat → Prop
    | base : Even 0
    | step : Odd n → Even (n+1)
  inductive Odd : Nat → Prop
    | step : Even n → Odd (n+1)
end
termination_by measure

mutual
 def f (n : Nat) :=
   if n == 0 then 0 else f (n / 2) + 1
 termination_by measure
end

mutual
  def f (n : Nat) :=
    match n with
    | 0 => 1
    | n+1 => f n * 2
end
termination_by measure


def g (n : Nat) :=
  match n with
  | 0 => 1
  | n+1 => g n * 3
termination_by measure
