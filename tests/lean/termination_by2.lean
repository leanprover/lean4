mutual
 def f (n : Nat) :=
   if n == 0 then 0 else f (n / 2) + 1
 termination_by _ => n
end

def g' (n : Nat) :=
  match n with
  | 0 => 1
  | n+1 => g' n * 3
termination_by
  g' n => n
  _ n => n

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
