/-! Dot ident notation should resolve mutual definitions -/

mutual

inductive Even
  | zero
  | succ (n : Odd)
  deriving Inhabited

inductive Odd
  | succ (n : Even)
  deriving Inhabited

end

mutual

def Even.ofNat : Nat → Even
  | 0 => .zero
  | n + 1 => .succ (.ofNat n)

def Odd.ofNat : Nat → Odd
  | 0 => panic! "invalid input"
  | n + 1 => .succ (.ofNat n)

end
