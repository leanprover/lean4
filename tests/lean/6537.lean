/-! Non-atomic pattern variables should give an error -/

example : Nat → Nat | x.y => x.y

def x.y := ()

example : Nat → Nat | x.y => x.y

attribute [match_pattern] x.y

example : Nat → Nat | x.y => x.y
