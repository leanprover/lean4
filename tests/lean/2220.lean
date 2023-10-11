/-! Coercions should ignore the RHS of `^` -/

set_option pp.coercions false
set_option pp.explicit true

#check (3 : Int) ^ 2
-- 3 is Int
-- 2 is Nat

#check (1 : Int) + 3 ^ 2
-- 1 is Int
-- 3 is Int
-- 2 is Nat

#check (1 + 3 ^ 2 : Int)
-- 1 is Int
-- 3 is Int
-- 2 is Nat

/-! With the binop behavior instead: -/

macro_rules | `($x ^ $y)   => `(binop% HPow.hPow $x $y)

#check (3 : Int) ^ 2  -- same
#check (1 : Int) + 3 ^ 2  -- breaks
#check (1 + 3 ^ 2 : Int)  -- breaks
