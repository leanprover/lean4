/-! Coercions should ignore the RHS of `^` -/

set_option pp.coercions false
set_option pp.explicit true

/--
info: @HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow))
  (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3)))
  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) : Int
-/
#guard_msgs in
#check (3 : Int) ^ 2
-- 3 is Int
-- 2 is Nat

/--
info: @HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
  (@HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow))
    (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3)))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) : Int
-/
#guard_msgs in
#check (1 : Int) + 3 ^ 2
-- 1 is Int
-- 3 is Int
-- 2 is Nat

/--
info: @HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
  (@HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow))
    (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3)))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) : Int
-/
#guard_msgs in
#check (1 + 3 ^ 2 : Int)
-- 1 is Int
-- 3 is Int
-- 2 is Nat
