set_option cbv.warning false

def popcount : Nat → Nat
| 0 => 0
| 1 => 1
| n@(_+2) => if n % 2 = 0 then popcount (n / 2) else popcount (n / 2) + 1
termination_by n => n

/--
error: Tactic `decide` failed for proposition
  popcount 123498203491224398 = 32
because its `Decidable` instance
  instDecidableEqNat (popcount 123498203491224398) 32
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at
  (popcount 123498203491224398).beq 32
-/
#guard_msgs in
example : popcount 123498203491224398 = 32 := by decide

example : popcount 123498203491224398 = 32 := by conv => lhs; cbv

example : popcount 1234982034912243981 = 30 := by conv => lhs; cbv

example : popcount 1234982034912243981523 = 35 := by conv => lhs; cbv

example : popcount 12349820349122439815231238 = 42 := by conv => lhs; cbv

example : popcount 12349820349122439815231238098123 = 49 := by conv => lhs; cbv

example : popcount 1234982034912243981523123809812323 = 65 := by conv => lhs; cbv

example : popcount 1234982034912243981523123809812323982928213984812309234 = 101 := by conv => lhs; cbv

example : popcount 1234982034912243981523123809812323982928213984812309234213989 = 84 := by conv => lhs; cbv
