import Std.Tactic.BVDecide

/-
This is based on: https://saw.galois.com/intro/IntroToSAW.html#the-code
-/

namespace Popcount

/-
int pop_spec(uint32_t x) {
    uint32_t pop = 0;
    uint32_t mask = 1;
    for (int i = 0; i < 32; i++) {
        if (x & mask) { pop++; }
        mask = mask << 1;
    }
    return pop;
}
-/

def pop_spec (x : BitVec 32) : BitVec 32 := Id.run do
  let mut pop : BitVec 32 := 0
  let mut mask : BitVec 32 := 1
  for _ in [0:32] do
    if (x &&& mask != 0) then
      pop := pop + 1
    mask := mask <<< 1
  return pop

/-
We do currently not have nice support for if statements in the bit blaster and arguing about
monadic for loops is not nicely done as well, instead we will use a recursive version:
-/

def pop_spec' (x : BitVec 32) : BitVec 32 :=
  go x 0 32
where
  go (x : BitVec 32) (pop : BitVec 32) (i : Nat) : BitVec 32 :=
    match i with
    | 0 => pop
    | i + 1 =>
      let pop := pop + (x &&& 1)
      go (x >>> 1) pop i

def optimized (x : BitVec 32) : BitVec 32 :=
    let x := x - ((x >>> 1) &&& 0x55555555);
    let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
    let x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
    let x := x + (x >>> 8);
    let x := x + (x >>> 16);
    x &&& 0x0000003F

example (x : BitVec 32) : pop_spec' x = optimized x := by
  dsimp [pop_spec', pop_spec'.go, optimized]
  bv_decide

end Popcount
