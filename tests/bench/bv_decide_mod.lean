import Std.Tactic.BVDecide

/-
Verify: https://en.wikipedia.org/wiki/Lehmer_random_number_generator#Sample_C99_code

uint32_t lcg_parkmiller(uint32_t *state)
{
	return *state = (uint64_t)*state * 48271 % 0x7fffffff;
}

vs

uint32_t lcg_parkmiller(uint32_t *state)
{
	uint64_t product = (uint64_t)*state * 48271;
	uint32_t x = (product & 0x7fffffff) + (product >> 31);

	x = (x & 0x7fffffff) + (x >> 31);
	return *state = x;
}
-/

def naive (state : BitVec 32) : BitVec 32 :=
  (((state.zeroExtend 64) * 48271) % 0x7fffffff).extractLsb 31 0

def opt (state : BitVec 32) : BitVec 32 :=
  let product := (state.zeroExtend 64) * 48271
  let x := ((product &&& 0x7fffffff) + (product >>> 31)).extractLsb 31 0
  let x := (x &&& 0x7fffffff) + (x >>> 31)
  x

--set_option trace.Meta.Tactic.bv true in
--set_option trace.Meta.Tactic.sat true in
--set_option trace.profiler true in
theorem lehmer_correct (state : BitVec 32) (h1 : state > 0) (h2 : state < 0x7fffffff) :
    naive state = opt state := by
  unfold naive opt
  bv_decide (config := { timeout := 120 })
