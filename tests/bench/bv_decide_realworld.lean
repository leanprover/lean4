import Std.Tactic.BVDecide

-- two hard problems from: https://github.com/leanprover/LNSym/pull/85
notation:50 x " >>>ᵤ " y => BitVec.ushiftRight x y

def popcount32_spec_rec (i : Nat) (x : BitVec 32) : (BitVec 32) :=
  match i with
  | 0 => 0#32
  | i' + 1 =>
    let bit_idx := BitVec.extractLsb i' i' x
    let bv_idx := (BitVec.zeroExtend 32 bit_idx)
    (bv_idx + (popcount32_spec_rec i' x))

def popcount32_spec (x : BitVec 32) : BitVec 32 :=
  popcount32_spec_rec 32 x

def popcount32_impl (x : BitVec 32) : BitVec 32 :=
  let x' := x - ((x >>>ᵤ 1) &&& 0x55555555#32)
  let x'' := (x' &&& 0x33333333#32) + ((x' >>>ᵤ 2) &&& 0x33333333#32)
  ((x'' + (x'' >>>ᵤ 4) &&& 0x0f0f0f0f#32) * 0x01010101#32) >>>ᵤ 24

theorem popcount32_correct (x : BitVec 32) :
  (popcount32_spec x) = (popcount32_impl x) := by
  dsimp only [popcount32_spec_rec, popcount32_spec, popcount32_impl]
  bv_decide

def parity32_spec_rec (i : Nat) (x : BitVec 32) : Bool :=
  match i with
  | 0 => false
  | i' + 1 =>
    let bit_idx := BitVec.getLsbD x i'
    bit_idx ^^ (parity32_spec_rec i' x)

def parity32_spec (x : BitVec 32) : Bool :=
  parity32_spec_rec 32 x

def parity32_impl (x : BitVec 32) : BitVec 32 :=
  let x1 := x ^^^ (x >>> 16)
  let x2 := x1 ^^^ (x1 >>> 8)
  let x3 := x2 ^^^ (x2 >>> 4)
  let x4 := x3 &&& 0x0000000f#32
  (0x00006996#32 >>> x4) &&& 1#32

theorem parity32_correct (x : BitVec 32) :
    (parity32_spec x) = ((parity32_impl x).getLsbD 0) := by
  dsimp only [parity32_spec, parity32_impl, parity32_spec_rec]
  bv_decide
