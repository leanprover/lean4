import Std.Tactic.BVDecide

/-
This file is based on: https://grack.com/blog/2022/12/20/deriving-a-bit-twiddling-hack/
-/

open BitVec

namespace DerivingBitTwiddlingHack


/-
bool will_add_overflow_64bit(int32_t a, int32_t b) {
    // a and b are promoted to 64-bit signed integers
    int64_t result = (int64_t)a + b;
    if (result < INT32_MIN || result > INT32_MAX) {
        return true;
    }
    return false;
}
-/

def will_add_overflow_64bit (a b : BitVec 32) : Bool :=
  let a := a.signExtend 64
  let b := b.signExtend 64
  let result := a + b
  -- copied from libc
  let INT32_MAX := 0x7fffffff#32
  let INT32_MIN := (-0x7fffffff#32 - 1#32)
  BitVec.slt result (INT32_MIN.signExtend 64) || BitVec.slt (INT32_MAX.signExtend 64) result

/-
bool will_add_overflow_expression(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    #define NEG(x) (((uint32_t)(x) & 0x80000000) == 0x80000000)
    return ((!NEG(a) && !NEG(b) && NEG(c))
        || (NEG(a) && NEG(b) && !NEG(c)));
    #undef NEG
}
-/

def will_add_overflow_expression (a b : BitVec 32) : Bool :=
  let c := a + b
  let NEG (x : BitVec 32) : Bool :=
    (x &&& 0x80000000#32) == 0x80000000#32
  (!NEG a && !NEG b && NEG c) || (NEG a && NEG b && !NEG c)

example (a b : BitVec 32) : will_add_overflow_64bit a b = will_add_overflow_expression a b := by
  dsimp [will_add_overflow_64bit, will_add_overflow_expression]
  intros; bv_decide

/-
bool will_add_overflow_bitwise_2(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    #define NEG(x) (((uint32_t)(x) & 0x80000000) == 0x80000000)
    return NEG((~a & ~b & c) | (a & b & ~c));
    #undef NEG
}
-/
def will_add_overflow_bitwise_2 (a b : BitVec 32) : Bool :=
  let c := a + b
  let NEG (x : BitVec 32) : Bool :=
    ((x &&& 0x80000000#32) == 0x80000000#32)
  NEG ((~~~a &&& ~~~b &&& c) ||| (a &&& b &&& ~~~c))

example (a b : BitVec 32) : will_add_overflow_expression a b = will_add_overflow_bitwise_2 a b := by
  dsimp [will_add_overflow_expression, will_add_overflow_bitwise_2]
  intros; bv_decide

/-
bool will_add_overflow_bitwise_3(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    return ((~a & ~b & c) | (a & b & ~c)) >> 31;
}
-/
def will_add_overflow_bitwise_3 (a b : BitVec 32) : Bool :=
  let c := a + b
  getLsbD (((~~~a &&& ~~~b &&& c) ||| (a &&& b &&& ~~~c)) >>> 31) 0

example (a b : BitVec 32) : will_add_overflow_bitwise_2 a b = will_add_overflow_bitwise_3 a b := by
  dsimp [will_add_overflow_bitwise_2, will_add_overflow_bitwise_3]
  intros; bv_decide

/-
bool will_add_overflow_optimized_a(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    return (~(a ^ b) & (c ^ a)) >> 31;
}
-/
def will_add_overflow_optimized_a (a b : BitVec 32) : Bool :=
  let c := a + b
  getLsbD ((~~~(a ^^^ b) &&& (c ^^^ a)) >>> 31) 0

example (a b : BitVec 32) :
    will_add_overflow_bitwise_3 a b = will_add_overflow_optimized_a a b := by
  dsimp [will_add_overflow_bitwise_3, will_add_overflow_optimized_a]
  intros; bv_decide

/-
bool will_add_overflow_optimized_b(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    return ((c ^ a) & (c ^ b)) >> 31;
}
-/
def will_add_overflow_optimized_b (a b : BitVec 32) : Bool :=
  let c := a + b
  getLsbD (((c ^^^ a) &&& (c ^^^ b)) >>> 31) 0

example (a b : BitVec 32) :
    will_add_overflow_optimized_a a b = will_add_overflow_optimized_b a b := by
  dsimp [will_add_overflow_optimized_a, will_add_overflow_optimized_b]
  intros; bv_decide


end DerivingBitTwiddlingHack
