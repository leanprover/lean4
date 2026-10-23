module
import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
import Init.Data.UInt.BitCounts
import Init.Data.SInt.BitCounts

/-! Bitblasting the word zero-count APIs, including both platform widths and signed wrappers. -/

example (x : UInt8) : x.ctz ≤ 8 := by bv_decide
example (x : UInt16) : x.clz ≤ 16 := by bv_decide
example (x : UInt32) : x.ctz = 32 ↔ x = 0 := by bv_decide
example (x : UInt64) : x.clz = 64 ↔ x = 0 := by bv_decide
example (x : Int8) (h : x < 0) : x.clz = 0 := by bv_decide
example (x : Int16) : x.ctz = 16 ↔ x = 0 := by bv_decide
example (x : Int32) (h : x < 0) : x.clz = 0 := by bv_decide
example (x : Int64) : x.ctz = 64 ↔ x = 0 := by bv_decide
example (h : System.Platform.numBits = 32) (x : USize) : x.ctz ≤ 32 := by bv_decide
example (h : System.Platform.numBits = 64) (x : USize) : x.clz ≤ 64 := by bv_decide
example (h : System.Platform.numBits = 32) (x : ISize) (hx : x < 0) : x.clz = 0 := by bv_decide
example (h : System.Platform.numBits = 64) (x : ISize) : x.ctz = 64 ↔ x = 0 := by bv_decide
