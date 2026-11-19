module

/-!
Tests for `grind` evaluation of structural `BitVec` operations on literals, including modulo
equalities: given `x = 42#64`, `grind` propagates values for `extractLsb'`, `setWidth`,
bitwise operations, shifts, bit accessors, `toNat`, etc. applied to `x`. Arithmetic operations
and comparisons are covered by `cutsat` and are included here as regression tests.
-/

/-! Henrik's examples (Zulip): ground and modulo-equality extract operations. -/

example : BitVec.extractLsb 63 32 42#64 = 0#32 := by grind
example : BitVec.extractLsb' 63 32 42#64 = 0#32 := by grind
example {x : BitVec 64} (h : x = 42#64) : BitVec.extractLsb 63 32 x = 0#32 := by grind
example {x : BitVec 64} (h : x = 42#64) : BitVec.extractLsb' 63 32 x = 0#32 := by grind
example : BitVec.extractLsb 63 32 (0#64 + 42#64) = 0#32 := by grind
example : BitVec.extractLsb' 63 32 (0#64 + 42#64) = 0#32 := by grind
example {x : BitVec 64} (h : x = 0#64 + 42#64) : BitVec.extractLsb 63 32 x = 0#32 := by grind
example {x : BitVec 64} (h : x = 0#64 + 42#64) : BitVec.extractLsb' 63 32 x = 0#32 := by grind


/-! Arithmetic and comparisons: handled by `cutsat`, not the propagators. -/

example {x : BitVec 64} (h : x = 42#64) : x + 1#64 = 43#64 := by grind
example {x : BitVec 64} (h : x = 42#64) : 2#64 * x = 84#64 := by grind
example {x : BitVec 64} (h : x = 42#64) : x < 43#64 := by grind
example {x : BitVec 64} (h : x = 42#64) : x ≤ 42#64 := by grind

/-! Conversions. -/

example {x : BitVec 64} (h : x = 42#64) : x.toNat = 42 := by grind
example {x : BitVec 8} (h : x = 255#8) : x.toInt = -1 := by grind
example {n : Nat} (h : n = 300) : BitVec.ofNat 8 n = 44#8 := by grind
example {i : Int} (h : i = -1) : BitVec.ofInt 8 i = 255#8 := by grind

/-! Bitwise operations. -/

example {x : BitVec 64} (h : x = 42#64) : x &&& 15#64 = 10#64 := by grind
example {x : BitVec 64} (h : x = 42#64) : x ||| 1#64 = 43#64 := by grind
example {x : BitVec 64} (h : x = 42#64) : x ^^^ 42#64 = 0#64 := by grind
example {x : BitVec 8} (h : x = 0#8) : ~~~x = 255#8 := by grind
example {x y : BitVec 64} (h₁ : x = 42#64) (h₂ : y = 15#64) : x &&& y = 10#64 := by grind

/-! Shifts and rotations. -/

example {x : BitVec 64} (h : x = 42#64) : x >>> 1 = 21#64 := by grind
example {x : BitVec 64} (h : x = 42#64) : x <<< 1 = 84#64 := by grind
example {x : BitVec 64} (h : x = 42#64) : x >>> 1#64 = 21#64 := by grind
example {x : BitVec 64} (h : x = 42#64) (i : Nat) (h' : i = 1) : x <<< i = 84#64 := by grind
example {x : BitVec 8} (h : x = 129#8) : x.rotateLeft 1 = 3#8 := by grind
example {x : BitVec 8} (h : x = 3#8) : x.rotateRight 1 = 129#8 := by grind

/-! Bit accessors. -/

example {x : BitVec 64} (h : x = 42#64) : x.getLsbD 1 = true := by grind
example {x : BitVec 64} (h : x = 42#64) : x.getLsbD 0 = false := by grind
example {x : BitVec 64} (h : x = 42#64) : x.getMsbD 0 = false := by grind
example {x : BitVec 64} (h : x = 42#64) (h' : 1 < 64) : x[1] = true := by grind
example {x : BitVec 8} (h : x = 255#8) : x.msb = true := by grind

/-! Width changing operations. -/

example {x : BitVec 64} (h : x = 42#64) : x.setWidth 32 = 42#32 := by grind
example {x : BitVec 64} (h : x = 42#64) : BitVec.signExtend 128 x = 42#128 := by grind
example {x : BitVec 8} (h : x = 255#8) : BitVec.signExtend 16 x = 65535#16 := by grind

/-! Append and replicate. -/

example {x : BitVec 64} (h : x = 42#64) : x ++ x = 0x000000000000002a000000000000002a#128 := by grind
example {x : BitVec 8} (h : x = 1#8) : BitVec.replicate 2 x = 257#16 := by grind

/-! Misc unary operations. -/

example {x : BitVec 8} (h : x = 1#8) : x.clz = 7#8 := by grind
example {x : BitVec 8} (h : x = 255#8) : x.cpop = 8#8 := by grind

/-! Chained: the propagated value feeds further propagation. -/

example {x : BitVec 64} {y : BitVec 32} (h₁ : x = 42#64) (h₂ : y = BitVec.extractLsb' 0 32 x) :
    y &&& 2#32 = 2#32 := by grind

/-! The index/argument being only *equal* to a literal. -/

example {x : BitVec 64} (h : x = 42#64) (i : Nat) (hi : i = 1) : x.getLsbD i = true := by grind

/-!
Regression test: the `ofNat` propagator merges `BitVec.ofNat`-spelled literals (e.g. the
`Std.LawfulIdentity` neutral elements internalized by the AC module) with canonical `OfNat`
literals. This used to trigger a kernel error because the AC module internalized the neutral
element of `|||` in a non-canonical form, violating the invariant that interpreted nodes
are canonical.
-/

example (x y : BitVec 64) : (x ||| y) &&& x = x := by grind
