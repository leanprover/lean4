import Std.Tactic.BVDecide

/-!
Test for `bv_decide` in `sym =>` and `grind =>` mode.
-/

def optimized (x : BitVec 32) : BitVec 32 :=
  let x := x - ((x >>> 1) &&& 0x55555555);
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
  let x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
  let x := x + (x >>> 8);
  let x := x + (x >>> 16);
  x &&& 0x0000003F

example : optimized x = BitVec.cpop x := by
  sym =>
    simp [optimized.eq_def]
    bv_decide

example {x : BitVec 16} : x + 1 - 1 = x := by
  sym =>
    bv_normalize

namespace Alloc

opaque alloc : Nat → BitVec 64

axiom alloc_aligned (n : Nat) : alloc n &&& 0xfff#64 = 0#64

grind_pattern alloc_aligned => alloc n

example (n m : Nat) (x : BitVec 64) (h : m = n + 1) (hx : x = alloc m) :
    (x + alloc (n + 1)) &&& 0x1fff#64 = 0#64 := by
  grind =>
    instantiate [alloc_aligned]
    bv_decide

example (n m : Nat) (x : BitVec 64) (h : m = n + 1) (hx : x = alloc m) :
    (x + alloc (n + 1)) &&& 0x1fff#64 = 0#64 := by
  sym =>
    instantiate [alloc_aligned]
    bv_decide

example (n : Nat) (h1 : 0 < n) (h2 : n < 2) (h3 : x = alloc 1) :
    (x + alloc n) &&& 0x1fff#64 = 0#64 := by
  grind =>
    instantiate [alloc_aligned]
    bv_decide

end Alloc

namespace Enum

inductive Perm where
  | r | w | x
  deriving Inhabited

opaque perm : BitVec 64 → Perm

example (a b c d : BitVec 64)
    (h1 : perm a ≠ perm b) (h2 : perm a ≠ perm c) (h3 : perm a ≠ perm d)
    (h4 : perm b ≠ perm c) (h5 : perm b ≠ perm d) :
    perm c = perm d := by
  grind =>
    bv_decide

end Enum

namespace FixedInt

namespace U8

opaque g : UInt8 → UInt8

example (a b d : UInt8) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end U8

namespace U16

opaque g : UInt16 → UInt16

example (a b d : UInt16) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end U16

namespace U32

opaque g : UInt32 → UInt32

example (a b d : UInt32) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end U32

namespace U64

opaque g : UInt64 → UInt64

example (a b d : UInt64) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end U64

namespace USize

opaque g : USize → USize

example (a b d : USize) (h0 : d = a ||| b) (h : System.Platform.numBits = 64)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end USize

namespace I8

opaque g : Int8 → Int8

example (a b d : Int8) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end I8

namespace I16

opaque g : Int16 → Int16

example (a b d : Int16) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end I16

namespace I32

opaque g : Int32 → Int32

example (a b d : Int32) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end I32

namespace I64

opaque g : Int64 → Int64

example (a b d : Int64) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end I64

namespace ISize

opaque g : ISize → ISize

example (a b d : ISize) (h0 : d = a ||| b) (h : System.Platform.numBits = 64)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide

end ISize

end FixedInt

namespace Structure

structure Vec2 where
  x : BitVec 64
  y : BitVec 64
  inv : x &&& y = 0#64

opaque g : BitVec 64 → BitVec 64

example (a b d : BitVec 64) (p : Vec2) (h0 : d = a ||| b)
    (h1 : p.x = g d) (h2 : p.y = g (a ||| b)) :
    p.x = 0#64 := by
  grind =>
    bv_decide

end Structure
