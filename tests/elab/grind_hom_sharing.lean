/-!
Tests that the `[grind hom]` engine handles repeated doubling of a widened fixed-width integer
without blowing up, ported from the intblasting prototype test suite (#15224). Each `let`
doubles the previous value, so the unsigned interpretation must be shared across the chain.
-/

example (x0 : UInt8) :
    let x := x0.toUInt16
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

example (x0 : UInt16) :
    let x := x0.toUInt32
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

example (x0 : UInt32) :
    let x := x0.toUInt64
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

-- TODO: `grind` fails (`USize`); 16 doublings also time out
/-
example (x0 : UInt16) :
    let x := x0.toUSize
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 := by
  grind
-/
