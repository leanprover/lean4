set_option trace.Compiler.result true in
def mulDivShift (a : Nat) (b : UInt8) (c : UInt16) (d : UInt32) (e : UInt64) : Nat :=
  let a1 := a / 32
  let a2 := a * 32
  let b1 := b / 32
  let b2 := b * 32
  let c1 := c / 32
  let c2 := c * 32
  let d1 := d / 32
  let d2 := d * 32
  let e1 := e / 32
  let e2 := e * 32
  a1 + a2 + b1.val.val + b2.val.val + c1.val.val + c2.val.val + d1.val.val + d2.val.val + e1.val.val + e2.val.val
