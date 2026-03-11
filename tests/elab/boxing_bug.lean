@[implicit_reducible]
def myCast : NatCast UInt8 where
  natCast := UInt8.ofNat

class Semiring (α : Type u) where
  [nsmul : SMul Nat α]

/--
trace: [Compiler.IR] [result]
    def instSemiringUInt8 : obj :=
      let x_1 : obj := Lean.Grind.instCommRingUInt8;
      let x_2 : obj := proj[0] x_1;
      inc x_2;
      dec x_1;
      let x_3 : obj := Lean.Grind.Semiring.toNatModule._redArg x_2;
      let x_4 : tobj := proj[1] x_3;
      inc x_4;
      dec x_3;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
attribute [local instance] myCast UInt8.intCast in
instance : Semiring UInt8 where
  nsmul := ⟨(· * ·)⟩
