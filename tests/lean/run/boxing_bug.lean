def myCast : NatCast UInt8 where
  natCast := UInt8.ofNat

class Semiring (α : Type u) where
  [nsmul : SMul Nat α]

/--
trace: [Compiler.IR] [result]
    def instSemiringUInt8._lam_0 (x_1 : @& tobj) (x_2 : u8) : u8 :=
      let x_3 : u8 := UInt8.ofNat x_1;
      let x_4 : u8 := UInt8.mul x_3 x_2;
      ret x_4
    def instSemiringUInt8._lam_0._boxed (x_1 : tobj) (x_2 : tagged) : tagged :=
      let x_3 : u8 := unbox x_2;
      let x_4 : u8 := instSemiringUInt8._lam_0 x_1 x_3;
      dec x_1;
      let x_5 : tagged := box x_4;
      ret x_5
[Compiler.IR] [result]
    def instSemiringUInt8._closed_0 : obj :=
      let x_1 : obj := pap instSemiringUInt8._lam_0._boxed;
      ret x_1
    def instSemiringUInt8 : obj :=
      let x_1 : obj := instSemiringUInt8._closed_0;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
attribute [local instance] myCast UInt8.intCast in
instance : Semiring UInt8 where
  nsmul := ⟨(· * ·)⟩

