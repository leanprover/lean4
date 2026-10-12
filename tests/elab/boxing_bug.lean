@[instance_reducible]
def myCast : NatCast UInt8 where
  natCast := UInt8.ofNat

class Semiring (α : Type u) where
  [nsmul : SMul Nat α]

/--
trace: [Compiler.result] size: 2
    def instSemiringUInt8._lam_0 (x1.1 : @&tobj) (x2.2 : UInt8) : UInt8 :=
      let _x.3 : UInt8 := UInt8.ofNat x1.1;
      let _x.4 : UInt8 := UInt8.mul _x.3 x2.2;
      return _x.4
[Compiler.result] size: 4
    def instSemiringUInt8._lam_0._boxed (x1.1 : tobj) (x2.2 : tagged) : tagged :=
      let x2.27.boxed : UInt8 := unbox x2.2;
      let res : UInt8 := instSemiringUInt8._lam_0 x1.1 x2.27.boxed;
      dec x1.1;
      let r : tagged := box res;
      return r
[Compiler.result] size: 1
    def instSemiringUInt8._closed_0 : obj :=
      let _f.1 : obj := pap instSemiringUInt8._lam_0._boxed;
      return _f.1
[Compiler.result] size: 2
    def instSemiringUInt8 : obj :=
      let _f.1 : obj := instSemiringUInt8._closed_0;
      inc[persistent][ref] _f.1;
      return _f.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
attribute [local instance] myCast UInt8.intCast in
instance : Semiring UInt8 where
  nsmul := ⟨(· * ·)⟩
