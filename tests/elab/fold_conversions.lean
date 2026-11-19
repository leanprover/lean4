/-!
This test checks that the LCNF constant folder evaluates literal applications of the conversions
between the fixed-width unsigned integer types.
-/

/--
trace: [Compiler.saveBase] size: 1
    def u8ToU16 : UInt16 :=
      let _x.1 := 200;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ToU16 : UInt16 := (200 : UInt8).toUInt16

/--
trace: [Compiler.saveBase] size: 1
    def u8ToU32 : UInt32 :=
      let _x.1 := 200;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ToU32 : UInt32 := (200 : UInt8).toUInt32

/--
trace: [Compiler.saveBase] size: 1
    def u8ToU64 : UInt64 :=
      let _x.1 := 200;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ToU64 : UInt64 := (200 : UInt8).toUInt64

/--
trace: [Compiler.saveBase] size: 1
    def u8ToUSize : USize :=
      let _x.1 := 200;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ToUSize : USize := (200 : UInt8).toUSize

/--
trace: [Compiler.saveBase] size: 1
    def u16ToU8 : UInt8 :=
      let _x.1 := 44;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ToU8 : UInt8 := (300 : UInt16).toUInt8

/--
trace: [Compiler.saveBase] size: 1
    def u16ToU32 : UInt32 :=
      let _x.1 := 300;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ToU32 : UInt32 := (300 : UInt16).toUInt32

/--
trace: [Compiler.saveBase] size: 1
    def u16ToU64 : UInt64 :=
      let _x.1 := 300;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ToU64 : UInt64 := (300 : UInt16).toUInt64

/--
trace: [Compiler.saveBase] size: 1
    def u16ToUSize : USize :=
      let _x.1 := 300;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ToUSize : USize := (300 : UInt16).toUSize

/--
trace: [Compiler.saveBase] size: 1
    def u32ToU8 : UInt8 :=
      let _x.1 := 44;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ToU8 : UInt8 := (300 : UInt32).toUInt8

/--
trace: [Compiler.saveBase] size: 1
    def u32ToU16 : UInt16 :=
      let _x.1 := 4464;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ToU16 : UInt16 := (70000 : UInt32).toUInt16

/--
trace: [Compiler.saveBase] size: 1
    def u32ToU64 : UInt64 :=
      let _x.1 := 70000;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ToU64 : UInt64 := (70000 : UInt32).toUInt64

/--
trace: [Compiler.saveBase] size: 1
    def u32ToUSize : USize :=
      let _x.1 := 70000;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ToUSize : USize := (70000 : UInt32).toUSize

/--
trace: [Compiler.saveBase] size: 1
    def u64ToU8 : UInt8 :=
      let _x.1 := 44;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ToU8 : UInt8 := (300 : UInt64).toUInt8

/--
trace: [Compiler.saveBase] size: 1
    def u64ToU16 : UInt16 :=
      let _x.1 := 4464;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ToU16 : UInt16 := (70000 : UInt64).toUInt16

/--
trace: [Compiler.saveBase] size: 1
    def u64ToU32 : UInt32 :=
      let _x.1 := 705032704;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ToU32 : UInt32 := (5000000000 : UInt64).toUInt32

/--
trace: [Compiler.saveBase] size: 1
    def u64ToUSize : USize :=
      let _x.1 := 300;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ToUSize : USize := (300 : UInt64).toUSize

/--
trace: [Compiler.saveBase] size: 1
    def u64ToUSizeLarge : USize :=
      let _x.1 := 5000000000;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ToUSizeLarge : USize := (5000000000 : UInt64).toUSize

/--
trace: [Compiler.saveBase] size: 1
    def usizeToU8 : UInt8 :=
      let _x.1 := 44;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeToU8 : UInt8 := (300 : USize).toUInt8

/--
trace: [Compiler.saveBase] size: 1
    def usizeToU16 : UInt16 :=
      let _x.1 := 4464;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeToU16 : UInt16 := (70000 : USize).toUInt16

/--
trace: [Compiler.saveBase] size: 1
    def usizeToU32 : UInt32 :=
      let _x.1 := 70000;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeToU32 : UInt32 := (70000 : USize).toUInt32

/--
trace: [Compiler.saveBase] size: 1
    def usizeToU64 : UInt64 :=
      let _x.1 := 70000;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeToU64 : UInt64 := (70000 : USize).toUInt64

/--
trace: [Compiler.saveBase] size: 1
    def u8Clamp : UInt8 :=
      let _x.1 := 255;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8Clamp : UInt8 := UInt8.ofNatClamp 300

/--
trace: [Compiler.saveBase] size: 1
    def u8ClampSmall : UInt8 :=
      let _x.1 := 100;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ClampSmall : UInt8 := UInt8.ofNatClamp 100

/--
trace: [Compiler.saveBase] size: 1
    def u16Clamp : UInt16 :=
      let _x.1 := 65535;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16Clamp : UInt16 := UInt16.ofNatClamp 70000

/--
trace: [Compiler.saveBase] size: 1
    def u32Clamp : UInt32 :=
      let _x.1 := 4294967295;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32Clamp : UInt32 := UInt32.ofNatClamp 5000000000

/--
trace: [Compiler.saveBase] size: 1
    def u64Clamp : UInt64 :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64Clamp : UInt64 := UInt64.ofNatClamp 100000000000000000000

/--
trace: [Compiler.saveBase] size: 1
    def usizeClamp : USize :=
      let _x.1 := 100;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeClamp : USize := USize.ofNatClamp 100

/--
trace: [Compiler.saveBase] size: 2
    def usizeClampLarge : USize :=
      let _x.1 := 5000000000;
      let _x.2 := USize.ofNatClamp _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeClampLarge : USize := USize.ofNatClamp 5000000000

/--
trace: [Compiler.saveBase] size: 1
    def boolToNatTrue : Nat :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToNatTrue : Nat := true.toNat

/--
trace: [Compiler.saveBase] size: 1
    def boolToNatFalse : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToNatFalse : Nat := false.toNat

/--
trace: [Compiler.saveBase] size: 1
    def boolToU8True : UInt8 :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU8True : UInt8 := true.toUInt8

/--
trace: [Compiler.saveBase] size: 1
    def boolToU8False : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU8False : UInt8 := false.toUInt8

/--
trace: [Compiler.saveBase] size: 1
    def boolToU16True : UInt16 :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU16True : UInt16 := true.toUInt16

/--
trace: [Compiler.saveBase] size: 1
    def boolToU16False : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU16False : UInt16 := false.toUInt16

/--
trace: [Compiler.saveBase] size: 1
    def boolToU32True : UInt32 :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU32True : UInt32 := true.toUInt32

/--
trace: [Compiler.saveBase] size: 1
    def boolToU32False : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU32False : UInt32 := false.toUInt32

/--
trace: [Compiler.saveBase] size: 1
    def boolToU64True : UInt64 :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU64True : UInt64 := true.toUInt64

/--
trace: [Compiler.saveBase] size: 1
    def boolToU64False : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToU64False : UInt64 := false.toUInt64

/--
trace: [Compiler.saveBase] size: 1
    def boolToUSizeTrue : USize :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToUSizeTrue : USize := true.toUSize

/--
trace: [Compiler.saveBase] size: 1
    def boolToUSizeFalse : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def boolToUSizeFalse : USize := false.toUSize

/--
trace: [Compiler.saveBase] size: 5
    def noFold x b n : UInt8 × Nat × UInt16 :=
      let _x.1 := UInt64.toUInt8 x;
      let _x.2 := Bool.toNat b;
      let _x.3 := UInt16.ofNatClamp n;
      let _x.4 := @Prod.mk _ _ _x.2 _x.3;
      let _x.5 := @Prod.mk _ _ _x.1 _x.4;
      return _x.5
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def noFold (x : UInt64) (b : Bool) (n : Nat) : UInt8 × Nat × UInt16 :=
  (x.toUInt8, b.toNat, UInt16.ofNatClamp n)
