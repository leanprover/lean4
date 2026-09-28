module
/-!
This test checks that the LCNF constant folder evaluates `UIntN.complement` (`~~~`) applied to a
literal for `UInt8`, `UInt16`, `UInt32` and `UInt64`.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def u8 : UInt8 :=
      let _x.1 := 255;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8 : UInt8 := ~~~(0 : UInt8)

/--
trace: [Compiler.saveBase] size: 1
    def u8' : UInt8 :=
      let _x.1 := 250;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8' : UInt8 := ~~~(5 : UInt8)

/--
trace: [Compiler.saveBase] size: 1
    def u16 : UInt16 :=
      let _x.1 := 65535;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16 : UInt16 := ~~~(0 : UInt16)

/--
trace: [Compiler.saveBase] size: 1
    def u16' : UInt16 :=
      let _x.1 := 65235;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16' : UInt16 := ~~~(300 : UInt16)

/--
trace: [Compiler.saveBase] size: 1
    def u32 : UInt32 :=
      let _x.1 := 4294967295;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32 : UInt32 := ~~~(0 : UInt32)

/--
trace: [Compiler.saveBase] size: 1
    def u32' : UInt32 :=
      let _x.1 := 4294967290;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32' : UInt32 := ~~~(5 : UInt32)

/--
trace: [Compiler.saveBase] size: 1
    def u64 : UInt64 :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64 : UInt64 := ~~~(0 : UInt64)

/--
trace: [Compiler.saveBase] size: 1
    def u64' : UInt64 :=
      let _x.1 := 18446744073709551610;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64' : UInt64 := ~~~(5 : UInt64)

/--
trace: [Compiler.saveBase] size: 1
    def dbl : UInt8 :=
      let _x.1 := 5;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def dbl : UInt8 := ~~~(~~~(5 : UInt8))

/--
trace: [Compiler.saveBase] size: 2
    def usize : USize :=
      let _x.1 := 0;
      let _x.2 := USize.complement _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usize : USize := ~~~(0 : USize)

/--
trace: [Compiler.saveBase] size: 1
    def var8 x : UInt8 :=
      let _x.1 := UInt8.complement x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def var8 (x : UInt8) : UInt8 := ~~~x

/--
trace: [Compiler.saveBase] size: 1
    def var64 x : UInt64 :=
      let _x.1 := UInt64.complement x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def var64 (x : UInt64) : UInt64 := ~~~x
