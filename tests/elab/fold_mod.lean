module
/-!
This test checks that the LCNF constant folder handles `Nat.mod` and its `UInt8`/`UInt16`/
`UInt32`/`UInt64`/`USize` counterparts.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def natLit : Nat :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natLit : Nat := 17 % 5

/--
trace: [Compiler.saveBase] size: 0
    def natModZero x : Nat :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natModZero (x : Nat) : Nat := x % 0

/--
trace: [Compiler.saveBase] size: 1
    def natZeroMod x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natZeroMod (x : Nat) : Nat := 0 % x

/--
trace: [Compiler.saveBase] size: 1
    def natModOne x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natModOne (x : Nat) : Nat := x % 1

/--
trace: [Compiler.saveBase] size: 2
    def natNoFold x : Nat :=
      let _x.1 := 3;
      let _x.2 := Nat.mod x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natNoFold (x : Nat) : Nat := x % 3

/--
trace: [Compiler.saveBase] size: 1
    def u8Lit : UInt8 :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8Lit : UInt8 := 17 % 5

/--
trace: [Compiler.saveBase] size: 0
    def u8ModZero x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ModZero (x : UInt8) : UInt8 := x % 0

/--
trace: [Compiler.saveBase] size: 1
    def u8ZeroMod x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ZeroMod (x : UInt8) : UInt8 := 0 % x

/--
trace: [Compiler.saveBase] size: 1
    def u8ModOne x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ModOne (x : UInt8) : UInt8 := x % 1

/--
trace: [Compiler.saveBase] size: 2
    def u8NoFold x : UInt8 :=
      let _x.1 := 3;
      let _x.2 := UInt8.mod x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8NoFold (x : UInt8) : UInt8 := x % 3

/--
trace: [Compiler.saveBase] size: 1
    def u16Lit : UInt16 :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16Lit : UInt16 := 17 % 5

/--
trace: [Compiler.saveBase] size: 0
    def u16ModZero x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ModZero (x : UInt16) : UInt16 := x % 0

/--
trace: [Compiler.saveBase] size: 1
    def u16ZeroMod x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ZeroMod (x : UInt16) : UInt16 := 0 % x

/--
trace: [Compiler.saveBase] size: 1
    def u16ModOne x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ModOne (x : UInt16) : UInt16 := x % 1

/--
trace: [Compiler.saveBase] size: 2
    def u16NoFold x : UInt16 :=
      let _x.1 := 3;
      let _x.2 := UInt16.mod x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16NoFold (x : UInt16) : UInt16 := x % 3

/--
trace: [Compiler.saveBase] size: 1
    def u32Lit : UInt32 :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32Lit : UInt32 := 17 % 5

/--
trace: [Compiler.saveBase] size: 0
    def u32ModZero x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ModZero (x : UInt32) : UInt32 := x % 0

/--
trace: [Compiler.saveBase] size: 1
    def u32ZeroMod x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ZeroMod (x : UInt32) : UInt32 := 0 % x

/--
trace: [Compiler.saveBase] size: 1
    def u32ModOne x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ModOne (x : UInt32) : UInt32 := x % 1

/--
trace: [Compiler.saveBase] size: 2
    def u32NoFold x : UInt32 :=
      let _x.1 := 3;
      let _x.2 := UInt32.mod x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32NoFold (x : UInt32) : UInt32 := x % 3

/--
trace: [Compiler.saveBase] size: 1
    def u64Lit : UInt64 :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64Lit : UInt64 := 17 % 5

/--
trace: [Compiler.saveBase] size: 0
    def u64ModZero x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ModZero (x : UInt64) : UInt64 := x % 0

/--
trace: [Compiler.saveBase] size: 1
    def u64ZeroMod x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ZeroMod (x : UInt64) : UInt64 := 0 % x

/--
trace: [Compiler.saveBase] size: 1
    def u64ModOne x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ModOne (x : UInt64) : UInt64 := x % 1

/--
trace: [Compiler.saveBase] size: 2
    def u64NoFold x : UInt64 :=
      let _x.1 := 3;
      let _x.2 := UInt64.mod x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64NoFold (x : UInt64) : UInt64 := x % 3

/--
trace: [Compiler.saveBase] size: 1
    def usizeLit : USize :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeLit : USize := 17 % 5

/--
trace: [Compiler.saveBase] size: 0
    def usizeModZero x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeModZero (x : USize) : USize := x % 0

/--
trace: [Compiler.saveBase] size: 1
    def usizeZeroMod x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeZeroMod (x : USize) : USize := 0 % x

/--
trace: [Compiler.saveBase] size: 1
    def usizeModOne x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeModOne (x : USize) : USize := x % 1

/--
trace: [Compiler.saveBase] size: 2
    def usizeNoFold x : USize :=
      let _x.1 := 3;
      let _x.2 := USize.mod x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeNoFold (x : USize) : USize := x % 3

/--
trace: [Compiler.saveBase] size: 3
    def usizeLitNoFold : USize :=
      let _x.1 := 4294967296;
      let _x.2 := 4294967295;
      let _x.3 := USize.mod _x.1 _x.2;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeLitNoFold : USize := 4294967296 % 4294967295
