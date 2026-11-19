module
/-!
This test checks that the LCNF constant folder handles `Nat.shiftLeft`/`Nat.shiftRight` and their
`UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize` counterparts.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def natLitShl : Nat :=
      let _x.1 := 12;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natLitShl : Nat := 3 <<< 2

/--
trace: [Compiler.saveBase] size: 1
    def natLitShr : Nat :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natLitShr : Nat := 12 >>> 2

/--
trace: [Compiler.saveBase] size: 1
    def natZeroShl x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natZeroShl (x : Nat) : Nat := 0 <<< x

/--
trace: [Compiler.saveBase] size: 1
    def natZeroShr x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natZeroShr (x : Nat) : Nat := 0 >>> x

/--
trace: [Compiler.saveBase] size: 0
    def natShlZero x : Nat :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natShlZero (x : Nat) : Nat := x <<< 0

/--
trace: [Compiler.saveBase] size: 0
    def natShrZero x : Nat :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natShrZero (x : Nat) : Nat := x >>> 0

/--
trace: [Compiler.saveBase] size: 2
    def natShlOne x : Nat :=
      let _x.1 := 1;
      let _x.2 := Nat.shiftLeft x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natShlOne (x : Nat) : Nat := x <<< 1

/--
trace: [Compiler.saveBase] size: 1
    def natShrVar x y : Nat :=
      let _x.1 := Nat.shiftRight x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natShrVar (x y : Nat) : Nat := x >>> y

/--
trace: [Compiler.saveBase] size: 1
    def u8LitShl : UInt8 :=
      let _x.1 := 12;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8LitShl : UInt8 := (3 : UInt8) <<< (2 : UInt8)

/--
trace: [Compiler.saveBase] size: 1
    def u8LitShr : UInt8 :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8LitShr : UInt8 := (12 : UInt8) >>> (2 : UInt8)

/--
trace: [Compiler.saveBase] size: 1
    def u8ZeroShl x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ZeroShl (x : UInt8) : UInt8 := 0 <<< x

/--
trace: [Compiler.saveBase] size: 1
    def u8ZeroShr x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ZeroShr (x : UInt8) : UInt8 := 0 >>> x

/--
trace: [Compiler.saveBase] size: 0
    def u8ShlZero x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ShlZero (x : UInt8) : UInt8 := x <<< 0

/--
trace: [Compiler.saveBase] size: 0
    def u8ShrZero x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ShrZero (x : UInt8) : UInt8 := x >>> 0

/--
trace: [Compiler.saveBase] size: 2
    def u8ShlOne x : UInt8 :=
      let _x.1 := 1;
      let _x.2 := UInt8.shiftLeft x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ShlOne (x : UInt8) : UInt8 := x <<< 1

/--
trace: [Compiler.saveBase] size: 1
    def u8ShrVar x y : UInt8 :=
      let _x.1 := UInt8.shiftRight x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ShrVar (x y : UInt8) : UInt8 := x >>> y

/--
trace: [Compiler.saveBase] size: 1
    def u16ZeroShl x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ZeroShl (x : UInt16) : UInt16 := 0 <<< x

/--
trace: [Compiler.saveBase] size: 1
    def u16ZeroShr x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ZeroShr (x : UInt16) : UInt16 := 0 >>> x

/--
trace: [Compiler.saveBase] size: 2
    def u16ShlOne x : UInt16 :=
      let _x.1 := 1;
      let _x.2 := UInt16.shiftLeft x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ShlOne (x : UInt16) : UInt16 := x <<< 1

/--
trace: [Compiler.saveBase] size: 1
    def u32ZeroShl x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ZeroShl (x : UInt32) : UInt32 := 0 <<< x

/--
trace: [Compiler.saveBase] size: 1
    def u32ZeroShr x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ZeroShr (x : UInt32) : UInt32 := 0 >>> x

/--
trace: [Compiler.saveBase] size: 1
    def u32ShrVar x y : UInt32 :=
      let _x.1 := UInt32.shiftRight x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ShrVar (x y : UInt32) : UInt32 := x >>> y

/--
trace: [Compiler.saveBase] size: 1
    def u64LitShl : UInt64 :=
      let _x.1 := 12;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64LitShl : UInt64 := (3 : UInt64) <<< (2 : UInt64)

/--
trace: [Compiler.saveBase] size: 1
    def u64ZeroShl x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ZeroShl (x : UInt64) : UInt64 := 0 <<< x

/--
trace: [Compiler.saveBase] size: 1
    def u64ZeroShr x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ZeroShr (x : UInt64) : UInt64 := 0 >>> x

/--
trace: [Compiler.saveBase] size: 0
    def u64ShrZero x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ShrZero (x : UInt64) : UInt64 := x >>> 0

/--
trace: [Compiler.saveBase] size: 2
    def u64ShlOne x : UInt64 :=
      let _x.1 := 1;
      let _x.2 := UInt64.shiftLeft x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ShlOne (x : UInt64) : UInt64 := x <<< 1

/--
trace: [Compiler.saveBase] size: 1
    def usizeLitShl : USize :=
      let _x.1 := 12;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeLitShl : USize := (3 : USize) <<< (2 : USize)

/--
trace: [Compiler.saveBase] size: 1
    def usizeLitShr : USize :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeLitShr : USize := (12 : USize) >>> (2 : USize)

/--
trace: [Compiler.saveBase] size: 1
    def usizeZeroShl x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeZeroShl (x : USize) : USize := 0 <<< x

/--
trace: [Compiler.saveBase] size: 1
    def usizeZeroShr x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeZeroShr (x : USize) : USize := 0 >>> x

/--
trace: [Compiler.saveBase] size: 0
    def usizeShlZero x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeShlZero (x : USize) : USize := x <<< 0

/--
trace: [Compiler.saveBase] size: 0
    def usizeShrZero x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeShrZero (x : USize) : USize := x >>> 0

/--
trace: [Compiler.saveBase] size: 2
    def usizeShlOne x : USize :=
      let _x.1 := 1;
      let _x.2 := USize.shiftLeft x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeShlOne (x : USize) : USize := x <<< 1

/--
trace: [Compiler.saveBase] size: 1
    def usizeShrVar x y : USize :=
      let _x.1 := USize.shiftRight x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeShrVar (x y : USize) : USize := x >>> y
