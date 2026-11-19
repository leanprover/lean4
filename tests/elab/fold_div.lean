module
/-!
This test checks that the LCNF constant folder handles `Nat.div` and its `UInt8`/`UInt16`/
`UInt32`/`UInt64`/`USize` counterparts.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def natLit : Nat :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natLit : Nat := 7 / 2

/--
trace: [Compiler.saveBase] size: 1
    def natZeroDiv x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natZeroDiv (x : Nat) : Nat := 0 / x

/--
trace: [Compiler.saveBase] size: 0
    def natDivOne x : Nat :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natDivOne (x : Nat) : Nat := x / 1

/--
trace: [Compiler.saveBase] size: 2
    def natDivShift x : Nat :=
      let _x.1 := 1;
      let _x.2 := Nat.shiftRight x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natDivShift (x : Nat) : Nat := x / 2

/--
trace: [Compiler.saveBase] size: 2
    def natNoFold x : Nat :=
      let _x.1 := 3;
      let _x.2 := Nat.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natNoFold (x : Nat) : Nat := x / 3

/--
trace: [Compiler.saveBase] size: 2
    def natDivZero x : Nat :=
      let _x.1 := 0;
      let _x.2 := Nat.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natDivZero (x : Nat) : Nat := x / 0

/--
trace: [Compiler.saveBase] size: 1
    def u8Lit : UInt8 :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8Lit : UInt8 := 7 / 2

/--
trace: [Compiler.saveBase] size: 1
    def u8ZeroDiv x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ZeroDiv (x : UInt8) : UInt8 := 0 / x

/--
trace: [Compiler.saveBase] size: 0
    def u8DivOne x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8DivOne (x : UInt8) : UInt8 := x / 1

/--
trace: [Compiler.saveBase] size: 2
    def u8DivShift x : UInt8 :=
      let _x.1 := 1;
      let _x.2 := UInt8.shiftRight x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8DivShift (x : UInt8) : UInt8 := x / 2

/--
trace: [Compiler.saveBase] size: 2
    def u8NoFold x : UInt8 :=
      let _x.1 := 3;
      let _x.2 := UInt8.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8NoFold (x : UInt8) : UInt8 := x / 3

/--
trace: [Compiler.saveBase] size: 2
    def u8DivZero x : UInt8 :=
      let _x.1 := 0;
      let _x.2 := UInt8.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8DivZero (x : UInt8) : UInt8 := x / 0

/--
trace: [Compiler.saveBase] size: 1
    def u16Lit : UInt16 :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16Lit : UInt16 := 7 / 2

/--
trace: [Compiler.saveBase] size: 1
    def u16ZeroDiv x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ZeroDiv (x : UInt16) : UInt16 := 0 / x

/--
trace: [Compiler.saveBase] size: 0
    def u16DivOne x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16DivOne (x : UInt16) : UInt16 := x / 1

/--
trace: [Compiler.saveBase] size: 2
    def u16DivShift x : UInt16 :=
      let _x.1 := 1;
      let _x.2 := UInt16.shiftRight x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16DivShift (x : UInt16) : UInt16 := x / 2

/--
trace: [Compiler.saveBase] size: 2
    def u16NoFold x : UInt16 :=
      let _x.1 := 3;
      let _x.2 := UInt16.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16NoFold (x : UInt16) : UInt16 := x / 3

/--
trace: [Compiler.saveBase] size: 2
    def u16DivZero x : UInt16 :=
      let _x.1 := 0;
      let _x.2 := UInt16.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16DivZero (x : UInt16) : UInt16 := x / 0

/--
trace: [Compiler.saveBase] size: 1
    def u32Lit : UInt32 :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32Lit : UInt32 := 7 / 2

/--
trace: [Compiler.saveBase] size: 1
    def u32ZeroDiv x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ZeroDiv (x : UInt32) : UInt32 := 0 / x

/--
trace: [Compiler.saveBase] size: 0
    def u32DivOne x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32DivOne (x : UInt32) : UInt32 := x / 1

/--
trace: [Compiler.saveBase] size: 2
    def u32DivShift x : UInt32 :=
      let _x.1 := 1;
      let _x.2 := UInt32.shiftRight x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32DivShift (x : UInt32) : UInt32 := x / 2

/--
trace: [Compiler.saveBase] size: 2
    def u32NoFold x : UInt32 :=
      let _x.1 := 3;
      let _x.2 := UInt32.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32NoFold (x : UInt32) : UInt32 := x / 3

/--
trace: [Compiler.saveBase] size: 2
    def u32DivZero x : UInt32 :=
      let _x.1 := 0;
      let _x.2 := UInt32.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32DivZero (x : UInt32) : UInt32 := x / 0

/--
trace: [Compiler.saveBase] size: 1
    def u64Lit : UInt64 :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64Lit : UInt64 := 7 / 2

/--
trace: [Compiler.saveBase] size: 1
    def u64ZeroDiv x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ZeroDiv (x : UInt64) : UInt64 := 0 / x

/--
trace: [Compiler.saveBase] size: 0
    def u64DivOne x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64DivOne (x : UInt64) : UInt64 := x / 1

/--
trace: [Compiler.saveBase] size: 2
    def u64DivShift x : UInt64 :=
      let _x.1 := 1;
      let _x.2 := UInt64.shiftRight x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64DivShift (x : UInt64) : UInt64 := x / 2

/--
trace: [Compiler.saveBase] size: 2
    def u64NoFold x : UInt64 :=
      let _x.1 := 3;
      let _x.2 := UInt64.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64NoFold (x : UInt64) : UInt64 := x / 3

/--
trace: [Compiler.saveBase] size: 2
    def u64DivZero x : UInt64 :=
      let _x.1 := 0;
      let _x.2 := UInt64.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64DivZero (x : UInt64) : UInt64 := x / 0

/--
trace: [Compiler.saveBase] size: 1
    def usizeLit : USize :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeLit : USize := 7 / 2

/--
trace: [Compiler.saveBase] size: 1
    def usizeZeroDiv x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeZeroDiv (x : USize) : USize := 0 / x

/--
trace: [Compiler.saveBase] size: 0
    def usizeDivOne x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeDivOne (x : USize) : USize := x / 1

/--
trace: [Compiler.saveBase] size: 2
    def usizeDivShift x : USize :=
      let _x.1 := 1;
      let _x.2 := USize.shiftRight x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeDivShift (x : USize) : USize := x / 2

/--
trace: [Compiler.saveBase] size: 2
    def usizeNoFold x : USize :=
      let _x.1 := 3;
      let _x.2 := USize.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeNoFold (x : USize) : USize := x / 3

/--
trace: [Compiler.saveBase] size: 2
    def usizeDivZero x : USize :=
      let _x.1 := 0;
      let _x.2 := USize.div x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeDivZero (x : USize) : USize := x / 0
