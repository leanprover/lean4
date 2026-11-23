module
/-!
This test checks that the LCNF constant folder treats handles all-ones value of
`UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize` on `&&&` and `|||`.
-/

public section

/--
trace: [Compiler.saveBase] size: 0
    def u8AndOnes x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8AndOnes (x : UInt8) : UInt8 := x &&& 255

/--
trace: [Compiler.saveBase] size: 0
    def u8OnesAnd x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OnesAnd (x : UInt8) : UInt8 := 255 &&& x

/--
trace: [Compiler.saveBase] size: 1
    def u8OrOnes x : UInt8 :=
      let _x.1 := 255;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OrOnes (x : UInt8) : UInt8 := x ||| 255

/--
trace: [Compiler.saveBase] size: 1
    def u8OnesOr x : UInt8 :=
      let _x.1 := 255;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OnesOr (x : UInt8) : UInt8 := 255 ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u8AndZero x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8AndZero (x : UInt8) : UInt8 := x &&& 0

/--
trace: [Compiler.saveBase] size: 0
    def u8OrZero x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OrZero (x : UInt8) : UInt8 := x ||| 0

/--
trace: [Compiler.saveBase] size: 2
    def u8AndFive x : UInt8 :=
      let _x.1 := 5;
      let _x.2 := UInt8.land x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8AndFive (x : UInt8) : UInt8 := x &&& 5

/--
trace: [Compiler.saveBase] size: 2
    def u8OrFive x : UInt8 :=
      let _x.1 := 5;
      let _x.2 := UInt8.lor x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OrFive (x : UInt8) : UInt8 := x ||| 5

/--
trace: [Compiler.saveBase] size: 0
    def u16AndOnes x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16AndOnes (x : UInt16) : UInt16 := x &&& 65535

/--
trace: [Compiler.saveBase] size: 0
    def u16OnesAnd x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16OnesAnd (x : UInt16) : UInt16 := 65535 &&& x

/--
trace: [Compiler.saveBase] size: 1
    def u16OrOnes x : UInt16 :=
      let _x.1 := 65535;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16OrOnes (x : UInt16) : UInt16 := x ||| 65535

/--
trace: [Compiler.saveBase] size: 1
    def u16OnesOr x : UInt16 :=
      let _x.1 := 65535;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16OnesOr (x : UInt16) : UInt16 := 65535 ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u16AndZero x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16AndZero (x : UInt16) : UInt16 := x &&& 0

/--
trace: [Compiler.saveBase] size: 0
    def u16OrZero x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16OrZero (x : UInt16) : UInt16 := x ||| 0

/--
trace: [Compiler.saveBase] size: 2
    def u16AndFive x : UInt16 :=
      let _x.1 := 5;
      let _x.2 := UInt16.land x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16AndFive (x : UInt16) : UInt16 := x &&& 5

/--
trace: [Compiler.saveBase] size: 2
    def u16OrFive x : UInt16 :=
      let _x.1 := 5;
      let _x.2 := UInt16.lor x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16OrFive (x : UInt16) : UInt16 := x ||| 5

/--
trace: [Compiler.saveBase] size: 0
    def u32AndOnes x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32AndOnes (x : UInt32) : UInt32 := x &&& 4294967295

/--
trace: [Compiler.saveBase] size: 0
    def u32OnesAnd x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32OnesAnd (x : UInt32) : UInt32 := 4294967295 &&& x

/--
trace: [Compiler.saveBase] size: 1
    def u32OrOnes x : UInt32 :=
      let _x.1 := 4294967295;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32OrOnes (x : UInt32) : UInt32 := x ||| 4294967295

/--
trace: [Compiler.saveBase] size: 1
    def u32OnesOr x : UInt32 :=
      let _x.1 := 4294967295;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32OnesOr (x : UInt32) : UInt32 := 4294967295 ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u32AndZero x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32AndZero (x : UInt32) : UInt32 := x &&& 0

/--
trace: [Compiler.saveBase] size: 0
    def u32OrZero x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32OrZero (x : UInt32) : UInt32 := x ||| 0

/--
trace: [Compiler.saveBase] size: 2
    def u32AndFive x : UInt32 :=
      let _x.1 := 5;
      let _x.2 := UInt32.land x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32AndFive (x : UInt32) : UInt32 := x &&& 5

/--
trace: [Compiler.saveBase] size: 2
    def u32OrFive x : UInt32 :=
      let _x.1 := 5;
      let _x.2 := UInt32.lor x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32OrFive (x : UInt32) : UInt32 := x ||| 5

/--
trace: [Compiler.saveBase] size: 0
    def u64AndOnes x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64AndOnes (x : UInt64) : UInt64 := x &&& 18446744073709551615

/--
trace: [Compiler.saveBase] size: 0
    def u64OnesAnd x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OnesAnd (x : UInt64) : UInt64 := 18446744073709551615 &&& x

/--
trace: [Compiler.saveBase] size: 1
    def u64OrOnes x : UInt64 :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OrOnes (x : UInt64) : UInt64 := x ||| 18446744073709551615

/--
trace: [Compiler.saveBase] size: 1
    def u64OnesOr x : UInt64 :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OnesOr (x : UInt64) : UInt64 := 18446744073709551615 ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u64AndZero x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64AndZero (x : UInt64) : UInt64 := x &&& 0

/--
trace: [Compiler.saveBase] size: 0
    def u64OrZero x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OrZero (x : UInt64) : UInt64 := x ||| 0

/--
trace: [Compiler.saveBase] size: 2
    def u64AndFive x : UInt64 :=
      let _x.1 := 5;
      let _x.2 := UInt64.land x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64AndFive (x : UInt64) : UInt64 := x &&& 5

/--
trace: [Compiler.saveBase] size: 2
    def u64OrFive x : UInt64 :=
      let _x.1 := 5;
      let _x.2 := UInt64.lor x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OrFive (x : UInt64) : UInt64 := x ||| 5

/--
trace: [Compiler.saveBase] size: 0
    def usAndOnes x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usAndOnes (x : USize) : USize := x &&& 18446744073709551615

/--
trace: [Compiler.saveBase] size: 0
    def usOnesAnd x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usOnesAnd (x : USize) : USize := 18446744073709551615 &&& x

/--
trace: [Compiler.saveBase] size: 1
    def usOrOnes x : USize :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usOrOnes (x : USize) : USize := x ||| 18446744073709551615

/--
trace: [Compiler.saveBase] size: 1
    def usOnesOr x : USize :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usOnesOr (x : USize) : USize := 18446744073709551615 ||| x

/--
trace: [Compiler.saveBase] size: 1
    def usAndZero x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usAndZero (x : USize) : USize := x &&& 0

/--
trace: [Compiler.saveBase] size: 0
    def usOrZero x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usOrZero (x : USize) : USize := x ||| 0

/--
trace: [Compiler.saveBase] size: 2
    def usAndFive x : USize :=
      let _x.1 := 5;
      let _x.2 := USize.land x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usAndFive (x : USize) : USize := x &&& 5

/--
trace: [Compiler.saveBase] size: 2
    def usOrFive x : USize :=
      let _x.1 := 5;
      let _x.2 := USize.lor x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usOrFive (x : USize) : USize := x ||| 5

/--
trace: [Compiler.saveBase] size: 2
    def usAndOnes32 x : USize :=
      let _x.1 := 4294967295;
      let _x.2 := USize.land x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usAndOnes32 (x : USize) : USize := x &&& 4294967295

/--
trace: [Compiler.saveBase] size: 2
    def usOrOnes32 x : USize :=
      let _x.1 := 4294967295;
      let _x.2 := USize.lor x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usOrOnes32 (x : USize) : USize := x ||| 4294967295
