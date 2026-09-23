module
/-!
This test checks that the LCNF constant folder folds `UInt8.neg`/`UInt16.neg`/`UInt32.neg`/
`UInt64.neg` applied to a literal.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def u8NegOne : UInt8 :=
      let _x.1 := 255;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8NegOne : UInt8 := -(1 : UInt8)

/--
trace: [Compiler.saveBase] size: 1
    def u8NegZero : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8NegZero : UInt8 := -(0 : UInt8)

/--
trace: [Compiler.saveBase] size: 1
    def u8NegFive : UInt8 :=
      let _x.1 := 251;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8NegFive : UInt8 := -(5 : UInt8)

/--
trace: [Compiler.saveBase] size: 1
    def u8NegNegFive : UInt8 :=
      let _x.1 := 5;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8NegNegFive : UInt8 := -(-(5 : UInt8))

/--
trace: [Compiler.saveBase] size: 0
    def u8AndNegOne x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8AndNegOne (x : UInt8) : UInt8 := x &&& -1

/--
trace: [Compiler.saveBase] size: 1
    def u8OrNegOne x : UInt8 :=
      let _x.1 := 255;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OrNegOne (x : UInt8) : UInt8 := x ||| -1

/--
trace: [Compiler.saveBase] size: 1
    def u8NegVar x : UInt8 :=
      let _x.1 := UInt8.neg x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8NegVar (x : UInt8) : UInt8 := -x

/--
trace: [Compiler.saveBase] size: 1
    def u16NegOne : UInt16 :=
      let _x.1 := 65535;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16NegOne : UInt16 := -(1 : UInt16)

/--
trace: [Compiler.saveBase] size: 1
    def u16NegZero : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16NegZero : UInt16 := -(0 : UInt16)

/--
trace: [Compiler.saveBase] size: 1
    def u16NegFive : UInt16 :=
      let _x.1 := 65531;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16NegFive : UInt16 := -(5 : UInt16)

/--
trace: [Compiler.saveBase] size: 1
    def u16NegNegFive : UInt16 :=
      let _x.1 := 5;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16NegNegFive : UInt16 := -(-(5 : UInt16))

/--
trace: [Compiler.saveBase] size: 0
    def u16AndNegOne x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16AndNegOne (x : UInt16) : UInt16 := x &&& -1

/--
trace: [Compiler.saveBase] size: 1
    def u16OrNegOne x : UInt16 :=
      let _x.1 := 65535;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16OrNegOne (x : UInt16) : UInt16 := x ||| -1

/--
trace: [Compiler.saveBase] size: 1
    def u16NegVar x : UInt16 :=
      let _x.1 := UInt16.neg x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16NegVar (x : UInt16) : UInt16 := -x

/--
trace: [Compiler.saveBase] size: 1
    def u32NegOne : UInt32 :=
      let _x.1 := 4294967295;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32NegOne : UInt32 := -(1 : UInt32)

/--
trace: [Compiler.saveBase] size: 1
    def u32NegZero : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32NegZero : UInt32 := -(0 : UInt32)

/--
trace: [Compiler.saveBase] size: 1
    def u32NegFive : UInt32 :=
      let _x.1 := 4294967291;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32NegFive : UInt32 := -(5 : UInt32)

/--
trace: [Compiler.saveBase] size: 1
    def u32NegNegFive : UInt32 :=
      let _x.1 := 5;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32NegNegFive : UInt32 := -(-(5 : UInt32))

/--
trace: [Compiler.saveBase] size: 0
    def u32AndNegOne x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32AndNegOne (x : UInt32) : UInt32 := x &&& -1

/--
trace: [Compiler.saveBase] size: 1
    def u32OrNegOne x : UInt32 :=
      let _x.1 := 4294967295;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32OrNegOne (x : UInt32) : UInt32 := x ||| -1

/--
trace: [Compiler.saveBase] size: 1
    def u32NegVar x : UInt32 :=
      let _x.1 := UInt32.neg x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32NegVar (x : UInt32) : UInt32 := -x

/--
trace: [Compiler.saveBase] size: 1
    def u64NegOne : UInt64 :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64NegOne : UInt64 := -(1 : UInt64)

/--
trace: [Compiler.saveBase] size: 1
    def u64NegZero : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64NegZero : UInt64 := -(0 : UInt64)

/--
trace: [Compiler.saveBase] size: 1
    def u64NegFive : UInt64 :=
      let _x.1 := 18446744073709551611;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64NegFive : UInt64 := -(5 : UInt64)

/--
trace: [Compiler.saveBase] size: 1
    def u64NegNegFive : UInt64 :=
      let _x.1 := 5;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64NegNegFive : UInt64 := -(-(5 : UInt64))

/--
trace: [Compiler.saveBase] size: 0
    def u64AndNegOne x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64AndNegOne (x : UInt64) : UInt64 := x &&& -1

/--
trace: [Compiler.saveBase] size: 1
    def u64OrNegOne x : UInt64 :=
      let _x.1 := 18446744073709551615;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OrNegOne (x : UInt64) : UInt64 := x ||| -1

/--
trace: [Compiler.saveBase] size: 1
    def u64NegVar x : UInt64 :=
      let _x.1 := UInt64.neg x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64NegVar (x : UInt64) : UInt64 := -x

/--
trace: [Compiler.saveBase] size: 1
    def usNegZero : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usNegZero : USize := -(0 : USize)

/--
trace: [Compiler.saveBase] size: 2
    def usNegOne : USize :=
      let _x.1 := 1;
      let _x.2 := USize.neg _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usNegOne : USize := -(1 : USize)

/--
trace: [Compiler.saveBase] size: 1
    def usNegVar x : USize :=
      let _x.1 := USize.neg x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usNegVar (x : USize) : USize := -x
