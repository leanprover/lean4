module
/-!
This test checks LCNF simplifications around applying the operation to the same argument such as
`x - x`, `x &&& x` etc.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def natSubSelf x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natSubSelf (x : Nat) : Nat := x - x

/--
trace: [Compiler.saveBase] size: 1
    def natXorSelf x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natXorSelf (x : Nat) : Nat := x ^^^ x

/--
trace: [Compiler.saveBase] size: 0
    def natAndSelf x : Nat :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natAndSelf (x : Nat) : Nat := x &&& x

/--
trace: [Compiler.saveBase] size: 0
    def natOrSelf x : Nat :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natOrSelf (x : Nat) : Nat := x ||| x

/--
trace: [Compiler.saveBase] size: 1
    def natModSelf x : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natModSelf (x : Nat) : Nat := x % x

/--
trace: [Compiler.saveBase] size: 1
    def u8SubSelf x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8SubSelf (x : UInt8) : UInt8 := x - x

/--
trace: [Compiler.saveBase] size: 1
    def u8XorSelf x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8XorSelf (x : UInt8) : UInt8 := x ^^^ x

/--
trace: [Compiler.saveBase] size: 0
    def u8AndSelf x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8AndSelf (x : UInt8) : UInt8 := x &&& x

/--
trace: [Compiler.saveBase] size: 0
    def u8OrSelf x : UInt8 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OrSelf (x : UInt8) : UInt8 := x ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u8ModSelf x : UInt8 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ModSelf (x : UInt8) : UInt8 := x % x

/--
trace: [Compiler.saveBase] size: 1
    def u16SubSelf x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16SubSelf (x : UInt16) : UInt16 := x - x

/--
trace: [Compiler.saveBase] size: 1
    def u16XorSelf x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16XorSelf (x : UInt16) : UInt16 := x ^^^ x

/--
trace: [Compiler.saveBase] size: 0
    def u16AndSelf x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16AndSelf (x : UInt16) : UInt16 := x &&& x

/--
trace: [Compiler.saveBase] size: 0
    def u16OrSelf x : UInt16 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16OrSelf (x : UInt16) : UInt16 := x ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u16ModSelf x : UInt16 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u16ModSelf (x : UInt16) : UInt16 := x % x

/--
trace: [Compiler.saveBase] size: 1
    def u32SubSelf x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32SubSelf (x : UInt32) : UInt32 := x - x

/--
trace: [Compiler.saveBase] size: 1
    def u32XorSelf x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32XorSelf (x : UInt32) : UInt32 := x ^^^ x

/--
trace: [Compiler.saveBase] size: 0
    def u32AndSelf x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32AndSelf (x : UInt32) : UInt32 := x &&& x

/--
trace: [Compiler.saveBase] size: 0
    def u32OrSelf x : UInt32 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32OrSelf (x : UInt32) : UInt32 := x ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u32ModSelf x : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u32ModSelf (x : UInt32) : UInt32 := x % x

/--
trace: [Compiler.saveBase] size: 1
    def u64SubSelf x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64SubSelf (x : UInt64) : UInt64 := x - x

/--
trace: [Compiler.saveBase] size: 1
    def u64XorSelf x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64XorSelf (x : UInt64) : UInt64 := x ^^^ x

/--
trace: [Compiler.saveBase] size: 0
    def u64AndSelf x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64AndSelf (x : UInt64) : UInt64 := x &&& x

/--
trace: [Compiler.saveBase] size: 0
    def u64OrSelf x : UInt64 :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OrSelf (x : UInt64) : UInt64 := x ||| x

/--
trace: [Compiler.saveBase] size: 1
    def u64ModSelf x : UInt64 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ModSelf (x : UInt64) : UInt64 := x % x

/--
trace: [Compiler.saveBase] size: 1
    def usizeSubSelf x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeSubSelf (x : USize) : USize := x - x

/--
trace: [Compiler.saveBase] size: 1
    def usizeXorSelf x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeXorSelf (x : USize) : USize := x ^^^ x

/--
trace: [Compiler.saveBase] size: 0
    def usizeAndSelf x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeAndSelf (x : USize) : USize := x &&& x

/--
trace: [Compiler.saveBase] size: 0
    def usizeOrSelf x : USize :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeOrSelf (x : USize) : USize := x ||| x

/--
trace: [Compiler.saveBase] size: 1
    def usizeModSelf x : USize :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeModSelf (x : USize) : USize := x % x

/--
trace: [Compiler.saveBase] size: 1
    def natSubDistinct x y : Nat :=
      let _x.1 := Nat.sub x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natSubDistinct (x y : Nat) : Nat := x - y

/--
trace: [Compiler.saveBase] size: 1
    def natXorDistinct x y : Nat :=
      let _x.1 := Nat.xor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natXorDistinct (x y : Nat) : Nat := x ^^^ y

/--
trace: [Compiler.saveBase] size: 1
    def natAndDistinct x y : Nat :=
      let _x.1 := Nat.land x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natAndDistinct (x y : Nat) : Nat := x &&& y

/--
trace: [Compiler.saveBase] size: 1
    def natOrDistinct x y : Nat :=
      let _x.1 := Nat.lor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natOrDistinct (x y : Nat) : Nat := x ||| y

/--
trace: [Compiler.saveBase] size: 1
    def natModDistinct x y : Nat :=
      let _x.1 := Nat.mod x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natModDistinct (x y : Nat) : Nat := x % y

/--
trace: [Compiler.saveBase] size: 1
    def u8SubDistinct x y : UInt8 :=
      let _x.1 := UInt8.sub x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8SubDistinct (x y : UInt8) : UInt8 := x - y

/--
trace: [Compiler.saveBase] size: 1
    def u8XorDistinct x y : UInt8 :=
      let _x.1 := UInt8.xor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8XorDistinct (x y : UInt8) : UInt8 := x ^^^ y

/--
trace: [Compiler.saveBase] size: 1
    def u8AndDistinct x y : UInt8 :=
      let _x.1 := UInt8.land x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8AndDistinct (x y : UInt8) : UInt8 := x &&& y

/--
trace: [Compiler.saveBase] size: 1
    def u8OrDistinct x y : UInt8 :=
      let _x.1 := UInt8.lor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8OrDistinct (x y : UInt8) : UInt8 := x ||| y

/--
trace: [Compiler.saveBase] size: 1
    def u8ModDistinct x y : UInt8 :=
      let _x.1 := UInt8.mod x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u8ModDistinct (x y : UInt8) : UInt8 := x % y

/--
trace: [Compiler.saveBase] size: 1
    def u64SubDistinct x y : UInt64 :=
      let _x.1 := UInt64.sub x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64SubDistinct (x y : UInt64) : UInt64 := x - y

/--
trace: [Compiler.saveBase] size: 1
    def u64XorDistinct x y : UInt64 :=
      let _x.1 := UInt64.xor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64XorDistinct (x y : UInt64) : UInt64 := x ^^^ y

/--
trace: [Compiler.saveBase] size: 1
    def u64AndDistinct x y : UInt64 :=
      let _x.1 := UInt64.land x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64AndDistinct (x y : UInt64) : UInt64 := x &&& y

/--
trace: [Compiler.saveBase] size: 1
    def u64OrDistinct x y : UInt64 :=
      let _x.1 := UInt64.lor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64OrDistinct (x y : UInt64) : UInt64 := x ||| y

/--
trace: [Compiler.saveBase] size: 1
    def u64ModDistinct x y : UInt64 :=
      let _x.1 := UInt64.mod x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def u64ModDistinct (x y : UInt64) : UInt64 := x % y

/--
trace: [Compiler.saveBase] size: 1
    def usizeSubDistinct x y : USize :=
      let _x.1 := USize.sub x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeSubDistinct (x y : USize) : USize := x - y

/--
trace: [Compiler.saveBase] size: 1
    def usizeXorDistinct x y : USize :=
      let _x.1 := USize.xor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeXorDistinct (x y : USize) : USize := x ^^^ y

/--
trace: [Compiler.saveBase] size: 1
    def usizeAndDistinct x y : USize :=
      let _x.1 := USize.land x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeAndDistinct (x y : USize) : USize := x &&& y

/--
trace: [Compiler.saveBase] size: 1
    def usizeOrDistinct x y : USize :=
      let _x.1 := USize.lor x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeOrDistinct (x y : USize) : USize := x ||| y

/--
trace: [Compiler.saveBase] size: 1
    def usizeModDistinct x y : USize :=
      let _x.1 := USize.mod x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def usizeModDistinct (x y : USize) : USize := x % y

/--
trace: [Compiler.saveBase] size: 1
    def natDivSelf x : Nat :=
      let _x.1 := Nat.div x x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natDivSelf (x : Nat) : Nat := x / x
