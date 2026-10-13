module
/-!
This test ensures that `Char` literals are recognized by the LCNF constant folder. In the base
phase a `Char` literal is `Char.ofNat` applied to a `Nat` literal; only from the mono phase on,
where `Char` is represented as `UInt32`, may it become a `UInt32` literal. `compiler.checkTypes`
verifies that the folded code stays well typed in both phases.
-/

public section

set_option compiler.checkTypes true

/--
trace: [Compiler.saveBase] size: 1
    def pushLit : String :=
      let _x.1 := "abcd";
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def pushLit : String := "abc".push 'd'

/--
trace: [Compiler.saveBase] size: 1
    def pushOfNat : String :=
      let _x.1 := "abcd";
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def pushOfNat : String := String.push "abc" (Char.ofNat 100)

/--
trace: [Compiler.saveBase] size: 2
    def pushVar c : String :=
      let _x.1 := "abc";
      let _x.2 := String.push _x.1 c;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def pushVar (c : Char) : String := "abc".push c

/--
trace: [Compiler.saveBase] size: 2
    def charOfNat : Char :=
      let _x.1 := 97;
      let _x.2 := Char.ofNat _x.1;
      return _x.2
[Compiler.saveMono] size: 1
    def charOfNat : UInt32 :=
      let _x.1 := 97;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
set_option trace.Compiler.saveMono true in
def charOfNat : Char := Char.ofNat 97

/--
trace: [Compiler.saveBase] size: 2
    def charLit : Char :=
      let _x.1 := 97;
      let _x.2 := Char.ofNat _x.1;
      return _x.2
[Compiler.saveMono] size: 1
    def charLit : UInt32 :=
      let _x.1 := 97;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
set_option trace.Compiler.saveMono true in
def charLit : Char := 'a'

/--
trace: [Compiler.saveBase] size: 2
    def charOfNatInvalid : Char :=
      let _x.1 := 55296;
      let _x.2 := Char.ofNat _x.1;
      return _x.2
[Compiler.saveMono] size: 1
    def charOfNatInvalid : UInt32 :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
set_option trace.Compiler.saveMono true in
def charOfNatInvalid : Char := Char.ofNat 0xD800

/--
trace: [Compiler.saveBase] size: 1
    def utf8SizeAscii : Nat :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def utf8SizeAscii : Nat := 'a'.utf8Size

/--
trace: [Compiler.saveBase] size: 1
    def utf8SizeTwoBytes : Nat :=
      let _x.1 := 2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def utf8SizeTwoBytes : Nat := 'é'.utf8Size

/--
trace: [Compiler.saveBase] size: 1
    def utf8SizeThreeBytes : Nat :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def utf8SizeThreeBytes : Nat := '€'.utf8Size

/--
trace: [Compiler.saveBase] size: 1
    def utf8SizeFourBytes : Nat :=
      let _x.1 := 4;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def utf8SizeFourBytes : Nat := '𝔸'.utf8Size

/--
trace: [Compiler.saveBase] size: 1
    def utf8SizeVar c : Nat :=
      let _x.1 := Char.utf8Size c;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def utf8SizeVar (c : Char) : Nat := c.utf8Size
