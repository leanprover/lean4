/-!
This test checks that the LCNF constant folder handles `Nat.pow`.
-/

/--
trace: [Compiler.saveBase] size: 1
    def natLit : Nat :=
      let _x.1 := 1024;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natLit : Nat := 2 ^ 10

/--
trace: [Compiler.saveBase] size: 1
    def natPowZero x : Nat :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natPowZero (x : Nat) : Nat := x ^ 0

/--
trace: [Compiler.saveBase] size: 0
    def natPowOne x : Nat :=
      return x
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natPowOne (x : Nat) : Nat := x ^ 1

/--
trace: [Compiler.saveBase] size: 1
    def natOnePow x : Nat :=
      let _x.1 := 1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natOnePow (x : Nat) : Nat := 1 ^ x

/--
trace: [Compiler.saveBase] size: 2
    def natZeroPow x : Nat :=
      let _x.1 := 0;
      let _x.2 := Nat.pow _x.1 x;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natZeroPow (x : Nat) : Nat := 0 ^ x

/--
trace: [Compiler.saveBase] size: 2
    def natPowTwo x : Nat :=
      let _x.1 := 2;
      let _x.2 := Nat.pow x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natPowTwo (x : Nat) : Nat := x ^ 2

/--
trace: [Compiler.saveBase] size: 2
    def natTwoPow x : Nat :=
      let _x.1 := 2;
      let _x.2 := Nat.pow _x.1 x;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natTwoPow (x : Nat) : Nat := 2 ^ x

/--
trace: [Compiler.saveBase] size: 1
    def natPowVar x y : Nat :=
      let _x.1 := Nat.pow x y;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def natPowVar (x y : Nat) : Nat := x ^ y
