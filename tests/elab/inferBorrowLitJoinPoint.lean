/-!
Borrow inference must not make a join point parameter borrowed if a jump passes it a literal that
is allocated at runtime, as nothing would release the literal. Found through the test of #15235.
Closed term extraction hides this by turning such literals into persistent constants.
-/

set_option compiler.extract_closed false

@[noinline] def useBorrowed (s : @& String) : Nat := s.length

@[noinline] def useBorrowedNat (n : @& Nat) : Nat := n + 1

set_option trace.compiler.ir.result true

/--
trace: [Compiler.IR] [result]
    def strLit (x_1 : u8) (x_2 : @& obj) : tobj :=
      block_1 (x_3 : obj) :=
        let x_4 : tobj := useBorrowed x_3;
        dec x_3;
        let x_5 : tobj := useBorrowed x_2;
        let x_6 : tobj := Nat.add x_4 x_5;
        dec x_5;
        dec x_4;
        ret x_6;
      case x_1 : u8 of
      Bool.false →
        let x_7 : obj := "f";
        jmp block_1 x_7
      Bool.true →
        let x_8 : obj := "t";
        jmp block_1 x_8
    def strLit._boxed (x_1 : tagged) (x_2 : obj) : tobj :=
      let x_3 : u8 := unbox x_1;
      let x_4 : tobj := strLit x_3 x_2;
      dec x_2;
      ret x_4
-/
#guard_msgs in
@[noinline] def strLit (b : Bool) (t : @& String) : Nat :=
  let s := if b then "t" else "f"
  useBorrowed s + useBorrowed t

/-!
Literals too big for a tagged pointer are allocated as well.
-/

/--
trace: [Compiler.IR] [result]
    def bigNatLit (x_1 : u8) (x_2 : @& tobj) : tobj :=
      block_1 (x_3 : tobj) :=
        let x_4 : tobj := useBorrowedNat x_3;
        dec x_3;
        let x_5 : tobj := useBorrowedNat x_2;
        let x_6 : tobj := Nat.add x_4 x_5;
        dec x_5;
        dec x_4;
        ret x_6;
      case x_1 : u8 of
      Bool.false →
        inc x_2;
        jmp block_1 x_2
      Bool.true →
        let x_7 : tobj := 100000000000000000000000;
        jmp block_1 x_7
    def bigNatLit._boxed (x_1 : tagged) (x_2 : tobj) : tobj :=
      let x_3 : u8 := unbox x_1;
      let x_4 : tobj := bigNatLit x_3 x_2;
      dec x_2;
      ret x_4
-/
#guard_msgs in
@[noinline] def bigNatLit (b : Bool) (t : @& Nat) : Nat :=
  let n := if b then 100000000000000000000000 else t
  useBorrowedNat n + useBorrowedNat t

/-!
Small literals are tagged pointers, so the parameter can stay borrowed.
-/

/--
trace: [Compiler.IR] [result]
    def smallNatLit (x_1 : u8) (x_2 : @& tobj) : tobj :=
      block_1 (x_3 : @& tobj) :=
        let x_4 : tobj := useBorrowedNat x_3;
        let x_5 : tobj := useBorrowedNat x_2;
        let x_6 : tobj := Nat.add x_4 x_5;
        dec x_5;
        dec x_4;
        ret x_6;
      case x_1 : u8 of
      Bool.false →
        jmp block_1 x_2
      Bool.true →
        let x_7 : tagged := 0;
        jmp block_1 x_7
    def smallNatLit._boxed (x_1 : tagged) (x_2 : tobj) : tobj :=
      let x_3 : u8 := unbox x_1;
      let x_4 : tobj := smallNatLit x_3 x_2;
      dec x_2;
      ret x_4
-/
#guard_msgs in
@[noinline] def smallNatLit (b : Bool) (t : @& Nat) : Nat :=
  let n := if b then 0 else t
  useBorrowedNat n + useBorrowedNat t
