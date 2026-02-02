/-!
This test ensures that we constant fold Decidable related things in base already.
Previously the below code would produce a series of nested join points that would only ever be
simplified in the mono phase when we convert `Decidable` to `Bool`.
-/

/--
trace: [Compiler.saveBase] size: 33
    def f a b : BitVec lcAny :=
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := 4;
      let _x.5 := 5;
      let _x.6 := 6;
      let _x.7 := 7;
      let _x.8 := 0;
      let _x.9 := @BitVec.toNat _x.4 a;
      let _x.10 := Nat.testBit _x.9 _x.8;
      let _x.11 := BitVec.ofBool _x.10;
      let _x.12 := @BitVec.toNat _x.4 b;
      let _x.13 := Nat.testBit _x.12 _x.8;
      let _x.14 := BitVec.ofBool _x.13;
      let _x.15 := @BitVec.append _x.1 _x.1 _x.11 _x.14;
      let _x.16 := Nat.testBit _x.9 _x.1;
      let _x.17 := BitVec.ofBool _x.16;
      let _x.18 := @BitVec.append _x.2 _x.1 _x.15 _x.17;
      let _x.19 := Nat.testBit _x.12 _x.1;
      let _x.20 := BitVec.ofBool _x.19;
      let _x.21 := @BitVec.append _x.3 _x.1 _x.18 _x.20;
      let _x.22 := Nat.testBit _x.9 _x.2;
      let _x.23 := BitVec.ofBool _x.22;
      let _x.24 := @BitVec.append _x.4 _x.1 _x.21 _x.23;
      let _x.25 := Nat.testBit _x.12 _x.2;
      let _x.26 := BitVec.ofBool _x.25;
      let _x.27 := @BitVec.append _x.5 _x.1 _x.24 _x.26;
      let _x.28 := Nat.testBit _x.9 _x.3;
      let _x.29 := BitVec.ofBool _x.28;
      let _x.30 := @BitVec.append _x.6 _x.1 _x.27 _x.29;
      let _x.31 := Nat.testBit _x.12 _x.3;
      let _x.32 := BitVec.ofBool _x.31;
      let _x.33 := @BitVec.append _x.7 _x.1 _x.30 _x.32;
      return _x.33
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def f (a b : BitVec 4) :=
  BitVec.ofBool a[0]! ++ BitVec.ofBool b[0]! ++
  BitVec.ofBool a[1]! ++ BitVec.ofBool b[1]! ++
  BitVec.ofBool a[2]! ++ BitVec.ofBool b[2]! ++
  BitVec.ofBool a[3]! ++ BitVec.ofBool b[3]!
