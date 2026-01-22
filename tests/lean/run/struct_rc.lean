/-!
# Tests the `struct_rc` compiler pass
-/

@[extern]
opaque fn (a b : Nat) : Nat

/-!
The `struct_rc` pass correctly removes `inc` and `dec` instructions when possible.
-/

/--
trace: [Compiler.IR] [struct_rc]
    def test1 (x_1 : {tobj, tobj}) : tobj :=
      let x_2 : tobj := proj[0, 0] x_1;
      let x_3 : tobj := proj[0, 1] x_1;
      let x_4 : tobj := fn x_2 x_3;
      ret x_4
    def test1._boxed (x_1 : obj) : tobj :=
      let x_2 : {tobj, tobj} := unbox x_1;
      inc x_2;
      dec x_1;
      let x_3 : tobj := test1 x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.struct_rc true in
@[noinline]
def test1 (x : Nat × Nat) : Nat :=
  fn x.1 x.2

/-!
The `struct_rc` introduces new `inc` or `dec` instructions when needed.
-/

/--
trace: [Compiler.IR] [struct_rc]
    def test2 (x_1 : {tobj, tobj}) : tobj :=
      let x_2 : tobj := proj[0, 0] x_1;
      let x_4 : tobj := proj[0, 1] x_1;
      dec x_4;
      inc x_2;
      let x_3 : tobj := fn x_2 x_2;
      ret x_3
    def test2._boxed (x_1 : obj) : tobj :=
      let x_2 : {tobj, tobj} := unbox x_1;
      inc x_2;
      dec x_1;
      let x_3 : tobj := test2 x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.struct_rc true in
def test2 (x : Nat × Nat) : Nat :=
  fn x.1 x.1

/-!
The `struct_rc` pass may introduce double-decrements (which are otherwise impossible).
-/

def borrowedFn (x : Nat × Nat) : Nat :=
  x.1 + x.2

/--
trace: [Compiler.IR] [struct_rc]
    def test3 (x_1 : tobj) : tobj :=
      inc x_1;
      let x_2 : {tobj, tobj} := ctor_0[Prod.mk] x_1 x_1;
      let x_3 : tobj := borrowedFn x_2;
      dec[2] x_1;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.struct_rc true in
def test3 (a : Nat) : Nat :=
  borrowedFn (a, a)

/-!
The `struct_rc` pass doesn't apply reference counting instructions to persistent values (and
removes existing such RC instructions).
-/

@[noinline]
def persistentValue : Nat := 2^100

/--
trace: [Compiler.IR] [struct_rc]
    def test4 (x_1 : tagged) : tobj :=
      let x_2 : tobj := persistentValue;
      let x_3 : {tobj, tobj} := ctor_0[Prod.mk] x_2 x_2;
      let x_4 : tobj := borrowedFn x_3;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.struct_rc true in
set_option compiler.extract_closed false in
def test4 (_ : Unit) : Nat :=
  borrowedFn (persistentValue, persistentValue)
