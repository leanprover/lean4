/-! We need to execute `csimp` both before and after `macr_inline` -/

@[macro_inline]
def myLength (xs : List Nat) : Nat := xs.length

/--
trace: [Compiler.init] size: 1
    def myLengthTest xs : Nat :=
      let _x.1 := @List.lengthTR _ xs;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.init true in
def myLengthTest (xs : List Nat) : Nat := myLength xs

@[noinline]
def myIte (c : Bool) (t e : Nat) : Nat := if c then t else e

@[macro_inline]
def myIte' (c : Bool) (t e : Nat) : Nat := if c then t else e

@[csimp]
theorem myIteThm : @myIte = @myIte' := rfl

/--
trace: [Compiler.init] size: 8
    def myIteTest c t e : Nat :=
      let _x.1 := true;
      let _x.2 := Bool.decEq c _x.1;
      let _x.3 := _x.2 # 0;
      cases _x.3 : Nat
      | Bool.false =>
        let _x.4 := Nat.add e e;
        return _x.4
      | Bool.true =>
        let _x.5 := Nat.add t t;
        return _x.5
-/
#guard_msgs in
set_option trace.Compiler.init true in
def myIteTest (c : Bool) (t e : Nat) : Nat := myIte c (Nat.add t t) (Nat.add e e)
