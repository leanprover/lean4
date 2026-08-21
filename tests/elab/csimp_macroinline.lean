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
trace: [Compiler.init] size: 7
    def myIteTest c t e : Nat :=
      let _x.1 := true;
      let _x.2 := instDecidableEqBool c _x.1;
      cases _x.2 : Nat
      | Decidable.isFalse x.3 =>
        let _x.4 := Nat.add e e;
        return _x.4
      | Decidable.isTrue x.5 =>
        let _x.6 := Nat.add t t;
        return _x.6
-/
#guard_msgs in
set_option trace.Compiler.init true in
def myIteTest (c : Bool) (t e : Nat) : Nat := myIte c (Nat.add t t) (Nat.add e e)
