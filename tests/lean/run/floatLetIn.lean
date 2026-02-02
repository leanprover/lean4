/-!
# Tests for the `floatLetIn` compiler pass
-/

structure State where
  abc : Nat
  xyz : Array Nat
  bool : Bool
deriving Inhabited

def State.size (t : State) : Nat := t.xyz.size

@[extern]
opaque State.restore (abc : Nat) (size : Nat) (s : State) : State

def StateFn := State → State

set_option trace.Compiler.result true

/-!
The `floatLetIn` pass moves values (here `st.size`) into one branch if they are only used in that
branch.
-/

/--
trace: [Compiler.result] size: 7
    def test1 st : State :=
      cases st : State
      | State.mk abc xyz bool =>
        cases bool : State
        | Bool.false =>
          return st
        | Bool.true =>
          let b := State.size st;
          let _x.1 := State.restore abc b st;
          return _x.1
-/
#guard_msgs in
def test1 : StateFn := fun st =>
  let a := st.abc
  let b := st.size
  if st.bool then
    st.restore a b
  else
    st

/-!
This doesn't occur if it would destroy linearity.
-/

/--
trace: [Compiler.result] size: 10
    def test2 fn st : State :=
      cases st : State
      | State.mk abc xyz bool =>
        let b := State.size st;
        let st := fn st;
        cases st : State
        | State.mk abc xyz bool =>
          cases bool : State
          | Bool.false =>
            return st
          | Bool.true =>
            let _x.1 := State.restore abc b st;
            return _x.1
-/
#guard_msgs in
def test2 (fn : StateFn) : StateFn := fun st =>
  let a := st.abc
  let b := st.size
  let st := fn st
  if st.bool then
    st.restore a b
  else
    st

/-!
Passing a value to a function as a borrowed parameter doesn't count as a linear pass and thus values
can be happily passed through it.
-/

@[extern]
opaque State.remake (s : @& State) : State

/--
trace: [Compiler.result] size: 10
    def test3 st : State :=
      let st := State.remake st;
      cases st : State
      | State.mk abc xyz bool =>
        cases bool : State
        | Bool.false =>
          return st
        | Bool.true =>
          cases st : State
          | State.mk abc xyz bool =>
            let b := State.size st;
            let _x.1 := State.restore abc b st;
            return _x.1
-/
#guard_msgs in
def test3 : StateFn := fun st =>
  let a := st.abc
  let b := st.size
  let st := State.remake st
  if st.bool then
    st.restore a b
  else
    st

/-!
This also doesn't occur if there are indirect uses of a variable in both branches.
-/

/--
trace: [Compiler.result] size: 13
    def test4 st : State :=
      cases st : State
      | State.mk abc xyz bool =>
        let b := State.size st;
        let _x.1 := 1;
        let c := Nat.add b _x.1;
        cases bool : State
        | Bool.false =>
          let _x.2 := Nat.add abc _x.1;
          let _x.3 := 2;
          let _x.4 := Nat.add c _x.3;
          let _x.5 := State.restore _x.2 _x.4 st;
          return _x.5
        | Bool.true =>
          let _x.6 := State.restore abc c st;
          return _x.6
-/
#guard_msgs in
def test4 : StateFn := fun st =>
  let a := st.abc
  let b := st.size
  let c := b + 1
  if st.bool then
    st.restore a c
  else
    st.restore (a + 1) (c + 2)
