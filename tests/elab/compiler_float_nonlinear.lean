/-!
Tests that `floatLetIn` does not float `let` declarations across a `cases` on `ST.Out`/`EST.Out`.
Doing so would move reads of a `ST.Ref` past writes to it and thus break linearity (issue #15086).
Floating into the arms of a pure `cases` must still happen.
-/

structure State where
  a : Nat
  b : Array Nat

abbrev M := StateRefT State IO

@[noinline]
def getState : M State := get

@[noinline]
def popBack : M Unit := modify fun s => { s with b := s.b.pop }

@[noinline]
def sideEffect : IO Unit := pure ()

@[noinline]
def testing (foo : Nat) : (Option Nat) :=
  if foo > 1 then
    some foo
  else
    none

/-! Both the read and the write are visible to the pass. -/

/--
trace: [Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] size: 20
    def test @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := instInhabitedNat;
      let _x.3 := @ST.Prim.Ref.get _ _ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        let _x.6 := val.4 # 1;
        let _x.7 := @Array.size _ _x.6;
        let _x.8 := 1;
        let _x.9 := Nat.sub _x.7 _x.8;
        let _x.10 := @Array.get!Internal _ _x.2 _x.6 _x.9;
        let _x.11 := @ST.Prim.Ref.take _ _ a state.5;
        cases _x.11 : EST.Out IO.Error lcAny Nat
        | ST.Out.mk val.12 state.13 =>
          let _x.14 := val.12 # 0;
          let _x.15 := val.12 # 1;
          let _x.16 := @Array.pop _ _x.15;
          let _x.17 := State.mk _x.14 _x.16;
          let _x.18 := @ST.Prim.Ref.put _ _ a _x.17 state.13;
          cases _x.18 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.19 state.20 =>
            let _x.21 := @EST.Out.ok _ _ _ _x.10 state.20;
            return _x.21
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] size: 21
    def test @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        cases val.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := @ST.Prim.Ref.take ◾ ◾ a state.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.11 state.12 =>
            cases val.11 : EST.Out IO.Error lcAny Nat
            | State.mk a b =>
              let _x.13 := Array.pop ◾ b;
              let _x.14 := State.mk a _x.13;
              let _x.15 := @ST.Prim.Ref.put ◾ ◾ a _x.14 state.12;
              cases _x.15 : EST.Out IO.Error lcAny Nat
              | ST.Out.mk val.16 state.17 =>
                let _x.18 := @EST.Out.ok ◾ ◾ ◾ _x.9 state.17;
                return _x.18
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] size: 21
    def test @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        cases val.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := @ST.Prim.Ref.take ◾ ◾ a state.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.11 state.12 =>
            cases val.11 : EST.Out IO.Error lcAny Nat
            | State.mk a b =>
              let _x.13 := Array.pop ◾ b;
              let _x.14 := State.mk a _x.13;
              let _x.15 := @ST.Prim.Ref.put ◾ ◾ a _x.14 state.12;
              cases _x.15 : EST.Out IO.Error lcAny Nat
              | ST.Out.mk val.16 state.17 =>
                let _x.18 := @EST.Out.ok ◾ ◾ ◾ _x.9 state.17;
                return _x.18
-/
#guard_msgs in
set_option trace.Compiler.floatLetIn true in
def test : M Nat := do
  let foo := (← get).b.back!
  modify fun s => { s with b := s.b.pop }
  return foo

/-! The read is hidden behind a `noinline` function. -/

/--
trace: [Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 22
    def testOpaqueGet @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := instInhabitedNat;
      let _x.3 := getState a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | EST.Out.ok a.4 a.5 =>
        let _x.6 := a.4 # 1;
        let _x.7 := @Array.size _ _x.6;
        let _x.8 := 1;
        let _x.9 := Nat.sub _x.7 _x.8;
        let _x.10 := @Array.get!Internal _ _x.2 _x.6 _x.9;
        let _x.11 := @ST.Prim.Ref.take _ _ a a.5;
        cases _x.11 : EST.Out IO.Error lcAny Nat
        | ST.Out.mk val.12 state.13 =>
          let _x.14 := val.12 # 0;
          let _x.15 := val.12 # 1;
          let _x.16 := @Array.pop _ _x.15;
          let _x.17 := State.mk _x.14 _x.16;
          let _x.18 := @ST.Prim.Ref.put _ _ a _x.17 state.13;
          cases _x.18 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.19 state.20 =>
            let _x.21 := @EST.Out.ok _ _ _ _x.10 state.20;
            return _x.21
      | EST.Out.error a.22 a.23 =>
        let _x.24 := @EST.Out.error _ _ _ a.22 a.23;
        return _x.24
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 23
    def testOpaqueGet @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := getState a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | EST.Out.ok a.4 a.5 =>
        cases a.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := @ST.Prim.Ref.take ◾ ◾ a a.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.11 state.12 =>
            cases val.11 : EST.Out IO.Error lcAny Nat
            | State.mk a b =>
              let _x.13 := Array.pop ◾ b;
              let _x.14 := State.mk a _x.13;
              let _x.15 := @ST.Prim.Ref.put ◾ ◾ a _x.14 state.12;
              cases _x.15 : EST.Out IO.Error lcAny Nat
              | ST.Out.mk val.16 state.17 =>
                let _x.18 := @EST.Out.ok ◾ ◾ ◾ _x.9 state.17;
                return _x.18
      | EST.Out.error a.19 a.20 =>
        let _x.21 := @EST.Out.error ◾ ◾ ◾ a.19 a.20;
        return _x.21
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 23
    def testOpaqueGet @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := getState a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | EST.Out.ok a.4 a.5 =>
        cases a.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := @ST.Prim.Ref.take ◾ ◾ a a.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.11 state.12 =>
            cases val.11 : EST.Out IO.Error lcAny Nat
            | State.mk a b =>
              let _x.13 := Array.pop ◾ b;
              let _x.14 := State.mk a _x.13;
              let _x.15 := @ST.Prim.Ref.put ◾ ◾ a _x.14 state.12;
              cases _x.15 : EST.Out IO.Error lcAny Nat
              | ST.Out.mk val.16 state.17 =>
                let _x.18 := @EST.Out.ok ◾ ◾ ◾ _x.9 state.17;
                return _x.18
      | EST.Out.error a.19 a.20 =>
        let _x.21 := @EST.Out.error ◾ ◾ ◾ a.19 a.20;
        return _x.21
-/
#guard_msgs in
set_option trace.Compiler.floatLetIn true in
def testOpaqueGet : M Nat := do
  let foo := (← getState).b.back!
  modify fun s => { s with b := s.b.pop }
  return foo

/-! The write is hidden behind a `noinline` function. -/

/--
trace: [Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 15
    def testOpaqueModify @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := instInhabitedNat;
      let _x.3 := @ST.Prim.Ref.get _ _ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        let _x.6 := val.4 # 1;
        let _x.7 := @Array.size _ _x.6;
        let _x.8 := 1;
        let _x.9 := Nat.sub _x.7 _x.8;
        let _x.10 := @Array.get!Internal _ _x.2 _x.6 _x.9;
        let _x.11 := popBack a state.5;
        cases _x.11 : EST.Out IO.Error lcAny Nat
        | EST.Out.ok a.12 a.13 =>
          let _x.14 := @EST.Out.ok _ _ _ _x.10 a.13;
          return _x.14
        | EST.Out.error a.15 a.16 =>
          let _x.17 := @EST.Out.error _ _ _ a.15 a.16;
          return _x.17
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 16
    def testOpaqueModify @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        cases val.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := popBack a state.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | EST.Out.ok a.11 a.12 =>
            let _x.13 := @EST.Out.ok ◾ ◾ ◾ _x.9 a.12;
            return _x.13
          | EST.Out.error a.14 a.15 =>
            let _x.16 := @EST.Out.error ◾ ◾ ◾ a.14 a.15;
            return _x.16
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 16
    def testOpaqueModify @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        cases val.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := popBack a state.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | EST.Out.ok a.11 a.12 =>
            let _x.13 := @EST.Out.ok ◾ ◾ ◾ _x.9 a.12;
            return _x.13
          | EST.Out.error a.14 a.15 =>
            let _x.16 := @EST.Out.error ◾ ◾ ◾ a.14 a.15;
            return _x.16
-/
#guard_msgs in
set_option trace.Compiler.floatLetIn true in
def testOpaqueModify : M Nat := do
  let foo := (← get).b.back!
  popBack
  return foo

/-! Both the read and the write are hidden behind `noinline` functions. -/

/--
trace: [Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 17
    def testOpaqueBoth @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := instInhabitedNat;
      let _x.3 := getState a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | EST.Out.ok a.4 a.5 =>
        let _x.6 := a.4 # 1;
        let _x.7 := @Array.size _ _x.6;
        let _x.8 := 1;
        let _x.9 := Nat.sub _x.7 _x.8;
        let _x.10 := @Array.get!Internal _ _x.2 _x.6 _x.9;
        let _x.11 := popBack a a.5;
        cases _x.11 : EST.Out IO.Error lcAny Nat
        | EST.Out.ok a.12 a.13 =>
          let _x.14 := @EST.Out.ok _ _ _ _x.10 a.13;
          return _x.14
        | EST.Out.error a.15 a.16 =>
          let _x.17 := @EST.Out.error _ _ _ a.15 a.16;
          return _x.17
      | EST.Out.error a.18 a.19 =>
        let _x.20 := @EST.Out.error _ _ _ a.18 a.19;
        return _x.20
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 18
    def testOpaqueBoth @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := getState a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | EST.Out.ok a.4 a.5 =>
        cases a.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := popBack a a.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | EST.Out.ok a.11 a.12 =>
            let _x.13 := @EST.Out.ok ◾ ◾ ◾ _x.9 a.12;
            return _x.13
          | EST.Out.error a.14 a.15 =>
            let _x.16 := @EST.Out.error ◾ ◾ ◾ a.14 a.15;
            return _x.16
      | EST.Out.error a.17 a.18 =>
        let _x.19 := @EST.Out.error ◾ ◾ ◾ a.17 a.18;
        return _x.19
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 18
    def testOpaqueBoth @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := getState a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | EST.Out.ok a.4 a.5 =>
        cases a.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := popBack a a.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | EST.Out.ok a.11 a.12 =>
            let _x.13 := @EST.Out.ok ◾ ◾ ◾ _x.9 a.12;
            return _x.13
          | EST.Out.error a.14 a.15 =>
            let _x.16 := @EST.Out.error ◾ ◾ ◾ a.14 a.15;
            return _x.16
      | EST.Out.error a.17 a.18 =>
        let _x.19 := @EST.Out.error ◾ ◾ ◾ a.17 a.18;
        return _x.19
-/
#guard_msgs in
set_option trace.Compiler.floatLetIn true in
def testOpaqueBoth : M Nat := do
  let foo := (← getState).b.back!
  popBack
  return foo

/-! An `IO` action that does not touch the reference blocks floating as well. -/

/--
trace: [Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 25
    def testIOInBetween @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := instInhabitedNat;
      let _x.3 := @ST.Prim.Ref.get _ _ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        let _x.6 := val.4 # 1;
        let _x.7 := @Array.size _ _x.6;
        let _x.8 := 1;
        let _x.9 := Nat.sub _x.7 _x.8;
        let _x.10 := @Array.get!Internal _ _x.2 _x.6 _x.9;
        let _x.11 := sideEffect state.5;
        cases _x.11 : EST.Out IO.Error lcAny Nat
        | EST.Out.ok a.12 a.13 =>
          let _x.14 := @ST.Prim.Ref.take _ _ a a.13;
          cases _x.14 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.15 state.16 =>
            let _x.17 := val.15 # 0;
            let _x.18 := val.15 # 1;
            let _x.19 := @Array.pop _ _x.18;
            let _x.20 := State.mk _x.17 _x.19;
            let _x.21 := @ST.Prim.Ref.put _ _ a _x.20 state.16;
            cases _x.21 : EST.Out IO.Error lcAny Nat
            | ST.Out.mk val.22 state.23 =>
              let _x.24 := @EST.Out.ok _ _ _ _x.10 state.23;
              return _x.24
        | EST.Out.error a.25 a.26 =>
          let _x.27 := @EST.Out.error _ _ _ a.25 a.26;
          return _x.27
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 26
    def testIOInBetween @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        cases val.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := sideEffect state.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | EST.Out.ok a.11 a.12 =>
            let _x.13 := @ST.Prim.Ref.take ◾ ◾ a a.12;
            cases _x.13 : EST.Out IO.Error lcAny Nat
            | ST.Out.mk val.14 state.15 =>
              cases val.14 : EST.Out IO.Error lcAny Nat
              | State.mk a b =>
                let _x.16 := Array.pop ◾ b;
                let _x.17 := State.mk a _x.16;
                let _x.18 := @ST.Prim.Ref.put ◾ ◾ a _x.17 state.15;
                cases _x.18 : EST.Out IO.Error lcAny Nat
                | ST.Out.mk val.19 state.20 =>
                  let _x.21 := @EST.Out.ok ◾ ◾ ◾ _x.9 state.20;
                  return _x.21
          | EST.Out.error a.22 a.23 =>
            let _x.24 := @EST.Out.error ◾ ◾ ◾ a.22 a.23;
            return _x.24
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.ok 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `EST.Out.error 0
[Compiler.floatLetIn] size: 26
    def testIOInBetween @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        cases val.4 : EST.Out IO.Error lcAny Nat
        | State.mk a b =>
          let _x.6 := Array.size ◾ b;
          let _x.7 := 1;
          let _x.8 := Nat.sub _x.6 _x.7;
          let _x.9 := Array.get!Internal ◾ _x.2 b _x.8;
          let _x.10 := sideEffect state.5;
          cases _x.10 : EST.Out IO.Error lcAny Nat
          | EST.Out.ok a.11 a.12 =>
            let _x.13 := @ST.Prim.Ref.take ◾ ◾ a a.12;
            cases _x.13 : EST.Out IO.Error lcAny Nat
            | ST.Out.mk val.14 state.15 =>
              cases val.14 : EST.Out IO.Error lcAny Nat
              | State.mk a b =>
                let _x.16 := Array.pop ◾ b;
                let _x.17 := State.mk a _x.16;
                let _x.18 := @ST.Prim.Ref.put ◾ ◾ a _x.17 state.15;
                cases _x.18 : EST.Out IO.Error lcAny Nat
                | ST.Out.mk val.19 state.20 =>
                  let _x.21 := @EST.Out.ok ◾ ◾ ◾ _x.9 state.20;
                  return _x.21
          | EST.Out.error a.22 a.23 =>
            let _x.24 := @EST.Out.error ◾ ◾ ◾ a.22 a.23;
            return _x.24
-/
#guard_msgs in
set_option trace.Compiler.floatLetIn true in
def testIOInBetween : M Nat := do
  let foo := (← get).b.back!
  sideEffect
  modify fun s => { s with b := s.b.pop }
  return foo

/-! Floating into the arms of a pure `cases` still happens in monadic code. -/

/--
trace: [Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.none 5
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.some 0
[Compiler.floatLetIn] size: 25
    def test' n @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := instInhabitedNat;
      let _x.3 := @ST.Prim.Ref.get _ _ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        let _x.6 := testing n;
        cases _x.6 : EST.Out IO.Error lcAny Nat
        | Option.none =>
          let _x.7 := val.4 # 1;
          let _x.8 := @Array.size _ _x.7;
          let _x.9 := 1;
          let _x.10 := Nat.sub _x.8 _x.9;
          let _x.11 := @Array.get!Internal _ _x.2 _x.7 _x.10;
          let _x.12 := @ST.Prim.Ref.take _ _ a state.5;
          cases _x.12 : EST.Out IO.Error lcAny Nat
          | ST.Out.mk val.13 state.14 =>
            let _x.15 := val.13 # 0;
            let _x.16 := val.13 # 1;
            let _x.17 := @Array.pop _ _x.16;
            let _x.18 := State.mk _x.15 _x.17;
            let _x.19 := @ST.Prim.Ref.put _ _ a _x.18 state.14;
            cases _x.19 : EST.Out IO.Error lcAny Nat
            | ST.Out.mk val.20 state.21 =>
              let _x.22 := @EST.Out.ok _ _ _ _x.11 state.21;
              return _x.22
        | Option.some val.23 =>
          let _x.24 := @EST.Out.ok _ _ _ val.23 state.5;
          return _x.24
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.none 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.some 0
[Compiler.floatLetIn] size: 26
    def test' n @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        let _x.6 := testing n;
        cases _x.6 : EST.Out IO.Error lcAny Nat
        | Option.none =>
          cases val.4 : EST.Out IO.Error lcAny Nat
          | State.mk a b =>
            let _x.7 := Array.size ◾ b;
            let _x.8 := 1;
            let _x.9 := Nat.sub _x.7 _x.8;
            let _x.10 := Array.get!Internal ◾ _x.2 b _x.9;
            let _x.11 := @ST.Prim.Ref.take ◾ ◾ a state.5;
            cases _x.11 : EST.Out IO.Error lcAny Nat
            | ST.Out.mk val.12 state.13 =>
              cases val.12 : EST.Out IO.Error lcAny Nat
              | State.mk a b =>
                let _x.14 := Array.pop ◾ b;
                let _x.15 := State.mk a _x.14;
                let _x.16 := @ST.Prim.Ref.put ◾ ◾ a _x.15 state.13;
                cases _x.16 : EST.Out IO.Error lcAny Nat
                | ST.Out.mk val.17 state.18 =>
                  let _x.19 := @EST.Out.ok ◾ ◾ ◾ _x.10 state.18;
                  return _x.19
        | Option.some val.20 =>
          let _x.21 := @EST.Out.ok ◾ ◾ ◾ val.20 state.5;
          return _x.21
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.none 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `State.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `ST.Out.mk 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.some 0
[Compiler.floatLetIn] size: 26
    def test' n @&a a.1 : EST.Out IO.Error lcAny Nat :=
      let _x.2 := 0;
      let _x.3 := @ST.Prim.Ref.get ◾ ◾ a a.1;
      cases _x.3 : EST.Out IO.Error lcAny Nat
      | ST.Out.mk val.4 state.5 =>
        let _x.6 := testing n;
        cases _x.6 : EST.Out IO.Error lcAny Nat
        | Option.none =>
          cases val.4 : EST.Out IO.Error lcAny Nat
          | State.mk a b =>
            let _x.7 := Array.size ◾ b;
            let _x.8 := 1;
            let _x.9 := Nat.sub _x.7 _x.8;
            let _x.10 := Array.get!Internal ◾ _x.2 b _x.9;
            let _x.11 := @ST.Prim.Ref.take ◾ ◾ a state.5;
            cases _x.11 : EST.Out IO.Error lcAny Nat
            | ST.Out.mk val.12 state.13 =>
              cases val.12 : EST.Out IO.Error lcAny Nat
              | State.mk a b =>
                let _x.14 := Array.pop ◾ b;
                let _x.15 := State.mk a _x.14;
                let _x.16 := @ST.Prim.Ref.put ◾ ◾ a _x.15 state.13;
                cases _x.16 : EST.Out IO.Error lcAny Nat
                | ST.Out.mk val.17 state.18 =>
                  let _x.19 := @EST.Out.ok ◾ ◾ ◾ _x.10 state.18;
                  return _x.19
        | Option.some val.20 =>
          let _x.21 := @EST.Out.ok ◾ ◾ ◾ val.20 state.5;
          return _x.21
-/
#guard_msgs in
set_option trace.Compiler.floatLetIn true in
def test' (n : Nat) : M Nat := do
  let foo := (← get).b.back!
  let res := testing n
  match res with
  | some res => return res
  | none =>
    modify fun s => { s with b := s.b.pop }
    return foo

/-! ... and in pure code. -/

/--
trace: [Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.none 4
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.some 0
[Compiler.floatLetIn] size: 9
    def testPureMatch n xs : Nat :=
      let _x.1 := instInhabitedNat;
      let _x.2 := testing n;
      cases _x.2 : Nat
      | Option.none =>
        let _x.3 := @Array.size _ xs;
        let _x.4 := 1;
        let _x.5 := Nat.sub _x.3 _x.4;
        let foo := @Array.get!Internal _ _x.1 xs _x.5;
        return foo
      | Option.some val.6 =>
        return val.6
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.none 1
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.some 0
[Compiler.floatLetIn] size: 9
    def testPureMatch n xs : Nat :=
      let _x.1 := testing n;
      cases _x.1 : Nat
      | Option.none =>
        let _x.2 := 0;
        let _x.3 := Array.size ◾ xs;
        let _x.4 := 1;
        let _x.5 := Nat.sub _x.3 _x.4;
        let foo := Array.get!Internal ◾ _x.2 xs _x.5;
        return foo
      | Option.some val.6 =>
        return val.6
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.none 0
[Compiler.floatLetIn] Size of code that was pushed into arm: Lean.Compiler.LCNF.FloatLetIn.Decision.arm `Option.some 0
[Compiler.floatLetIn] size: 9
    def testPureMatch n xs : Nat :=
      let _x.1 := testing n;
      cases _x.1 : Nat
      | Option.none =>
        let _x.2 := 0;
        let _x.3 := Array.size ◾ xs;
        let _x.4 := 1;
        let _x.5 := Nat.sub _x.3 _x.4;
        let foo := Array.get!Internal ◾ _x.2 xs _x.5;
        return foo
      | Option.some val.6 =>
        return val.6
-/
#guard_msgs in
set_option trace.Compiler.floatLetIn true in
def testPureMatch (n : Nat) (xs : Array Nat) : Nat :=
  let foo := xs.back!
  match testing n with
  | some res => res
  | none => foo
