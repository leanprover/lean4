/-! This does some basic unit tests for the pushProj pass in LCNF  -/


/--
trace: [Compiler.pushProj] size: 5
    def test1 a : tobj :=
      cases a : tobj
      | Option.none =>
        let _x.1 : tagged := 0;
        return _x.1
      | Option.some =>
        let val.2 : tobj := proj[0] a;
        return val.2
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test1 (a : Option Nat) : Nat :=
  match a with
  | some a => a
  | none => 0


/--
trace: [Compiler.pushProj] size: 10
    def test2 a b : tobj :=
      cases a : tobj
      | Option.none =>
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          return a
        | Option.some =>
          let val.1 : tobj := proj[0] a;
          let val.2 : tobj := proj[0] b;
          let _x.3 : tobj := Nat.add val.1 val.2;
          let _x.4 : obj := ctor_1[Option.some]  _x.3;
          return _x.4
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test2 (a b : Option Nat) : Option Nat :=
  match a with
  | some a =>
    match b with
    | some b => some (a + b)
    | none => some a
  | none => none

/--
trace: [Compiler.pushProj] size: 14
    def test3 a b : tobj :=
      cases a : tobj
      | Option.none =>
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := proj[0] a;
          let _x.2 : tagged := 1;
          let _x.3 : tobj := Nat.add val.1 _x.2;
          let _x.4 : obj := ctor_1[Option.some]  _x.3;
          return _x.4
        | Option.some =>
          let val.5 : tobj := proj[0] a;
          let val.6 : tobj := proj[0] b;
          let _x.7 : tobj := Nat.add val.5 val.6;
          let _x.8 : obj := ctor_1[Option.some]  _x.7;
          return _x.8
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test3 (a b : Option Nat) : Option Nat :=
  match a with
  | some a =>
    match b with
    | some b => some (a + b)
    | none => some (a + 1)
  | none => none

/--
trace: [Compiler.pushProj] size: 18
    def test4 a b c : tobj :=
      cases a : tobj
      | Option.none =>
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := proj[0] a;
          let _x.2 : tagged := 1;
          let _x.3 : tobj := Nat.add val.1 _x.2;
          let _x.4 : obj := ctor_1[Option.some]  _x.3;
          return _x.4
        | Option.some =>
          cases c : tobj
          | Bool.false =>
            let _x.5 : tagged := ctor_0[Option.none] ;
            return _x.5
          | Bool.true =>
            let val.6 : tobj := proj[0] a;
            let val.7 : tobj := proj[0] b;
            let _x.8 : tobj := Nat.add val.6 val.7;
            let _x.9 : obj := ctor_1[Option.some]  _x.8;
            return _x.9
-/
#guard_msgs in
set_option pp.letVarTypes true in
set_option trace.Compiler.pushProj true in
def test4 (a b : Option Nat) (c : Bool) : Option Nat :=
  match a with
  | some a =>
    match b with
    | some b =>
      match c with
      | true => some (a + b)
      | false => none
    | none => some (a + 1)
  | none => none

