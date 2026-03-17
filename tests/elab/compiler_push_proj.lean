/-! This does some basic unit tests for the pushProj pass in LCNF  -/


/--
trace: [Compiler.pushProj] size: 5
    def test1 a : tobj :=
      cases a : tobj
      | Option.none =>
        let _x.1 : tagged := 0;
        return _x.1
      | Option.some =>
        let val.2 : tobj := oproj[0] a;
        return val.2
[Compiler.pushProj] size: 6
    def test1 @&a : tobj :=
      cases a : tobj
      | Option.none =>
        let _x.1 : tagged := 0;
        return _x.1
      | Option.some =>
        let val.2 : tobj := oproj[0] a;
        inc val.2;
        return val.2
[Compiler.pushProj] size: 2
    def test1._boxed a : tobj :=
      let res : tobj := test1 a;
      dec a;
      return res
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
          let val.1 : tobj := oproj[0] a;
          let val.2 : tobj := oproj[0] b;
          let _x.3 : tobj := Nat.add val.1 val.2;
          let _x.4 : obj := ctor_1[Option.some] _x.3;
          return _x.4
[Compiler.pushProj] size: 27
    def test2 @&a b : tobj :=
      cases a : tobj
      | Option.none =>
        dec b;
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          inc a;
          return a
        | Option.some =>
          let val.1 : tobj := oproj[0] a;
          let val.2 : tobj := oproj[0] b;
          jp resetjp.3 _x.4 isShared.5 : tobj :=
            let _x.6 : tobj := Nat.add val.1 val.2;
            dec val.2;
            jp reusejp.7 _x.8 : tobj :=
              return _x.8;
            cases isShared.5 : tobj
            | Bool.false =>
              oset _x.4 [0] := _x.6;
              goto reusejp.7 _x.4
            | Bool.true =>
              let reuseFailAlloc.9 : obj := ctor_1[Option.some] _x.6;
              goto reusejp.7 reuseFailAlloc.9;
          let isSharedCheck.10 : UInt8 := isShared b;
          cases isSharedCheck.10 : tobj
          | Bool.false =>
            goto resetjp.3 b isSharedCheck.10
          | Bool.true =>
            inc val.2;
            dec b;
            goto resetjp.3 ◾ isSharedCheck.10
[Compiler.pushProj] size: 2
    def test2._boxed a b : tobj :=
      let res : tobj := test2 a b;
      dec a;
      return res
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
          let val.1 : tobj := oproj[0] a;
          let _x.2 : tagged := 1;
          let _x.3 : tobj := Nat.add val.1 _x.2;
          let _x.4 : obj := ctor_1[Option.some] _x.3;
          return _x.4
        | Option.some =>
          let val.5 : tobj := oproj[0] a;
          let val.6 : tobj := oproj[0] b;
          let _x.7 : tobj := Nat.add val.5 val.6;
          let _x.8 : obj := ctor_1[Option.some] _x.7;
          return _x.8
[Compiler.pushProj] size: 48
    def test3 a b : tobj :=
      cases a : tobj
      | Option.none =>
        dec b;
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := oproj[0] a;
          jp resetjp.2 _x.3 isShared.4 : tobj :=
            let _x.5 : tagged := 1;
            let _x.6 : tobj := Nat.add val.1 _x.5;
            dec val.1;
            jp reusejp.7 _x.8 : tobj :=
              return _x.8;
            cases isShared.4 : tobj
            | Bool.false =>
              oset _x.3 [0] := _x.6;
              goto reusejp.7 _x.3
            | Bool.true =>
              let reuseFailAlloc.9 : obj := ctor_1[Option.some] _x.6;
              goto reusejp.7 reuseFailAlloc.9;
          let isSharedCheck.10 : UInt8 := isShared a;
          cases isSharedCheck.10 : tobj
          | Bool.false =>
            goto resetjp.2 a isSharedCheck.10
          | Bool.true =>
            inc val.1;
            dec a;
            goto resetjp.2 ◾ isSharedCheck.10
        | Option.some =>
          let val.11 : tobj := oproj[0] a;
          inc val.11;
          dec a;
          let val.12 : tobj := oproj[0] b;
          jp resetjp.13 _x.14 isShared.15 : tobj :=
            let _x.16 : tobj := Nat.add val.11 val.12;
            dec val.12;
            dec val.11;
            jp reusejp.17 _x.18 : tobj :=
              return _x.18;
            cases isShared.15 : tobj
            | Bool.false =>
              oset _x.14 [0] := _x.16;
              goto reusejp.17 _x.14
            | Bool.true =>
              let reuseFailAlloc.19 : obj := ctor_1[Option.some] _x.16;
              goto reusejp.17 reuseFailAlloc.19;
          let isSharedCheck.20 : UInt8 := isShared b;
          cases isSharedCheck.20 : tobj
          | Bool.false =>
            goto resetjp.13 b isSharedCheck.20
          | Bool.true =>
            inc val.12;
            dec b;
            goto resetjp.13 ◾ isSharedCheck.20
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
          let val.1 : tobj := oproj[0] a;
          let _x.2 : tagged := 1;
          let _x.3 : tobj := Nat.add val.1 _x.2;
          let _x.4 : obj := ctor_1[Option.some] _x.3;
          return _x.4
        | Option.some =>
          cases c : tobj
          | Bool.false =>
            let _x.5 : tagged := ctor_0[Option.none];
            return _x.5
          | Bool.true =>
            let val.6 : tobj := oproj[0] a;
            let val.7 : tobj := oproj[0] b;
            let _x.8 : tobj := Nat.add val.6 val.7;
            let _x.9 : obj := ctor_1[Option.some] _x.8;
            return _x.9
[Compiler.pushProj] size: 54
    def test4 a b c : tobj :=
      cases a : tobj
      | Option.none =>
        dec b;
        return a
      | Option.some =>
        cases b : tobj
        | Option.none =>
          let val.1 : tobj := oproj[0] a;
          jp resetjp.2 _x.3 isShared.4 : tobj :=
            let _x.5 : tagged := 1;
            let _x.6 : tobj := Nat.add val.1 _x.5;
            dec val.1;
            jp reusejp.7 _x.8 : tobj :=
              return _x.8;
            cases isShared.4 : tobj
            | Bool.false =>
              oset _x.3 [0] := _x.6;
              goto reusejp.7 _x.3
            | Bool.true =>
              let reuseFailAlloc.9 : obj := ctor_1[Option.some] _x.6;
              goto reusejp.7 reuseFailAlloc.9;
          let isSharedCheck.10 : UInt8 := isShared a;
          cases isSharedCheck.10 : tobj
          | Bool.false =>
            goto resetjp.2 a isSharedCheck.10
          | Bool.true =>
            inc val.1;
            dec a;
            goto resetjp.2 ◾ isSharedCheck.10
        | Option.some =>
          cases c : tobj
          | Bool.false =>
            dec b;
            dec a;
            let _x.11 : tagged := ctor_0[Option.none];
            return _x.11
          | Bool.true =>
            let val.12 : tobj := oproj[0] a;
            inc val.12;
            dec a;
            let val.13 : tobj := oproj[0] b;
            jp resetjp.14 _x.15 isShared.16 : tobj :=
              let _x.17 : tobj := Nat.add val.12 val.13;
              dec val.13;
              dec val.12;
              jp reusejp.18 _x.19 : tobj :=
                return _x.19;
              cases isShared.16 : tobj
              | Bool.false =>
                oset _x.15 [0] := _x.17;
                goto reusejp.18 _x.15
              | Bool.true =>
                let reuseFailAlloc.20 : obj := ctor_1[Option.some] _x.17;
                goto reusejp.18 reuseFailAlloc.20;
            let isSharedCheck.21 : UInt8 := isShared b;
            cases isSharedCheck.21 : tobj
            | Bool.false =>
              goto resetjp.14 b isSharedCheck.21
            | Bool.true =>
              inc val.13;
              dec b;
              goto resetjp.14 ◾ isSharedCheck.21
[Compiler.pushProj] size: 2
    def test4._boxed a b c : tobj :=
      let c.boxed : UInt8 := unbox c;
      let res : tobj := test4 a b c.boxed;
      return res
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

