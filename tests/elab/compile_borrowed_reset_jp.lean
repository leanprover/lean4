module

public section

/--
trace: [Compiler.explicitRc] size: 17
    def testWithAnnotation @&n @&p @&q : obj :=
      jp _jp.1 fst.2 @&snd.3 : obj :=
        let snd := oproj[1] snd.3;
        inc snd;
        let _x.4 := ctor_0[Prod.mk] fst.2 snd;
        return _x.4;
      let zero := 0;
      let isZero := Nat.decEq n zero;
      cases isZero : obj
      | Bool.true =>
        let _x.5 := 123;
        goto _jp.1 _x.5 p
      | Bool.false =>
        let one := 1;
        let n.6 := Nat.sub n one;
        let _x.7 := Nat.add n.6 one;
        let _x.8 := Nat.mul n.6 _x.7;
        dec _x.7;
        dec n.6;
        goto _jp.1 _x.8 q
[Compiler.explicitRc] size: 4
    def testWithAnnotation._boxed n p q : obj :=
      let res := testWithAnnotation n p q;
      dec q;
      dec p;
      dec n;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def testWithAnnotation (n : Nat) (p q : @&Prod Nat Nat) : Prod Nat Nat :=
  let (value, helper) :=
    match n with
    | 0 => (123, p)
    | n + 1 => (n * (n + 1), q)
  { helper with fst := value }


/--
trace: [Compiler.explicitRc] size: 20
    def testWithoutAnnotation @&n p q : obj :=
      jp _jp.1 fst.2 snd.3 : obj :=
        let snd := oproj[1] snd.3;
        inc snd;
        let _x.4 := reset[2] snd.3;
        let _x.5 := reuse _x.4 in ctor_0[Prod.mk] fst.2 snd;
        return _x.5;
      let zero := 0;
      let isZero := Nat.decEq n zero;
      cases isZero : obj
      | Bool.true =>
        dec q;
        let _x.6 := 123;
        goto _jp.1 _x.6 p
      | Bool.false =>
        dec p;
        let one := 1;
        let n.7 := Nat.sub n one;
        let _x.8 := Nat.add n.7 one;
        let _x.9 := Nat.mul n.7 _x.8;
        dec _x.8;
        dec n.7;
        goto _jp.1 _x.9 q
[Compiler.explicitRc] size: 2
    def testWithoutAnnotation._boxed n p q : obj :=
      let res := testWithoutAnnotation n p q;
      dec n;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def testWithoutAnnotation (n : Nat) (p q : Prod Nat Nat) : Prod Nat Nat :=
  let (value, helper) :=
    match n with
    | 0 => (123, p)
    | n + 1 => (n * (n + 1), q)
  { helper with fst := value }

/--
trace: [Compiler.inferBorrow] own _x.28: result of ctor call _x.28
[Compiler.inferBorrow] own _x.30: result of ctor call _x.30
[Compiler.inferBorrow] own n: argument to constructor call _x.30
[Compiler.inferBorrow] own _x.29: result of function call _x.29
[Compiler.inferBorrow] size: 2
    def testArrayWithAnnotation._closed_0 : obj :=
      let _x.1 := 0;
      let _x.2 := ctor_0[Prod.mk] _x.1 _x.1;
      return _x.2
[Compiler.inferBorrow] size: 4
    def testArrayWithAnnotation n @&ps : obj :=
      let _x.1 := testArrayWithAnnotation._closed_0;
      let pair := Array.get!Internal ◾ _x.1 ps n;
      let snd := oproj[1] pair;
      let _x.2 := ctor_0[Prod.mk] n snd;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.inferBorrow true in
def testArrayWithAnnotation (n : Nat) (ps : @&Array (Nat × Nat)) : Nat × Nat :=
  let pair := ps[n]!
  { pair with fst := n }

/--
trace: [Compiler.inferBorrow] own _x.28: used in reset reuse _x.28
[Compiler.inferBorrow] own _x.29: used in reset reuse _x.28
[Compiler.inferBorrow] own n: argument to constructor call _x.28
[Compiler.inferBorrow] own pair: used in reset reuse _x.29
[Compiler.inferBorrow] own snd: fwd projection propagation snd
[Compiler.inferBorrow] own _x.27: result of function call _x.27
[Compiler.inferBorrow] size: 5
    def testArrayWithoutAnnotation n @&ps : obj :=
      let _x.1 := testArrayWithAnnotation._closed_0;
      let pair := Array.get!Internal ◾ _x.1 ps n;
      let snd := oproj[1] pair;
      let _x.2 := reset[2] pair;
      let _x.3 := reuse _x.2 in ctor_0[Prod.mk] n snd;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.inferBorrow true in
def testArrayWithoutAnnotation (n : Nat) (ps : Array (Nat × Nat)) : Nat × Nat :=
  let pair := ps[n]!
  { pair with fst := n }

/--
warning: declaration uses `sorry`
---
trace: [Compiler.inferBorrow] own _x.11: result of ctor call _x.11
[Compiler.inferBorrow] own n: argument to constructor call _x.11
[Compiler.inferBorrow] size: 3
    def testArrayWithAnnotation' n @&ps : obj :=
      let pair := Array.getInternal ◾ ps n ◾;
      let snd := oproj[1] pair;
      let _x.1 := ctor_0[Prod.mk] n snd;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.inferBorrow true in
def testArrayWithAnnotation' (n : Nat) (ps : @&Array (Nat × Nat)) : Nat × Nat :=
  let pair := ps[n]'sorry
  { pair with fst := n }

/--
warning: declaration uses `sorry`
---
trace: [Compiler.inferBorrow] own _x.13: result of ctor call _x.13
[Compiler.inferBorrow] own _x.12: result of function call _x.12
[Compiler.inferBorrow] size: 4
    def testArrayWithAnnotation'' n @&ps : obj :=
      let pair := Array.uget ◾ ps n ◾;
      let snd := oproj[1] pair;
      let _x.1 := USize.toNat n;
      let _x.2 := ctor_0[Prod.mk] _x.1 snd;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.inferBorrow true in
def testArrayWithAnnotation'' (n : USize) (ps : @&Array (Nat × Nat)) : Nat × Nat :=
  let pair := ps[n]'sorry
  { pair with fst := n.toNat }
