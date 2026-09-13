/-!
Tests for `reduceArity` issue #13355: support removing unused recursive arguments, even if they are
involved in (otherwise unused) computation.
-/

/--
trace: [Compiler.reduceArity] simple, used params: [n]
[Compiler.reduceArity] size: 11
    def simple._redArg n : Nat :=
      let zero := 0;
      let isZero := Nat.decEq n zero;
      cases isZero : Nat
      | Bool.true =>
        let _x.1 := 0;
        return _x.1
      | Bool.false =>
        let one := 1;
        let n.2 := Nat.sub n one;
        let _x.3 := 1;
        let _x.4 := simple._redArg n.2;
        let _x.5 := Nat.add _x.3 _x.4;
        return _x.5
[Compiler.reduceArity] size: 1
    def simple n p : Nat :=
      let _x.1 := simple._redArg n;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.reduceArity true in
def simple (n p : Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => 1 + simple n (n + p + p + n + p + n + p)

/--
trace: [Compiler.reduceArity] viaJp, used params: [n, c]
[Compiler.reduceArity] size: 16
    def viaJp._redArg n c : Nat :=
      let zero := 0;
      let isZero := Nat.decEq n zero;
      cases isZero : Nat
      | Bool.true =>
        let _x.1 := 0;
        return _x.1
      | Bool.false =>
        let one := 1;
        let n.2 := Nat.sub n one;
        jp _jp.3 : Nat :=
          let _x.4 := 1;
          let _x.5 := viaJp._redArg n.2 c;
          let _x.6 := Nat.add _x.4 _x.5;
          return _x.6;
        cases c : Nat
        | Bool.false =>
          goto _jp.3
        | Bool.true =>
          goto _jp.3
[Compiler.reduceArity] size: 1
    def viaJp n p c : Nat :=
      let _x.1 := viaJp._redArg n c;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.reduceArity true in
def viaJp (n p : Nat) (c : Bool) : Nat :=
  match n with
  | 0 => 0
  | m+1 =>
    let q := if c then p + 1 else p + 2
    1 + viaJp m q c

/--
trace: [Compiler.reduceArity] size: 16
    def viaJpUsed n p c : Nat :=
      let zero := 0;
      let isZero := Nat.decEq n zero;
      cases isZero : Nat
      | Bool.true =>
        return p
      | Bool.false =>
        let one := 1;
        let n.1 := Nat.sub n one;
        cases c : Nat
        | Bool.false =>
          let _x.2 := 2;
          let _x.3 := Nat.add p _x.2;
          let _x.4 := viaJpUsed n.1 _x.3 c;
          return _x.4
        | Bool.true =>
          let _x.5 := 1;
          let _x.6 := Nat.add p _x.5;
          let _x.7 := viaJpUsed n.1 _x.6 c;
          return _x.7
-/
#guard_msgs in
set_option trace.Compiler.reduceArity true in
def viaJpUsed (n p : Nat) (c : Bool) : Nat :=
  match n with
  | 0 => p
  | m+1 =>
    let q := if c then p + 1 else p + 2
    viaJpUsed m q c
