

@[noinline] def g (x : Nat) : Nat × Nat := (x, x)
@[noinline] def p (x : Nat) : Bool := x > 10

set_option trace.Compiler.explicitRc true

/--
trace: [Compiler.explicitRc] size: 27
    def f x y : UInt8 :=
      jp _jp.1 x : UInt8 :=
        let _x.2 := p x;
        cases _x.2 : UInt8
        | Bool.false =>
          let _x.3 := 1;
          let _x.4 := Nat.add x _x.3;
          dec x;
          let _x.5 := p _x.4;
          dec _x.4;
          return _x.5
        | Bool.true =>
          dec x;
          return _x.2;
      let _x.6 := 0;
      let _x.7 := Nat.decEq x _x.6;
      cases _x.7 : UInt8
      | Bool.false =>
        dec y;
        let z := g x;
        let fst := proj[0] z;
        inc fst;
        dec z;
        goto _jp.1 fst
      | Bool.true =>
        dec x;
        let z := g y;
        let fst := proj[0] z;
        inc fst;
        dec z;
        goto _jp.1 fst
[Compiler.explicitRc] size: 2
    def f._boxed x y : tagged :=
      let res := f x y;
      let r := box res;
      return r
-/
#guard_msgs in
def f (x : Nat) (y : Nat) : Bool :=
let jp (x : Nat) : Bool := -- x must be owned
  p x || p (x+1)
match x with
| 0 => let z := g y; jp z.1
| _ => let z := g x; jp z.1

/--
trace: [Compiler.explicitRc] size: 2
    def h @&x : UInt8 :=
      let _x.1 := 5;
      let _x.2 := Nat.decLt _x.1 x;
      return _x.2
[Compiler.explicitRc] size: 3
    def h._boxed x : tagged :=
      let res := h x;
      dec x;
      let r := box res;
      return r
-/
#guard_msgs in
def h (x : Nat) : Bool := -- x must be borrowed
x > 5
