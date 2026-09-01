/-!
This test checks specialization of `dec` when the shape of the object is known.
-/


inductive A where
  | ctor1 (x : Nat × Nat)
  | ctor2 (y : Nat × Nat) (z : Nat × Nat)
  | ctor3

-- Force lookAtA to own the A
@[extern "foo"]
opaque foo (x : A) : Nat


/--
trace: [Compiler.explicitRc] size: 47
    def lookAtA x : tobj :=
      inc x;
      let v1 := foo x;
      cases x : tobj
      | A.ctor1 =>
        let x.1 := oproj[0] x;
        inc[ref] x.1;
        dec[ref][1 objs] x;
        let fst.2 := oproj[0] x.1;
        inc fst.2;
        let snd.3 := oproj[1] x.1;
        inc snd.3;
        dec[ref] x.1;
        let _x.4 := Nat.add v1 fst.2;
        dec fst.2;
        dec v1;
        let _x.5 := Nat.add _x.4 snd.3;
        dec snd.3;
        dec _x.4;
        return _x.5
      | A.ctor2 =>
        let y.6 := oproj[0] x;
        inc[ref] y.6;
        let z.7 := oproj[1] x;
        inc[ref] z.7;
        dec[ref][2 objs] x;
        let fst.8 := oproj[0] y.6;
        inc fst.8;
        let snd.9 := oproj[1] y.6;
        inc snd.9;
        dec[ref] y.6;
        let fst.10 := oproj[0] z.7;
        inc fst.10;
        let snd.11 := oproj[1] z.7;
        inc snd.11;
        dec[ref] z.7;
        let _x.12 := Nat.add v1 fst.8;
        dec fst.8;
        dec v1;
        let _x.13 := Nat.add _x.12 snd.9;
        dec snd.9;
        dec _x.12;
        let _x.14 := Nat.add _x.13 fst.10;
        dec fst.10;
        dec _x.13;
        let _x.15 := Nat.add _x.14 snd.11;
        dec snd.11;
        dec _x.14;
        return _x.15
      | A.ctor3 =>
        return v1
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def lookAtA (x : A) : Nat :=
  let v1 := foo x
  match x with
  | .ctor1 (x1, x2) => v1 + x1 + x2
  | .ctor2 (x1, x2) (y1, y2) => v1 + x1 + x2 + y1 + y2
  | .ctor3 => v1

