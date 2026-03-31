module

public section



/--
trace: [Compiler.explicitRc] size: 1
    def test1._closed_0 : obj :=
      let _x.1 := "";
      return _x.1
[Compiler.explicitRc] size: 7
    def test1 @&xs : obj :=
      let _x.1 := test1._closed_0;
      let _x.2 := 0;
      let _x.3 := Array.get!InternalBorrowed ◾ _x.1 xs _x.2;
      let _x.4 := 1;
      let _x.5 := Array.get!InternalBorrowed ◾ _x.1 xs _x.4;
      inc _x.3;
      let _x.6 := String.append _x.3 _x.5;
      return _x.6
[Compiler.explicitRc] size: 2
    def test1._boxed xs : obj :=
      let res := test1 xs;
      dec[ref] xs;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def test1 (xs : Array String) := xs[0]! ++ xs[1]!

/--
trace: [Compiler.explicitRc] size: 7
    def test2._redArg @&inst.1 @&xs f : tobj :=
      let _x.2 := 0;
      let _x.3 := Array.get!InternalBorrowed ◾ inst.1 xs _x.2;
      let _x.4 := 1;
      let _x.5 := Array.get!InternalBorrowed ◾ inst.1 xs _x.4;
      inc _x.5;
      inc _x.3;
      let _x.6 := f _x.3 _x.5;
      return _x.6
[Compiler.explicitRc] size: 3
    def test2._redArg._boxed inst.1 xs f : tobj :=
      let res := test2._redArg inst.1 xs f;
      dec[ref] xs;
      dec inst.1;
      return res
[Compiler.explicitRc] size: 1
    def test2 α @&inst.1 @&xs f : tobj :=
      let _x.2 := test2._redArg inst.1 xs f;
      return _x.2
[Compiler.explicitRc] size: 3
    def test2._boxed α inst.1 xs f : tobj :=
      let res := test2 α inst.1 xs f;
      dec[ref] xs;
      dec inst.1;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def test2 [Inhabited α] (xs : Array α) (f : α → α → α) := f xs[0]! xs[1]!

/--
trace: [Compiler.explicitRc] size: 4
    def test3._lam_0 @&xs i : UInt8 :=
      let _x.1 := USize.toNat i;
      let _x.2 := Array.size ◾ xs;
      let _x.3 := Nat.decLt _x.1 _x.2;
      dec _x.1;
      return _x.3
[Compiler.explicitRc] size: 5
    def test3._lam_0._boxed xs i : tagged :=
      let i.boxed := unbox i;
      dec i;
      let res := test3._lam_0 xs i.boxed;
      dec[ref] xs;
      let r := box res;
      return r
[Compiler.explicitRc] size: 21
    def test3 @&xs : obj :=
      let _x.1 := test1._closed_0;
      jp _jp.2 _y.3 : obj :=
        let _x.4 := 1;
        let _x.5 := test3._lam_0 xs _x.4;
        cases _x.5 : obj
        | Bool.false =>
          let _x.6 := outOfBounds._redArg _x.1;
          let _x.7 := String.append _y.3 _x.6;
          dec _x.6;
          return _x.7
        | Bool.true =>
          let _x.8 := Array.ugetBorrowed ◾ xs _x.4 ◾;
          let _x.9 := String.append _y.3 _x.8;
          return _x.9;
      let _x.10 := 0;
      let _x.11 := test3._lam_0 xs _x.10;
      cases _x.11 : obj
      | Bool.false =>
        let _x.12 := outOfBounds._redArg _x.1;
        goto _jp.2 _x.12
      | Bool.true =>
        let _x.13 := Array.ugetBorrowed ◾ xs _x.10 ◾;
        inc _x.13;
        goto _jp.2 _x.13
[Compiler.explicitRc] size: 2
    def test3._boxed xs : obj :=
      let res := test3 xs;
      dec[ref] xs;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def test3 (xs : Array String) := xs[(0 : USize)]! ++ xs[(1 : USize)]!


/--
trace: [Compiler.explicitRc] size: 4
    def test4._redArg._lam_0 @&xs i : UInt8 :=
      let _x.1 := USize.toNat i;
      let _x.2 := Array.size ◾ xs;
      let _x.3 := Nat.decLt _x.1 _x.2;
      dec _x.1;
      return _x.3
[Compiler.explicitRc] size: 5
    def test4._redArg._lam_0._boxed xs i : tagged :=
      let i.boxed := unbox i;
      dec i;
      let res := test4._redArg._lam_0 xs i.boxed;
      dec[ref] xs;
      let r := box res;
      return r
[Compiler.explicitRc] size: 20
    def test4._redArg @&inst.1 @&xs f : tobj :=
      jp _jp.2 _y.3 : tobj :=
        let _x.4 := 1;
        let _x.5 := test4._redArg._lam_0 xs _x.4;
        cases _x.5 : tobj
        | Bool.false =>
          let _x.6 := outOfBounds._redArg inst.1;
          let _x.7 := f _y.3 _x.6;
          return _x.7
        | Bool.true =>
          let _x.8 := Array.ugetBorrowed ◾ xs _x.4 ◾;
          inc _x.8;
          let _x.9 := f _y.3 _x.8;
          return _x.9;
      let _x.10 := 0;
      let _x.11 := test4._redArg._lam_0 xs _x.10;
      cases _x.11 : tobj
      | Bool.false =>
        let _x.12 := outOfBounds._redArg inst.1;
        goto _jp.2 _x.12
      | Bool.true =>
        let _x.13 := Array.ugetBorrowed ◾ xs _x.10 ◾;
        inc _x.13;
        goto _jp.2 _x.13
[Compiler.explicitRc] size: 3
    def test4._redArg._boxed inst.1 xs f : tobj :=
      let res := test4._redArg inst.1 xs f;
      dec[ref] xs;
      dec inst.1;
      return res
[Compiler.explicitRc] size: 1
    def test4 α @&inst.1 @&xs f : tobj :=
      let _x.2 := test4._redArg inst.1 xs f;
      return _x.2
[Compiler.explicitRc] size: 3
    def test4._boxed α inst.1 xs f : tobj :=
      let res := test4 α inst.1 xs f;
      dec[ref] xs;
      dec inst.1;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def test4 [Inhabited α] (xs : Array α) (f : α → α → α) := f xs[(0 : USize)]! xs[(1 : USize)]!
