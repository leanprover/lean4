import Std.Do.Triple.SpecLemmas

@[specialize, expose]
def List.newForIn (l : List α) (b : β) (kcons : α → (β → γ) → β → γ) (knil : β → γ) : γ :=
  match l with
  | []     => knil b
  | a :: l => kcons a (l.newForIn · kcons knil) b

/--
trace: [Compiler.saveMono] size: 7
    def List.newForIn._at_.List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing.spec_1.spec_2.spec_2 i _x.1 tail.2 l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.3 := List.newForIn._at_.testing.spec_1 _x.1 tail.2 b;
        return _x.3
      | List.cons head.4 tail.5 =>
        let _x.6 := Nat.add b i;
        let x := Nat.add _x.6 head.4;
        let _x.7 := List.newForIn._at_.List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing.spec_1.spec_2.spec_2 i _x.1 tail.2 tail.5 x;
        return _x.7
[Compiler.saveMono] size: 7
    def List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing.spec_1.spec_2 _x.1 tail.2 i l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.3 := List.newForIn._at_.testing.spec_1 _x.1 tail.2 b;
        return _x.3
      | List.cons head.4 tail.5 =>
        let _x.6 := Nat.add b i;
        let x := Nat.add _x.6 head.4;
        let _x.7 := List.newForIn._at_.List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing.spec_1.spec_2.spec_2 i _x.1 tail.2 tail.5 x;
        return _x.7
[Compiler.saveMono] size: 12
    def List.newForIn._at_.testing.spec_1 _x.1 l b : Nat :=
      cases l : Nat
      | List.nil =>
        return b
      | List.cons head.2 tail.3 =>
        let _x.4 := 10;
        let _x.5 := Nat.sub _x.4 head.2;
        let _x.6 := Nat.add _x.5 _x.1;
        let _x.7 := 1;
        let _x.8 := Nat.sub _x.6 _x.7;
        let _x.9 := Nat.add head.2 _x.8;
        let _x.10 := [] ◾;
        let _x.11 := List.range'TR.go _x.1 _x.8 _x.9 _x.10;
        let _x.12 := List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing.spec_1.spec_2 _x.1 tail.3 head.2 _x.11 b;
        return _x.12
[Compiler.saveMono] size: 9
    def testing : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := [] ◾;
      let _x.5 := List.cons ◾ _x.3 _x.4;
      let _x.6 := List.cons ◾ _x.2 _x.5;
      let _x.7 := List.cons ◾ _x.1 _x.6;
      let _x.8 := List.newForIn._at_.testing.spec_1 _x.1 _x.7 x;
      return _x.8
[Compiler.saveMono] size: 7
    def List.newForIn._at_.testing.spec_0 i kcontinue l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.1 := kcontinue b;
        return _x.1
      | List.cons head.2 tail.3 =>
        let _x.4 := Nat.add b i;
        let x := Nat.add _x.4 head.2;
        let _x.5 := List.newForIn._at_.testing.spec_0 i kcontinue tail.3 x;
        return _x.5
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def testing :=
  let x := 42;
  List.newForIn (β := Nat) (γ := Id Nat)
    [1,2,3]
    x
    (fun i kcontinue s =>
      let x := s;
      List.newForIn
        [i:10].toList x
        (fun j kcontinue s =>
          let x := s;
          let x := x + i + j;
          kcontinue x)
        kcontinue)
    pure


/--
trace: [Compiler.saveMono] size: 7
    def List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing2.spec_0.spec_1 _x.1 tail.2 i l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.3 := List.newForIn._at_.testing2.spec_0 _x.1 tail.2 b;
        return _x.3
      | List.cons head.4 tail.5 =>
        let _x.6 := Nat.add b i;
        let x := Nat.add _x.6 head.4;
        let _x.7 := List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing2.spec_0.spec_1 _x.1 tail.2 i tail.5 x;
        return _x.7
[Compiler.saveMono] size: 14
    def List.newForIn._at_.testing2.spec_0 _x.1 l b : Nat :=
      cases l : Nat
      | List.nil =>
        return b
      | List.cons head.2 tail.3 =>
        let _x.4 := 37;
        let x := Nat.add b _x.4;
        let _x.5 := 10;
        let _x.6 := Nat.sub _x.5 head.2;
        let _x.7 := Nat.add _x.6 _x.1;
        let _x.8 := 1;
        let _x.9 := Nat.sub _x.7 _x.8;
        let _x.10 := Nat.add head.2 _x.9;
        let _x.11 := [] ◾;
        let _x.12 := List.range'TR.go _x.1 _x.9 _x.10 _x.11;
        let _x.13 := List.newForIn._at_.testing.spec_0._at_.List.newForIn._at_.testing2.spec_0.spec_1 _x.1 tail.3 head.2 _x.12 x;
        return _x.13
[Compiler.saveMono] size: 9
    def testing2 : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := [] ◾;
      let _x.5 := List.cons ◾ _x.3 _x.4;
      let _x.6 := List.cons ◾ _x.2 _x.5;
      let _x.7 := List.cons ◾ _x.1 _x.6;
      let _x.8 := List.newForIn._at_.testing2.spec_0 _x.1 _x.7 x;
      return _x.8
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def testing2 :=
  let x := 42;
  List.newForIn (β := Nat) (γ := Id Nat)
    [1,2,3]
    x
    (fun i kcontinue s =>
      -- difference to testing1 here
      let x := s + 37;
      List.newForIn
        [i:10].toList x
        (fun j kcontinue s =>
          let x := s;
          let x := x + i + j;
          kcontinue x)
        kcontinue)
    pure

/--
trace: [Compiler.saveMono] size: 9
    def List.newForIn._at_.List.newForIn._at_.testing3.spec_0._at_.List.newForIn._at_.testing3.spec_1.spec_2.spec_2 s i _x.1 tail.2 l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.3 := List.newForIn._at_.testing3.spec_1 _x.1 tail.2 b;
        return _x.3
      | List.cons head.4 tail.5 =>
        let _x.6 := Nat.add b b;
        let x := Nat.add _x.6 s;
        let _x.7 := Nat.add x i;
        let x := Nat.add _x.7 head.4;
        let _x.8 := List.newForIn._at_.List.newForIn._at_.testing3.spec_0._at_.List.newForIn._at_.testing3.spec_1.spec_2.spec_2 s i _x.1 tail.2 tail.5 x;
        return _x.8
[Compiler.saveMono] size: 9
    def List.newForIn._at_.testing3.spec_0._at_.List.newForIn._at_.testing3.spec_1.spec_2 _x.1 tail.2 s i l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.3 := List.newForIn._at_.testing3.spec_1 _x.1 tail.2 b;
        return _x.3
      | List.cons head.4 tail.5 =>
        let _x.6 := Nat.add b b;
        let x := Nat.add _x.6 s;
        let _x.7 := Nat.add x i;
        let x := Nat.add _x.7 head.4;
        let _x.8 := List.newForIn._at_.List.newForIn._at_.testing3.spec_0._at_.List.newForIn._at_.testing3.spec_1.spec_2.spec_2 s i _x.1 tail.2 tail.5 x;
        return _x.8
[Compiler.saveMono] size: 12
    def List.newForIn._at_.testing3.spec_1 _x.1 l b : Nat :=
      cases l : Nat
      | List.nil =>
        return b
      | List.cons head.2 tail.3 =>
        let _x.4 := 10;
        let _x.5 := Nat.sub _x.4 head.2;
        let _x.6 := Nat.add _x.5 _x.1;
        let _x.7 := 1;
        let _x.8 := Nat.sub _x.6 _x.7;
        let _x.9 := Nat.add head.2 _x.8;
        let _x.10 := [] ◾;
        let _x.11 := List.range'TR.go _x.1 _x.8 _x.9 _x.10;
        let _x.12 := List.newForIn._at_.testing3.spec_0._at_.List.newForIn._at_.testing3.spec_1.spec_2 _x.1 tail.3 b head.2 _x.11 b;
        return _x.12
[Compiler.saveMono] size: 9
    def testing3 : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := [] ◾;
      let _x.5 := List.cons ◾ _x.3 _x.4;
      let _x.6 := List.cons ◾ _x.2 _x.5;
      let _x.7 := List.cons ◾ _x.1 _x.6;
      let _x.8 := List.newForIn._at_.testing3.spec_1 _x.1 _x.7 x;
      return _x.8
[Compiler.saveMono] size: 9
    def List.newForIn._at_.testing3.spec_0 s i kcontinue l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.1 := kcontinue b;
        return _x.1
      | List.cons head.2 tail.3 =>
        let _x.4 := Nat.add b b;
        let x := Nat.add _x.4 s;
        let _x.5 := Nat.add x i;
        let x := Nat.add _x.5 head.2;
        let _x.6 := List.newForIn._at_.testing3.spec_0 s i kcontinue tail.3 x;
        return _x.6
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def testing3 :=
  let x := 42;
  List.newForIn (β := Nat) (γ := Id Nat)
    [1,2,3]
    x
    (fun i kcontinue s =>
      let x := s;
      List.newForIn
        [i:10].toList x
        (fun j kcontinue s =>
          -- difference to testing1 here
          let x := s + s + x;
          let x := x + i + j;
          kcontinue x)
        kcontinue)
    pure
