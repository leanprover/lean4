/-!
This tests controls the behavior of specialize with user annotations.
-/


/--
trace: [Compiler.specialize.info] List.foldrNonTR: preliminary: [[(N, false),
      (N, false),
      (H, true),
      (U, true),
      (O, false)]], fixed mask: [true, true, true, true, false]
[Compiler.specialize.info] List.foldrNonTR [N, N, H, FU, O]
-/
#guard_msgs in
set_option trace.Compiler.specialize.info true in
@[specialize f init]
def List.foldrNonTR (f : α → β → β) (init : β) : (l : List α) → β
  | []     => init
  | a :: l => f a (foldrNonTR f init l)

/--
trace: [Compiler.saveMono] size: 7
    def List.foldrNonTR._at_._example.spec_0 i kcontinue x.1 _y.2 : Nat :=
      cases x.1 : Nat
      | List.nil =>
        let _x.3 := kcontinue _y.2;
        return _x.3
      | List.cons head.4 tail.5 =>
        let _x.6 := Nat.add _y.2 i;
        let x := Nat.add _x.6 head.4;
        let _x.7 := List.foldrNonTR._at_._example.spec_0 i kcontinue tail.5 x;
        return _x.7
[Compiler.saveMono] size: 12
    def List.foldrNonTR._at_.List.foldrNonTR._at_._example.spec_1.spec_1 x.1 _y.2 : Nat :=
      cases x.1 : Nat
      | List.nil =>
        return _y.2
      | List.cons head.3 tail.4 =>
        let _x.5 := List.foldrNonTR._at_.List.foldrNonTR._at_._example.spec_1.spec_1 tail.4;
        let _x.6 := 2;
        let _x.7 := 3;
        let _x.8 := 4;
        let _x.9 := [] ◾;
        let _x.10 := List.cons ◾ _x.8 _x.9;
        let _x.11 := List.cons ◾ _x.7 _x.10;
        let _x.12 := List.cons ◾ _x.6 _x.11;
        let _x.13 := List.foldrNonTR._at_._example.spec_0 head.3 _x.5 _x.12 _y.2;
        return _x.13
[Compiler.saveMono] size: 12
    def List.foldrNonTR._at_._example.spec_1 x.1 _y.2 : Nat :=
      cases x.1 : Nat
      | List.nil =>
        return _y.2
      | List.cons head.3 tail.4 =>
        let _x.5 := List.foldrNonTR._at_.List.foldrNonTR._at_._example.spec_1.spec_1 tail.4;
        let _x.6 := 2;
        let _x.7 := 3;
        let _x.8 := 4;
        let _x.9 := [] ◾;
        let _x.10 := List.cons ◾ _x.8 _x.9;
        let _x.11 := List.cons ◾ _x.7 _x.10;
        let _x.12 := List.cons ◾ _x.6 _x.11;
        let _x.13 := List.foldrNonTR._at_._example.spec_0 head.3 _x.5 _x.12 _y.2;
        return _x.13
[Compiler.saveMono] size: 9
    def _example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := [] ◾;
      let _x.5 := List.cons ◾ _x.3 _x.4;
      let _x.6 := List.cons ◾ _x.2 _x.5;
      let _x.7 := List.cons ◾ _x.1 _x.6;
      let _x.8 := List.foldrNonTR._at_._example.spec_1 _x.7 x;
      return _x.8
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
example :=
  let x := 42;
  List.foldrNonTR (β := Nat → Id Nat)
    (fun i kcontinue s =>
      let x := s;
      List.foldrNonTR
        (fun j kcontinue s =>
          let x := s;
          let x := x + i + j;
          kcontinue x)
        kcontinue
        [2,3,4] x)
    pure
    [1, 2, 3] x
