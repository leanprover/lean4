@[specialize]
def foo {α} : Nat → (α → α) → α → α
  | 0, f => f
  | n+1, f => foo n f

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 5
    def foo._at_._example.spec_0 x.1 : Nat :=
      cases x.1 : Nat
      | Nat.zero =>
        let _x.2 := 6;
        return _x.2
      | Nat.succ n.3 =>
        let _x.4 := foo._at_._example.spec_0 n.3;
        return _x.4
[Compiler.saveBase] size: 1
    def _example n : Nat :=
      let _x.1 := foo._at_._example.spec_0 n;
      return _x.1
-/
#guard_msgs in
example {n} := foo n (· + 1) 5

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 9
    def foo._at_._example.spec_0 x.1 : Nat :=
      fun _f.2 x.3 : Nat :=
        let _x.4 := 1;
        let _x.5 := Nat.add x.3 _x.4;
        return _x.5;
      let _x.6 := 5;
      cases x.1 : Nat
      | Nat.zero =>
        let _x.7 := _f.2 _x.6;
        let _x.8 := _f.2 _x.7;
        return _x.8
      | Nat.succ n.9 =>
        let _x.10 := foo._at_._example.spec_0 n.9;
        return _x.10
[Compiler.saveBase] size: 1
    def _example n : Nat :=
      let _x.1 := foo._at_._example.spec_0 n;
      return _x.1
-/
#guard_msgs in
example {n} := foo n (fun f a => f (f a)) (· + 1) 5

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 5
    def foo._at_._example.spec_0 x.1 : Nat :=
      let _x.2 := 5;
      cases x.1 : Nat
      | Nat.zero =>
        return _x.2
      | Nat.succ n.3 =>
        let _x.4 := foo._at_._example.spec_0 n.3;
        return _x.4
[Compiler.saveBase] size: 1
    def _example n : Nat :=
      let _x.1 := foo._at_._example.spec_0 n;
      return _x.1
-/
#guard_msgs in
example {n} := foo n id id id id id id 5

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 9
    def foo._at_._example.spec_0 x.1 : Nat :=
      fun _f.2 f g : Nat :=
        let _x.3 := f g;
        let _x.4 := f _x.3;
        return _x.4;
      fun _f.5 _y.6 : Nat :=
        return _y.6;
      let _x.7 := 5;
      cases x.1 : Nat
      | Nat.zero =>
        let _x.8 := _f.2 _f.5;
        let _x.9 := _f.2 _x.8 _x.7;
        return _x.9
      | Nat.succ n.10 =>
        let _x.11 := foo._at_._example.spec_0 n.10;
        return _x.11
[Compiler.saveBase] size: 1
    def _example n : Nat :=
      let _x.1 := foo._at_._example.spec_0 n;
      return _x.1
-/
#guard_msgs in
example {n} := foo n (fun f g => f <| f g) (fun f g => f <| f g) id 5

@[specialize]
def List.forBreak_ {α : Type u} {m : Type w → Type x} [Monad m] (xs : List α) (body : α → ExceptCpsT PUnit m PUnit) : m PUnit :=
  match xs with
  | [] => pure ⟨⟩
  | x :: xs => body x (fun _ => forBreak_ xs body) (fun _ => pure ⟨⟩)

-- This one still does not properly specialize for the success and error continuations
-- (`_y.4`, `_y.5`). The reason is that the loop body is not yet inlined when the specializer looks
-- at the recursive call site in `List.forBreak_._at_._example.spec_0`, so it allocates another,
-- strictly less general specialization `…spec_0.spec_0`.
-- The reason the loop body is not yet inlined is that it occurs in the recursive call site as well,
-- but only pre-specialization.
set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 23
    def List.forBreak_._at_.List.forBreak_._at_._example.spec_0.spec_0 _x.1 _y.2 _y.3 _y.4 _y.5 xs : _y.3 :=
      cases xs : _y.3
      | List.nil =>
        let _x.6 := PUnit.unit;
        let _x.7 := @Prod.mk _ _ _x.6 _y.2;
        let _x.8 := _y.4 _x.7;
        return _x.8
      | List.cons head.9 tail.10 =>
        let _x.11 := 0;
        let _x.12 := instDecidableEqNat _y.2 _x.11;
        cases _x.12 : _y.3
        | Decidable.isFalse x.13 =>
          let _x.14 := 10;
          let _x.15 := Nat.decLt _x.14 _y.2;
          cases _x.15 : _y.3
          | Decidable.isFalse x.16 =>
            let _x.17 := Nat.add _y.2 head.9;
            let _x.18 := List.forBreak_._at_.List.forBreak_._at_._example.spec_0.spec_0 _x.1 _x.17 _y.3 _y.4 _y.5 tail.10;
            return _x.18
          | Decidable.isTrue x.19 =>
            let _x.20 := Nat.add _y.2 _x.1;
            let _x.21 := PUnit.unit;
            let _x.22 := @Prod.mk _ _ _x.21 _x.20;
            let _x.23 := _y.4 _x.22;
            return _x.23
        | Decidable.isTrue x.24 =>
          let _x.25 := _y.5 _y.2;
          return _x.25
[Compiler.saveBase] size: 19
    def List.forBreak_._at_._example.spec_0 _x.1 xs : Nat :=
      let x := 42;
      fun _f.2 a : Nat :=
        cases a : Nat
        | Prod.mk fst.3 snd.4 =>
          return snd.4;
      fun _f.5 _y.6 : Nat :=
        return _y.6;
      cases xs : Nat
      | List.nil =>
        return x
      | List.cons head.7 tail.8 =>
        let _x.9 := 0;
        let _x.10 := instDecidableEqNat x _x.9;
        cases _x.10 : Nat
        | Decidable.isFalse x.11 =>
          let _x.12 := 10;
          let _x.13 := Nat.decLt _x.12 x;
          cases _x.13 : Nat
          | Decidable.isFalse x.14 =>
            let _x.15 := Nat.add x head.7;
            let _x.16 := List.forBreak_._at_.List.forBreak_._at_._example.spec_0.spec_0 _x.1 _x.15 _ _f.2 _f.5 tail.8;
            return _x.16
          | Decidable.isTrue x.17 =>
            let _x.18 := Nat.add x _x.1;
            return _x.18
        | Decidable.isTrue x.19 =>
          return x
[Compiler.saveBase] size: 8
    def _example : Nat :=
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := List.forBreak_._at_._example.spec_0 _x.1 _x.7;
      return _x.8
-/
#guard_msgs in
-- set_option trace.Compiler.specialize.candidate true in
-- set_option trace.Compiler.specialize.step true in
example := Id.run <| ExceptCpsT.runCatch do
  let x := 42;
  let ((), x) ←
    (List.forBreak_ (m:=StateT Nat (ExceptCpsT Nat Id)) [1, 2, 3] fun i _β «continue» «break» x =>
      if x = 0 then throw x
      else if x > 10 then «break» () (x + 1)
      else «continue» PUnit.unit (x + i)).run x
  return x
