@[specialize 3 4] def List.foldrNonTR (f : α → β → β) (init : β) : (l : List α) → β
  | []     => init
  | a :: l => f a (foldrNonTR f init l)

@[always_inline, inline]
def List.forBreak_ {α : Type u} {m : Type w → Type x} [Monad m] (xs : List α) (s : σ) (body : α → OptionT (StateT σ (ExceptT ρ m)) PUnit) (kreturn : ρ → m γ) (kbreak : σ → m γ) : m γ :=
  List.foldrNonTR
    (fun a acc s => do
      let e ← body a s
      match e with
      | .error r => kreturn r
      | .ok (.some _, s) => acc s
      | .ok (none, s) => kbreak s)
    kbreak
    xs
    s

/--
trace: [Compiler.saveBase] size: 9
    def _example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := List.foldrNonTR._at_._example.spec_0 _x.7 x;
      return _x.8
[Compiler.saveBase] size: 25
    def List.foldrNonTR._at_._example.spec_0 x.1 _y.2 : Nat :=
      jp _jp.3 x : Nat :=
        let _x.4 := 13;
        let x := Nat.add x _x.4;
        let x := Nat.add x _x.4;
        let x := Nat.add x _x.4;
        let x := Nat.add x _x.4;
        let x := Nat.add x _x.4;
        let x := Nat.add x _x.4;
        let x := Nat.add x _x.4;
        return x;
      cases x.1 : Nat
      | List.nil =>
        goto _jp.3 _y.2
      | List.cons head.5 tail.6 =>
        let _x.7 := 0;
        let _x.8 := instDecidableEqNat _y.2 _x.7;
        cases _x.8 : Nat
        | Decidable.isFalse x.9 =>
          let _x.10 := 10;
          let _x.11 := Nat.decLt _x.10 _y.2;
          cases _x.11 : Nat
          | Decidable.isFalse x.12 =>
            let _x.13 := Nat.add _y.2 head.5;
            let _x.14 := List.foldrNonTR._at_._example.spec_0 tail.6 _x.13;
            return _x.14
          | Decidable.isTrue x.15 =>
            goto _jp.3 _y.2
        | Decidable.isTrue x.16 =>
          return _y.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
example := Id.run do
  let x := 42;
  List.forBreak_ (m:=Id) (ρ := Nat) [1, 2, 3] x (fun i => do
      let x ← get
      if x = 0 then throw (m := ExceptT Nat Id) x   -- return
      else if x > 10 then failure (f := OptionT _)  -- break
      else set (x + i) >>= fun _ => pure ())        -- continue
      pure fun x => do
  let x := x + 13;
  let x := x + 13;
  let x := x + 13;
  let x := x + 13;
  let x := x + 13;
  let x := x + 13;
  let x := x + 13;
  return x
