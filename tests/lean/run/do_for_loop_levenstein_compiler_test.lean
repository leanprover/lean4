@[inline] unsafe def Array.forInNew'Unsafe {α : Type u} {σ β : Type v} {m : Type v → Type w}
    (as : Array α) (s : σ) (kcons : (a : α) → (h : a ∈ as) → (σ → m β) → σ → m β) (knil : σ → m β) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (s : σ) : m β :=
    if i < sz then
      let a := as.uget i lcProof
      kcons a lcProof (loop (i+1)) s
    else
      knil s
  loop 0 s

@[inline] protected def Std.Legacy.Range.forInNew' {m : Type u → Type v} {σ β} (range : Range) (init : σ)
    (kcons : (i : Nat) → i ∈ range → (σ → m β) → σ → m β) (knil : σ → m β) : m β :=
  have := range.step_pos
  let rec @[specialize] loop (i : Nat)
      (hs : (i - range.start) % range.step = 0) (hl : range.start ≤ i := by omega) : σ → m β :=
    if h : i < range.stop then
      kcons i ⟨hl, by omega, hs⟩ (loop (i + range.step) (by rwa [Nat.add_comm, Nat.add_sub_assoc hl, Nat.add_mod_left]))
    else
      knil
  loop range.start (by simp) (by simp) init

/--
trace: [Compiler.saveMono] size: 13
    def _private.Init.Data.Array.Basic.0.Array.anyMUnsafe.any._at_.Array.contains._at_.deletions.spec_0.spec_0 a as i stop : Bool :=
      let _x.1 := USize.decEq i stop;
      cases _x.1 : Bool
      | Bool.false =>
        let _x.2 := Array.uget ◾ as i ◾;
        let _x.3 := String.decEq a _x.2;
        cases _x.3 : Bool
        | Bool.false =>
          let _x.4 := 1;
          let _x.5 := USize.add i _x.4;
          let _x.6 := Array.anyMUnsafe.any._at_.Array.contains._at_.deletions.spec_0.spec_0.2 a as _x.5 stop;
          return _x.6
        | Bool.true =>
          return _x.3
      | Bool.true =>
        let _x.7 := false;
        return _x.7
[Compiler.saveMono] size: 12
    def Array.contains._at_.deletions.spec_0 as a : Bool :=
      let _x.1 := 0;
      let _x.2 := Array.size ◾ as;
      let _x.3 := Nat.decLt _x.1 _x.2;
      cases _x.3 : Bool
      | Bool.false =>
        return _x.3
      | Bool.true =>
        cases _x.3 : Bool
        | Bool.false =>
          return _x.3
        | Bool.true =>
          let _x.4 := 0;
          let _x.5 := USize.ofNat _x.2;
          let _x.6 := Array.anyMUnsafe.any._at_.Array.contains._at_.deletions.spec_0.spec_0.2 a as _x.4 _x.5;
          return _x.6
[Compiler.saveMono] size: 18
    def Array.forInNew'Unsafe.loop._at_.deletions.spec_2 as sz i s : Array String :=
      let _x.1 := USize.decLt i sz;
      cases _x.1 : Array String
      | Bool.false =>
        let _x.2 := Array.reverse._redArg s;
        return _x.2
      | Bool.true =>
        let a := Array.uget ◾ as i ◾;
        let _x.3 := @String.instDecidableEqBoolIsEmptyTrue a;
        cases _x.3 : Array String
        | Bool.false =>
          let _x.4 := 1;
          let _x.5 := USize.add i _x.4;
          let _x.6 := 0;
          let _x.7 := String.length a;
          let _x.8 := 1;
          let _x.9 := Std.Legacy.Range.mk _x.6 _x.7 _x.8 ◾;
          let _x.10 := Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4._redArg as sz _x.5 a _x.8 _x.9 _x.6 s;
          return _x.10
        | Bool.true =>
          let _x.11 := Array.reverse._redArg s;
          return _x.11
[Compiler.saveMono] size: 24
    def Std.Legacy.Range.forInNew'.loop._at_.Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4.spec_4._redArg s' _x.1 as sz _x.2 range i a.3 : Array
      String :=
      cases range : Array String
      | Std.Legacy.Range.mk start stop step step_pos =>
        let _x.4 := Nat.decLt i stop;
        cases _x.4 : Array String
        | Bool.false =>
          let _x.5 := Array.forInNew'Unsafe.loop._at_.deletions.spec_2 as sz _x.2 a.3;
          return _x.5
        | Bool.true =>
          let _x.6 := Nat.add i step;
          let _x.7 := 0;
          let _x.8 := String.utf8ByteSize s';
          let _x.9 := String.Slice.mk s' _x.7 _x.8 ◾;
          let _x.10 := @String.Slice.Pos.nextn _x.9 _x.7 i;
          let _x.11 := @String.extract s' _x.7 _x.10;
          let _x.12 := Nat.add i _x.1;
          let _x.13 := @String.Slice.Pos.nextn _x.9 _x.7 _x.12;
          let _x.14 := @String.extract s' _x.13 _x.8;
          let d := String.append _x.11 _x.14;
          let _x.15 := Array.contains._at_.deletions.spec_0 a.3 d;
          cases _x.15 : Array String
          | Bool.false =>
            let out := Array.push ◾ a.3 d;
            let _x.16 := Std.Legacy.Range.forInNew'.loop._at_.Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4.spec_4._redArg s' _x.1 as sz _x.2 range _x.6 out;
            return _x.16
          | Bool.true =>
            let _x.17 := Std.Legacy.Range.forInNew'.loop._at_.Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4.spec_4._redArg s' _x.1 as sz _x.2 range _x.6 a.3;
            return _x.17
[Compiler.saveMono] size: 24
    def Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4._redArg as sz _x.1 s' _x.2 range i a.3 : Array
      String :=
      cases range : Array String
      | Std.Legacy.Range.mk start stop step step_pos =>
        let _x.4 := Nat.decLt i stop;
        cases _x.4 : Array String
        | Bool.false =>
          let _x.5 := Array.forInNew'Unsafe.loop._at_.deletions.spec_2 as sz _x.1 a.3;
          return _x.5
        | Bool.true =>
          let _x.6 := Nat.add i step;
          let _x.7 := 0;
          let _x.8 := String.utf8ByteSize s';
          let _x.9 := String.Slice.mk s' _x.7 _x.8 ◾;
          let _x.10 := @String.Slice.Pos.nextn _x.9 _x.7 i;
          let _x.11 := @String.extract s' _x.7 _x.10;
          let _x.12 := Nat.add i _x.2;
          let _x.13 := @String.Slice.Pos.nextn _x.9 _x.7 _x.12;
          let _x.14 := @String.extract s' _x.13 _x.8;
          let d := String.append _x.11 _x.14;
          let _x.15 := Array.contains._at_.deletions.spec_0 a.3 d;
          cases _x.15 : Array String
          | Bool.false =>
            let out := Array.push ◾ a.3 d;
            let _x.16 := Std.Legacy.Range.forInNew'.loop._at_.Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4.spec_4._redArg s' _x.2 as sz _x.1 range _x.6 out;
            return _x.16
          | Bool.true =>
            let _x.17 := Std.Legacy.Range.forInNew'.loop._at_.Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4.spec_4._redArg s' _x.2 as sz _x.1 range _x.6 a.3;
            return _x.17
[Compiler.saveMono] size: 15
    def deletions n s : Array String :=
      let zero := 0;
      let isZero := Nat.decEq n zero;
      cases isZero : Array String
      | Bool.true =>
        let _x.1 := 1;
        let _x.2 := Array.mkEmpty ◾ _x.1;
        let _x.3 := Array.push ◾ _x.2 s;
        return _x.3
      | Bool.false =>
        let one := 1;
        let n.4 := Nat.sub n one;
        let out := Array.mkEmpty ◾ zero;
        let _x.5 := deletions n.4 s;
        let sz := Array.usize ◾ _x.5;
        let _x.6 := 0;
        let _x.7 := Array.forInNew'Unsafe.loop._at_.deletions.spec_2 _x.5 sz _x.6 out;
        return _x.7
[Compiler.saveMono] size: 24
    def Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._redArg s' _x.1 kcontinue range i a.2 : Array String :=
      cases range : Array String
      | Std.Legacy.Range.mk start stop step step_pos =>
        let _x.3 := Nat.decLt i stop;
        cases _x.3 : Array String
        | Bool.false =>
          let _x.4 := kcontinue a.2;
          return _x.4
        | Bool.true =>
          let _x.5 := Nat.add i step;
          let _x.6 := 0;
          let _x.7 := String.utf8ByteSize s';
          let _x.8 := String.Slice.mk s' _x.6 _x.7 ◾;
          let _x.9 := @String.Slice.Pos.nextn _x.8 _x.6 i;
          let _x.10 := @String.extract s' _x.6 _x.9;
          let _x.11 := Nat.add i _x.1;
          let _x.12 := @String.Slice.Pos.nextn _x.8 _x.6 _x.11;
          let _x.13 := @String.extract s' _x.12 _x.7;
          let d := String.append _x.10 _x.13;
          let _x.14 := Array.contains._at_.deletions.spec_0 a.2 d;
          cases _x.14 : Array String
          | Bool.false =>
            let out := Array.push ◾ a.2 d;
            let _x.15 := Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._redArg s' _x.1 kcontinue range _x.5 out;
            return _x.15
          | Bool.true =>
            let _x.16 := Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._redArg s' _x.1 kcontinue range _x.5 a.2;
            return _x.16
[Compiler.saveMono] size: 1
    def Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1 s' _x.1 kcontinue range this i hs hl a.2 : Array String :=
      let _x.3 := Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._redArg s' _x.1 kcontinue range i a.2;
      return _x.3
[Compiler.saveMono] size: 1
    def Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4 as sz _x.1 s' _x.2 range this i hs hl a.3 : Array
      String :=
      let _x.4 := Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4._redArg as sz _x.1 s' _x.2 range i a.3;
      return _x.4
[Compiler.saveMono] size: 1
    def Std.Legacy.Range.forInNew'.loop._at_.Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4.spec_4 s' _x.1 as sz _x.2 range this i hs hl a.3 : Array
      String :=
      let _x.4 := Std.Legacy.Range.forInNew'.loop._at_.Std.Legacy.Range.forInNew'.loop._at_.deletions.spec_1._at_.Array.forInNew'Unsafe.loop._at_.deletions.spec_2.spec_4.spec_4._redArg s' _x.1 as sz _x.2 range i a.3;
      return _x.4
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
unsafe def deletions (n : Nat) (s : String) : Array String :=
  match n with
  | 0 => #[s]
  | n' + 1 => Id.run do
    let out := #[];
    have kbreak := fun (s : Array String) =>
      let out := s;
      pure out.reverse;
    (deletions n' s).forInNew'Unsafe out
      (fun s' _ kcontinue s =>
        let out := s;
        if s'.isEmpty = true then kbreak out
        else
          [:s'.length].forInNew' out
            (fun i _ kcontinue s =>
              let out := s;
              let d := (s'.take i).copy ++ s'.drop (i + 1);
              if (!out.contains d) = true then
                let out := out.push d;
                kcontinue out
              else kcontinue out)
            fun s =>
            let out := s;
            kcontinue out)
      kbreak
