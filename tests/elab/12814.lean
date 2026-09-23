/-!
Regression test for #12814: when we pattern match on a discriminant that occurs in a local
hypothesis, ToLCNF previously used a very generalized mechanism to handle this situation. However,
after a round of simplification all of the generated overhead just disappears. Thus, we special
cased this situation to generate code that is much closer to what we would have generated if no
dependent hypotheses were in scope.
-/

@[noinline]
def hole {P : Prop} (n : Nat) (_h : P) : Nat := n

/--
trace: [Compiler.init] size: 9
    def ex1 n h : Nat :=
      fun _f.1 h : Nat :=
        let _x.2 := @hole ◾ n ◾;
        return _x.2;
      let _alt.3 := _f.1;
      fun _f.4 k h : Nat :=
        let _x.5 := @hole ◾ k ◾;
        return _x.5;
      let _alt.6 := _f.4;
      cases n : Nat
      | Nat.zero =>
        let _x.7 := _alt.3 ◾;
        return _x.7
      | Nat.succ n.8 =>
        let _x.9 := _alt.6 n.8 ◾;
        return _x.9
-/
#guard_msgs in
set_option trace.Compiler.init true in
def ex1 (n : Nat) (h : n = n) : Nat :=
  match n with
  | 0 => hole n h
  | k + 1 => hole k h

/--
trace: [Compiler.init] size: 19
    def ex2 n h1 h2 : Nat :=
      fun _f.1 h1 h2 : Nat :=
        let _x.2 := instAddNat;
        let _x.3 := @instHAdd _ _x.2;
        let _x.4 := _x.3 # 0;
        let _x.5 := @hole ◾ n ◾;
        let _x.6 := @hole ◾ n ◾;
        let _x.7 := _x.4 _x.5 _x.6;
        return _x.7;
      let _alt.8 := _f.1;
      fun _f.9 k h1 h2 : Nat :=
        let _x.10 := instAddNat;
        let _x.11 := @instHAdd _ _x.10;
        let _x.12 := _x.11 # 0;
        let _x.13 := @hole ◾ n ◾;
        let _x.14 := @hole ◾ k ◾;
        let _x.15 := _x.12 _x.13 _x.14;
        return _x.15;
      let _alt.16 := _f.9;
      cases n : Nat
      | Nat.zero =>
        let _x.17 := _alt.8 ◾ ◾;
        return _x.17
      | Nat.succ n.18 =>
        let _x.19 := _alt.16 n.18 ◾ ◾;
        return _x.19
-/
#guard_msgs in
set_option trace.Compiler.init true in
def ex2 (n : Nat) (h1 : n ≠ 5) (h2 : 0 < n + 1) : Nat :=
  match n with
  | 0 => hole n h1 + hole n h2
  | k + 1 => hole n h1 + hole k h2
