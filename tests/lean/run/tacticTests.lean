inductive Le (m : Nat) : Nat → Prop
  | base : Le m m
  | succ : (n : Nat) → Le m n → Le m n.succ

theorem ex1 (m : Nat) : Le m 0 → m = 0 := by
  intro h
  cases h
  rfl

theorem ex2 (m n : Nat) : Le m n → Le m.succ n.succ := by
  intro h
  induction h with
  | base => apply Le.base
  | succ n m ih =>
    apply Le.succ
    apply ih

theorem ex3 (m : Nat) : Le 0 m := by
  induction m with
  | zero => apply Le.base
  | succ m ih =>
    apply Le.succ
    apply ih

theorem ex4 (m : Nat) : ¬ Le m.succ 0 := by
  intro h
  cases h

theorem ex5 {m n : Nat} : Le m n.succ → m = n.succ ∨ Le m n := by
  intro h
  cases h with
  | base => apply Or.inl; rfl
  | succ => apply Or.inr; assumption

theorem ex6 {m n : Nat} : Le m.succ n.succ → Le m n := by
  revert m
  induction n with
  | zero =>
    intros m h;
    cases h with
    | base => apply Le.base
    | succ n h => exact absurd h (ex4 _)
  | succ n ih =>
    intros m h
    have aux := ih (m := m)
    cases ex5 h with
    | inl h =>
      injection h with h
      subst h
      apply Le.base
    | inr h =>
      apply Le.succ
      exact ih h

theorem ex7 {m n o : Nat} : Le m n → Le n o → Le m o := by
  intro h
  induction h with
  | base => intros; assumption
  | succ n s ih =>
    intro h₂
    apply ih
    apply ex6
    apply Le.succ
    assumption

theorem ex8 {m n : Nat} : Le m.succ n → Le m n := by
  intro h
  apply ex6
  apply Le.succ
  assumption

theorem ex9 {m n : Nat} : Le m n → m = n ∨ Le m.succ n := by
  intro h
  cases h with
  | base => apply Or.inl; rfl
  | succ n s =>
    apply Or.inr
    apply ex2
    assumption

/-
theorem ex10 (n : Nat) : ¬ Le n.succ n := by
  intro h
  cases h -- TODO: improve cases tactic
  done
-/

theorem ex10 (n : Nat) : n.succ ≠ n := by
  induction n with
  | zero => intro h; injection h; done
  | succ n ih => intro h; injection h with h; apply ih h

theorem ex11 (n : Nat) : ¬ Le n.succ n := by
  induction n with
  | zero => intro h; cases h; done
  | succ n ih =>
    intro h
    have aux := ex6 h
    exact absurd aux ih
    done

theorem ex12 (m n : Nat) : Le m n → Le n m → m = n := by
  revert m
  induction n with
  | zero => intro m h1 h2; apply ex1; assumption; done
  | succ n ih =>
    intro m h1 h2
    have ih := ih m
    cases ex5 h1 with
    | inl h => assumption
    | inr h =>
      have ih := ih h
      have h3 := ex8 h2
      have ih := ih h3
      subst ih
      apply absurd h2 (ex11 _)
      done

inductive Foo : Nat → Prop where
  | foo : Foo 0
  | bar : Foo 0
  | baz : Foo 1

example (f : Foo 0) : True := by
  cases f with
  | _ => trivial

example (f : Foo n) (h : n = 0) : True := by
  induction f with simp at h
  | _ => trivial
