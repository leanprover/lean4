module

/-!
Smart unfolding must check a recursive match inside a discriminant before returning
its result. Writing the discriminant inline or binding it with `let` should agree.
-/

private def fromSome : Nat → Nat
  | 0 => 0
  | n+1 => match some (match n with | 0 => 11 | k+1 => fromSome k) with
    | some x => x
    | none => 5

example (n : Nat) : fromSome (n+1) = (match n with | 0 => 11 | k+1 => fromSome k) := by
  fail_if_success exact rfl
  cases n <;> rfl

private def fromSomeLet : Nat → Nat
  | 0 => 0
  | n+1 =>
    let t := match n with | 0 => 11 | k+1 => fromSomeLet k
    match some t with
    | some x => x
    | none => 5

example (n : Nat) : fromSomeLet (n+1) = (match n with | 0 => 11 | k+1 => fromSomeLet k) := by
  fail_if_success exact rfl
  cases n <;> rfl

-- The pair pattern can select its branch even when the match producing the pair is stuck.
private def fromPair : Nat → Nat
  | 0 => 0
  | n+1 =>
    match (match n with | 0 => (0, 0) | k+1 => (fromPair k, 0)) with
    | (x, _) => x

example (n : Nat) :
    fromPair (n+1) = (match n with | 0 => (0, 0) | k+1 => (fromPair k, 0)).1 := by
  fail_if_success exact rfl
  cases n <;> rfl

-- The outer match also needs a marker because the `false` branch recurses on its pattern variable.
private def both (m : Nat) (flag : Bool) : Nat :=
  match m with
  | 0 => 0
  | n+1 =>
    match flag, some (match n with | 0 => 11 | k+1 => both k flag), n with
    | true, some x, _ => x
    | false, _, k+1 => both k flag
    | _, _, _ => 5
termination_by structural m

example (n : Nat) : both (n+1) true = (match n with | 0 => 11 | k+1 => both k true) := by
  fail_if_success exact rfl
  cases n <;> rfl

example (P : Nat → Prop) (k : Nat) (h : P (both k true)) : P (both (k+2) true) := by
  dsimp (config := { autoUnfold := true }) only
  guard_target = P (both k true)
  exact h
