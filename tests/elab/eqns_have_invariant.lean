module

/-! Simplifying generated equations must preserve the `have` abstraction invariant (#16122). -/

def dependentMatcher : Nat :=
  have a := 0
  have q : { n : Nat // n = a } :=
    match a with
    | 0 => ⟨0, rfl⟩
    | n+1 => ⟨n+1, rfl⟩
  q.val

example (n : Nat) : dependentMatcher = 0 := by
  simp -zeta only [dependentMatcher.eq_1, ← Nat.sub_self n]
  simp -zeta only [Nat.sub_self]
  rfl

opaque usesProof (n : Nat) (h : n = 0) : Nat

-- The dependency occurs inside a proof argument, while the result type remains `Nat`.
def namedMatcher : Nat :=
  have a := 0
  match h : a with
  | 0 => usesProof a h
  | _+1 => 0

example (n : Nat) : namedMatcher = usesProof 0 rfl := by
  simp -zeta only [namedMatcher.eq_1, ← Nat.sub_self n] <;>
    simp -zeta only [Nat.sub_self] <;> rfl

-- The dependent `let` makes equation normalization use `dsimp` for `n`'s value.
set_option cleanup.letToHave false in
def fixedHave : Nat :=
  have n :=
    have a := 0
    have q : {n : Nat // n = a} := match a with
      | 0 => ⟨0, rfl⟩
      | n+1 => ⟨n+1, rfl⟩
    q.val
  let v : Fin (n+1) := ⟨0, Nat.zero_lt_succ n⟩
  n + v.val

example (m : Nat) : fixedHave = 0 := by
  simp -zeta only [fixedHave.eq_1, ← Nat.sub_self m]
  simp -zeta only [Nat.sub_self]
  rfl
