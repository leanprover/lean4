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

/- The second and fourth alternatives are impossible because `a = 0`. Equation generation
must eliminate them, including the contradiction in the second alternative's overlap condition. -/
def depMatch (x : Nat) : Nat :=
  have a := 0
  have q : { n : Nat // n ≤ x + a } :=
    match x, a with
    | 0, 0 => ⟨0, by simp⟩
    | 0, a => ⟨0, by simp⟩
    | x+1, 0 => ⟨x, by simp⟩
    | x+1, a+1 => ⟨x+a, by lia⟩
  q.val

/--
info: depMatch.eq_1 :
  depMatch 0 =
    let a := 0;
    have q := ⟨0, depMatch._proof_1⟩;
    q.val
-/
#guard_msgs in #check depMatch.eq_1

/--
info: depMatch.eq_2 (x_3 : Nat) :
  depMatch x_3.succ =
    let a := 0;
    have q := ⟨x_3, ⋯⟩;
    q.val
-/
#guard_msgs in #check depMatch.eq_2

example : depMatch 0 = 0 := depMatch.eq_1
example (n : Nat) : depMatch (n+1) = n := depMatch.eq_2 n

/-- error: Unknown identifier `depMatch.eq_3` -/
#guard_msgs in #check depMatch.eq_3

-- Constant discriminants must eliminate impossible alternatives without any local bindings.
def constantDiscr (x : Nat) : Nat :=
  match x, (0 : Nat) with
  | 0, 0 => 0
  | 0, _ => 0
  | n+1, 0 => n
  | n+1, k+1 => n+k

example : constantDiscr 0 = 0 := constantDiscr.eq_1
example (n : Nat) : constantDiscr (n+1) = n := constantDiscr.eq_2 n

/-- error: Unknown identifier `constantDiscr.eq_3` -/
#guard_msgs in #check constantDiscr.eq_3

-- The impossible overlap condition quantifies over the payload of `some`.
def constructorDiscr (x : Nat) : Nat :=
  match x, (some 0 : Option Nat) with
  | 0, some n => n
  | 0, _ => 0
  | n+1, _ => n

example : constructorDiscr 0 = 0 := constructorDiscr.eq_1
example (n : Nat) : constructorDiscr (n+1) = n := constructorDiscr.eq_2 n

/-- info: constructorDiscr.eq_1 : constructorDiscr 0 = 0 -/
#guard_msgs in #check constructorDiscr.eq_1

/-- info: constructorDiscr.eq_2 (n : Nat) : constructorDiscr n.succ = n -/
#guard_msgs in #check constructorDiscr.eq_2

/-- error: Unknown identifier `constructorDiscr.eq_3` -/
#guard_msgs in #check constructorDiscr.eq_3
