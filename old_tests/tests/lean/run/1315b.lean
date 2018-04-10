open nat

def k : ℕ := 0

def fails : Π (n : ℕ) (m : ℕ), ℕ
| 0 m := 0
| (succ n) m :=
  match k with
  | 0 := 0
  | (succ i) :=
    let val := m+1 in
    match fails n val with
    | 0 := 0
    | (succ l) := 0
    end
  end


def test (k : ℕ) : Π (n : ℕ) (m : ℕ), ℕ
| 0 m := 0
| (succ n) m :=
  match k with
  | 0 := 1
  | (succ i) :=
    let val := m+1 in
    match test n val with
    | 0 := 2
    | (succ l) := 3
    end
  end

example (k m : ℕ) : test k 0 m = 0 :=
rfl

example (m n : ℕ) : test 0 (succ n) m = 1 :=
rfl

example (k m : ℕ) : test (succ k) 1 m = 2 :=
rfl

example (k m : ℕ) : test (succ k) 2 m = 3 :=
rfl

example (k m : ℕ) : test (succ k) 3 m = 3 :=
rfl

open tactic

run_cmd do
  t ← infer_type `(test._match_2),
  trace t,
  tactic.interactive.guard_expr_eq t ```(nat → nat)

example (k m n : ℕ) : test (succ k) (succ (succ n)) m = 3 :=
begin
  revert m,
  induction n with n',
  { intro, reflexivity},
  { intro,
    simp [test, n_ih] }
end
