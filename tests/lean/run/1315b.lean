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

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (expr.alpha_eqv t e)

meta def check_target (p : pexpr) : tactic unit :=
do t ← target, check_expr p t

run_cmd do
  t ← to_expr `(test._match_2) >>= infer_type,
  trace t,
  check_expr `(nat → nat) t

example (k m n : ℕ) : test (succ k) (succ (succ n)) m = 3 :=
begin
  revert m,
  induction n with n',
  {intro, reflexivity},
  {intro,
   simp [test] {zeta := ff}, dsimp, simp [ih_1],
   simp [nat.bit1_eq_succ_bit0, test]}
end
