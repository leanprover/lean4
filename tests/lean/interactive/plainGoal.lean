example : α → α := by
                  --^ $/lean/plainGoal
                   --^ $/lean/plainGoal
  intro a
--^ $/lean/plainGoal
 --^ $/lean/plainGoal
 --v $/lean/plainGoal
  focus
    apply a

example : α → α := by
                  --^ $/lean/plainGoal

example : 0 + n = n := by
  induction n with
  | zero => simp; simp
       --^ $/lean/plainGoal
  | succ
   --^ $/lean/plainGoal

example : α → α := by
  intro a; apply a
       --^ $/lean/plainGoal

example (h1 : n = m) (h2 : m = 0) : 0 = n := by
  rw [h1, h2]
 --^ $/lean/plainGoal
       --^ $/lean/plainGoal
           --^ $/lean/plainGoal

example : 0 + n = n := by
  induction n
  focus
 --^ $/lean/plainGoal
    rfl
-- TODO: goal state after dedent

example : 0 + n = n := by
  induction n with
 --^ $/lean/plainGoal

example : 0 + n = n := by
  cases n with
 --^ $/lean/plainGoal

example : ∀ a b : Nat, a = b := by
  intro a b
 --^ $/lean/plainGoal

example : α → α := (by
                  --^ $/lean/plainGoal

example (p : α → Prop) (a b : α) [DecidablePred p] (h : ∀ {p} [DecidablePred p], p a → p b) : p b := by
  apply h _
 --^ $/lean/plainGoal
 -- should not display solved goal `⊢ DecidablePred p`

example : True ∧ False := by
  constructor
  { constructor }
 --^ $/lean/plainGoal
  { }
 --^ $/lean/plainGoal

example : True ∧ False := by
  constructor
  · constructor
 --^ $/lean/plainGoal
  ·
 --^ $/lean/plainGoal

theorem left_distrib (t a b : Nat) : t * (a + b) = t * a + t * b := by
  induction b
  next => simp
  next =>
    rw [Nat.add_succ]
    repeat (rw [Nat.mul_succ])
                           --^ $/lean/plainGoal

example (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as <;> skip <;> (try rename_i h; simp[h]) <;> rfl
                                                   --^ $/lean/plainGoal
                                                    --^ $/lean/plainGoal

example : True := (by exact True.intro)
                                    --^ $/lean/plainGoal

example : True := (by exact True.intro )
                                     --^ $/lean/plainGoal

set_option trace.Elab.info true
example : True ∧ False := by
  · constructor; constructor
              --^ $/lean/plainGoal

example : False := by
-- EOF test
--^ $/lean/plainGoal
