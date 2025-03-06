
inductive P : Prop where
  | mk : P

def Q : Prop := P

theorem Q_of_P : P → Q := fun x => x

-- works
theorem foo : Q := by
  simp (discharger := exact P.mk) [Q_of_P]

#guard_msgs in
theorem bar : Q := by
  simp (discharger := as_aux_lemma => exact P.mk) [Q_of_P]

theorem Q_of_decide : (1 + 1 = 2) → Q := fun _ => P.mk

theorem bar_decide : Q := by
  simp (discharger := native_decide) [Q_of_decide]

-- Try with backtracking

theorem Q_of_decide' : (1 + 2 = 3) → False → Q := fun _ _ => P.mk

theorem bar_decide' : Q := by
  simp (discharger := native_decide) [Q_of_decide', Q_of_decide]

theorem bar_decide'' : Q := by
  try simp (discharger := native_decide) [Q_of_decide']
  simp (discharger := native_decide) [Q_of_decide]

-- The following were tests from trying to reproduce a failure in mathlib that was in the end
-- somewhere else. But maybe they are still useful in the future.

theorem bar_decide_3 : Q := by
  have q1 : Q := by apply Q_of_decide; native_decide
  have q2 : Q := by apply Q_of_decide; native_decide
  have h1 : 1 + 2 = 3 := by native_decide
  have h2 : 2 + 3 = 5 := by native_decide
  apply Q_of_decide
  native_decide

inductive Three where | A | B | C

theorem bar_decide_4 (t : Three) : Q := by
  cases t with
  | A | B =>
    rw [show Q ↔ True by apply iff_true_intro; apply Q_of_decide; native_decide]
    trivial
  | C =>
    rw [show Q ↔ True by apply iff_true_intro; apply Q_of_decide; native_decide]
    trivial

-- Check if messages from dischargers still appear

/--
info: case simp.discharger
⊢ 1 + 1 = 2
-/
#guard_msgs in
theorem bar_decide_with_message : Q := by
  simp (discharger := trace_state; native_decide) [Q_of_decide]
