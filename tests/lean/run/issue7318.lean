
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

#guard_msgs in
theorem bar_decide : Q := by
  simp (discharger := native_decide) [Q_of_decide]

-- Try with backtracking

theorem Q_of_decide' : (1 + 1 = 2) → False → Q := fun _ _ => P.mk

theorem bar_decide' : Q := by
  simp (discharger := native_decide) [Q_of_decide', Q_of_decide]

theorem bar_decide'' : Q := by
  try simp (discharger := native_decide) [Q_of_decide']
  simp (discharger := native_decide) [Q_of_decide]
