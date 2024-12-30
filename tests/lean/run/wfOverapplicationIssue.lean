theorem Array.sizeOf_lt_of_mem' [DecidableEq α] [SizeOf α] {as : Array α} (h : as.contains a) : sizeOf a < sizeOf as := by
  simp [Membership.mem, contains, any, Id.run, BEq.beq, anyM] at h
  let rec aux (j : Nat) : anyM.loop (m := Id) (fun b => decide (a = b)) as as.size (Nat.le_refl ..) j = true → sizeOf a < sizeOf as := by
    unfold anyM.loop
    intro h
    split at h
    · simp only [bind, decide_eq_true_eq, pure] at h; split at h
      next he => subst a; apply sizeOf_get
      next => have ih := aux (j+1) h; assumption
    · contradiction
    termination_by as.size - j
  apply aux 0 h
