lemma aux : nat.succ 0 = 1 :=
rfl

attribute [ematch] aux

lemma ex (a : nat) : a = 1 → nat.succ 0 = a :=
begin [smt]
  close
end
