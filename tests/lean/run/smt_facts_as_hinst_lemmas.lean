lemma aux : nat.succ 0 = 1 :=
rfl

attribute [ematch] aux

example (a : nat) : a = 1 → nat.succ 0 = a :=
begin [smt]
  close
end
