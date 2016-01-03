constant p : nat → nat → Prop

constant p_trans : ∀ a b c, p a b → p b c → p a c

definition lemma1 (a b c d : nat) : a = d → p b c → p a b → p a c :=
begin
  intros,
  apply p_trans,
  blast,
  blast
end

print lemma1
