example (a b c : nat) : a = b → b = 0 → a = 0 ∧ b = a :=
begin
  intros, constructor,
  focus {  subst a
       --^ "command":"info"
         },
     --^ "command":"info"
      assumption,
 --^ "command":"info"
    subst a
end
