example (n : nat) : true :=
begin
  cases h : n with m,
  { guard_hyp h := n = nat.zero, admit },
  { guard_hyp h := n = nat.succ m, admit}
end
