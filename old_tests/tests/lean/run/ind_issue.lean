def stack := list nat
instance : has_append stack :=
by unfold stack; apply_instance

example (s : stack) : s ++ [] = s :=
begin
  induction s,
  refl, apply list.append_nil
end
