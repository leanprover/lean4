definition p1 := (10, 20, 30)

definition v2 : nat :=
match p1 with
⟨a, b⟩ := a
end

example : v2 = 10 := rfl

definition v3 : nat :=
match p1 with
(| a, b |) := a
end
