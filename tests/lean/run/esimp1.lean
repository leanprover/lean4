open nat

example (x y : nat) (H : (fun (a : nat),  sigma.pr1 ⟨a, y⟩) x = 0) : x = 0 :=
begin
  esimp at H,
  exact H
end

definition foo [irreducible] (a : nat) := a

example (x y : nat) (H : (fun (a : nat), sigma.pr1 ⟨foo a, y⟩) x = 0) : x = 0 :=
begin
  esimp at H,
  esimp ↑foo at H,
  exact H
end

example (x y : nat) (H : x = 0) : (fun (a : nat), sigma.pr1 ⟨foo a, y⟩) x = 0 :=
begin
  esimp,
  esimp ↑foo,
  exact H
end

example (x y : nat) (H : x = 0) : (fun (a : nat), sigma.pr1 ⟨foo a, y⟩) x = 0 :=
begin
  esimp,
  unfold foo,
  exact H
end
