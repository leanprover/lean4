structure weird (A : Type) :=
{B : Type} (op : A → B → A)

definition foo1 : weird nat :=
{ op := nat.add }

definition foo2 : weird nat :=
⟨ nat.add ⟩

definition foo3 : weird nat :=
{ B := nat, op := nat.add }
