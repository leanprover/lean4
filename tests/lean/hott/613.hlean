import hit.pushout

open pushout unit bool
private definition unit_of_empty (u : empty) : unit := star

example : pushout unit_of_empty unit_of_empty → bool :=
begin
  intro x, induction x using pushout.rec,
    exact tt,
    exact ff,
    cases x
end

attribute pushout.rec [recursor]

example : pushout unit_of_empty unit_of_empty → bool :=
begin
  intro x, induction x,
    exact tt,
    exact ff,
    cases x
end
