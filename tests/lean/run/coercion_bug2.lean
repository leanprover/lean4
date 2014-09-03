import data.nat
open nat

inductive list (T : Type) : Type :=
nil {} : list T,
cons : T → list T → list T

definition length {T : Type} : list T → nat := list_rec 0 (fun x l m, succ m)
theorem length_nil {T : Type} : length (@nil T) = 0
:= refl _
