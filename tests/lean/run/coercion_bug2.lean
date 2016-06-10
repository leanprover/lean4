import data.nat
open nat

inductive List (T : Type) : Type :=
| nil {} : List T
| cons : T → List T → List T

definition length {T : Type} : List T → nat := List.rec 0 (fun x l m, succ m)
theorem length_nil {T : Type} : length (@List.nil T) = 0
:= eq.refl _
