import logic

inductive unit : Type :=
| tt : unit

theorem inhabited_unit : inhabited unit
:= inhabited_intro tt
