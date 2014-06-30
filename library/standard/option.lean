import logic

inductive option (A : Type) : Type :=
| none {} : option A
| some    : A → option A

theorem inhabited_option (A : Type) : inhabited (option A)
:= inhabited_intro none
