import logic data.prod
using prod

inductive t1 : Type :=
mk1 : t1

inductive t2 : Type :=
mk2 : t2

theorem inhabited_t1 : inhabited t1
:= inhabited_mk mk1

theorem inhabited_t2 : inhabited t2
:= inhabited_mk mk2

instance inhabited_t1 inhabited_t2

theorem T : inhabited (t1 × t2)
:= _
