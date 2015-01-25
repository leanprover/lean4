import logic data.prod
open prod

inductive t1 : Type :=
mk1 : t1

inductive t2 : Type :=
mk2 : t2

theorem inhabited_t1 : inhabited t1
:= inhabited.mk t1.mk1

theorem inhabited_t2 : inhabited t2
:= inhabited.mk t2.mk2

attribute inhabited_t1 [instance]
attribute inhabited_t2 [instance]

theorem T : inhabited (t1 × t2)
:= _
