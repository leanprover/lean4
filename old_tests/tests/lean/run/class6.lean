open tactic

inductive t1 : Type
| mk1 : t1

inductive t2 : Type
| mk2 : t2

theorem inhabited_t1 : inhabited t1
:= inhabited.mk t1.mk1

theorem inhabited_t2 : inhabited t2
:= inhabited.mk t2.mk2

attribute [instance] inhabited_t1
attribute [instance] inhabited_t2

theorem T : inhabited (t1 × t2)
:= by apply_instance
