variable P : Prop
premise HP : P

example : P :=
have H : P, from HP,
H

example : P :=
have H : P, from HP,
show P, from H

example : P :=
have H : P, from HP,
by+ exact H

example : P :=
have H : P, from HP,
show P, by+ exact H

example : P :=
have H : P, from HP,
show P, begin+ exact H end

example : P :=
have H : P, from HP,
show P, using H, by exact H

example : P :=
assert H : P, from HP,
show P, by exact H
