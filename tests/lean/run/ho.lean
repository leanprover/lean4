import data.nat

inductive star : Type₁ :=
| z  : star
| s  : (nat → star) → star

check @star.rec
check @star.cases_on

example (f : nat → star) : ¬ star.z = star.s f :=
assume H, star.no_confusion H
