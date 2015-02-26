import logic data.prod data.unit

definition mk_arrow (A : Type) (B : Type) :=
A → A → B

inductive confuse (A : Type) :=
| leaf1 : confuse A
| leaf2 : num → confuse A
| node : mk_arrow A (confuse A) → confuse A

check confuse.cases_on
