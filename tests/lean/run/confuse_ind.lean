attribute [reducible] definition mk_arrow (A : Sort*) (B : Sort*) :=
A → A → B

inductive confuse (A : Type)
| leaf1 : confuse
| leaf2 : num → confuse
| node : mk_arrow A confuse → confuse

check confuse.cases_on
