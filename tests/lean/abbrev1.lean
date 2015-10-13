open nat

abbreviation foo  : Π (A : Type), nat := λ a, 2 + 3

definition tst := foo nat

set_option pp.abbreviations false

print definition tst

set_option pp.abbreviations true

print definition tst

abbreviation id [parsing_only] {A : Type} (a : A) := a

definition tst1 :nat := id 10

print definition tst1
