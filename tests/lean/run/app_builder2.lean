import data.list
open perm
variables a b c : nat
variables H1 : a = b
variables H2 : b = c
set_option pp.all true
variables p q r : Prop
variables l1 l2 l3 : list nat
variables H3 : p ↔ q
variables H4 : q ↔ r
variables H5 : l1 ~ l2
variables H6 : l2 ~ l3

#refl eq a
#refl iff p
#refl perm l1

#symm eq H1
#symm iff H3
#symm perm H5

#trans eq H1, H2
#trans iff H3, H4
#trans perm H5, H6
