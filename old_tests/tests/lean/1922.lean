set_option pp.implicit true

structure C :=
( d : Π { X : Type }, list X → list X )

def P(c : C):= c.d [0]

#print P
