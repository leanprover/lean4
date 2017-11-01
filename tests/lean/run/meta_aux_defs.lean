def f : nat → nat
| 0     := 1
| (n+1) := f n + 10

#print f._main._meta_aux

#print nat.add._main._meta_aux
