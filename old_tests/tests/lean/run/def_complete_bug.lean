definition g : list nat → list nat → nat
| []          (y::ys)  := y
| []           ys      := 0
| (x1::x2::xs) ys      := g xs ys
| (x::xs)      (y::ys) := g xs ys + y
| (x::xs)      []      := g xs []

#print g._main.equations._eqn_1
#print g._main.equations._eqn_2
#print g._main.equations._eqn_3
#print g._main.equations._eqn_4
#print g._main.equations._eqn_5
#print g._main.equations._eqn_6
