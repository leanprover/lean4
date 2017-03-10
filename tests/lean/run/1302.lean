open list fin

#eval map (λ i, true) [1]
#eval map (λ i, true) [1, 2, 3]
#eval map (λ (i : fin 2), true) [fin.mk 0 dec_trivial, fin.mk 1 dec_trivial]
