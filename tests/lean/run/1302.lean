open list fin

vm_eval map (λ i, true) [1]
vm_eval map (λ i, true) [1, 2, 3]
vm_eval map (λ (i : fin 2), true) [fin.mk 0 dec_trivial, fin.mk 1 dec_trivial]
