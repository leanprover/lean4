import macros
import tactic

theorem my_proof_irrel {a b : Bool} (H1 : a) (H2 : b) : H1 == H2
:= let H1b       : b                     := cast (by simp) H1,
       H1_eq_H1b : H1 == H1b             := hsymm (cast_heq (by simp) H1),
       H1b_eq_H2 : H1b == H2             := to_heq (proof_irrel H1b H2)
   in  htrans H1_eq_H1b H1b_eq_H2
