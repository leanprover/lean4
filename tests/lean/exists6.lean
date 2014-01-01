Import Int.
Variable P : Int -> Int -> Int -> Bool
Axiom Ax1 : exists x y z, P x y z
Axiom Ax2 : forall x y z, not (P x y z)
Theorem T : false :=
    ExistsElim Ax1 (fun a H1, ExistsElim H1 (fun b H2, ExistsElim H2 (fun (c : Int) (H3 : P a b c),
         let notH3 : not (P a b c) :=  ForallElim (ForallElim (ForallElim Ax2 a) b) c
         in Absurd H3 notH3)))
