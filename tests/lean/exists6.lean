import Int.
variable P : Int -> Int -> Int -> Bool
axiom Ax1 : exists x y z, P x y z
axiom Ax2 : forall x y z, not (P x y z)
theorem T : false :=
    ExistsElim Ax1 (fun a H1, ExistsElim H1 (fun b H2, ExistsElim H2 (fun (c : Int) (H3 : P a b c),
         let notH3 : not (P a b c) :=  ForallElim (ForallElim (ForallElim Ax2 a) b) c
         in Absurd H3 notH3)))
