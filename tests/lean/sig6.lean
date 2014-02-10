variables A B : (Type U)
variables t1 t2 : A ⨯ B
axiom pair_Ax {A : (Type U)} {B : A → (Type U)} (p : sig x, B x) : (pair (proj1 p) (proj2 p) : sig x, B x) = p
theorem spairext {A B : (Type U)} {p1 p2 : A ⨯ B} (H1 : proj1 p1 = proj1 p2) (H2 : proj2 p1 = proj2 p2) : p1 = p2
:= calc p1  = (pair (proj1 p1) (proj2 p1))  :  symm (pair_Ax p1)
        ... = (pair (proj1 p2) (proj2 p1))  :  { H1 }
        ... = (pair (proj1 p2) (proj2 p2))  :  { H2 }
        ... = p2                            :  pair_Ax p2