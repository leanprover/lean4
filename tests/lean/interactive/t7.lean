Variable q : Int -> Int -> Bool.
Variable p : Int -> Bool.
Axiom Ax (a b : Int) (H : q a b) : p b.
Variable a : Int.
Theorem T (x : Int) : (q a x) => (p x).
    apply imp_tac.
    apply (Ax a).
    assumption.
    done.
