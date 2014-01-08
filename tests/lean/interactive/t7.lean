import Int.
(* import("tactic.lua") *)
variable q : Int -> Int -> Bool.
variable p : Int -> Bool.
axiom Ax (a b : Int) (H : q a b) : p b.
variable a : Int.
theorem T (x : Int) : (q a x) → (p x).
    apply (Ax a).
    exact.
    done.
