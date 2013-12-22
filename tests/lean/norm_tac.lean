Variable vector (A : Type) (sz : Nat) : Type
Variable read {A : Type} {sz : Nat} (v : vector A sz) (i : Nat) (H : i < sz) : A
Variable V1 : vector Int 10
Definition D := read V1 1 (by trivial_tac)
Variable b : Bool
Definition a := b
Theorem T : b => a := (by (** imp_tac() .. normalize_tac() .. assumption_tac() **))
