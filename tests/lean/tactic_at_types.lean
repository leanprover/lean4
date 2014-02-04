import tactic
set_option simplifier::heq true
set_option pp::implicit true -- to be able to parse output produced by Lean
variable vec : Nat → Type
variables n m : Nat
variable v1 : vec (n + m)
variable v2 : vec (m + n)
rewrite_set S
add_rewrite Nat::add_comm Nat::add_assoc Nat::add_left_comm eq_id : S
axiom Ax1    : v1 = cast (by simp S) v2
variable Ax2 : v2 = cast (by simp S) v1

variable concat {n m : Nat} (v : vec n) (w : vec m) : vec (n + m)
infixl   65 ; : concat
variable empty : vec 0
axiom    concat_assoc {n1 n2 n3 : Nat} (v1 : vec n1) (v2 : vec n2) (v3 : vec n3) :
             (v1 ; v2) ; v3 = cast (by simp S) (v1 ; (v2 ; v3))
add_rewrite Nat::add_zeror Nat::add_zerol : S
axiom    concat_empty {n : Nat} (v : vec n) :
             v ; empty = cast (by simp S) v

theorem T1 (n m : Nat) (v : vec (n + m)) (w : vec (m + n)) (H : v = cast (by simp S) w) :
                  w = cast (by simp S) v
:= (by simp S)
