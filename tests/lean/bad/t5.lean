Variable g {A : Type} (a : A) : A
Variable a : Int
Variable b : Int
Axiom H1 : a = b
(*
The following axiom fails to be elaborated because:
1- (g a) is actually (g _ a)
2- > is overloaded notation for Nat::gt, Int::gt and Real::gt
3- The current elaborator selects one of the overloads before
   the hole in (g _ a) is solved. Thus, it selects Nat::gt.
4- During elaboration, we transform (g _ a) into (g Int a),
   and a type error is detected.

The next elaborator should address this problem.
*)
Axiom H2 : (g a) > 0

(*
A possible workaround is to manually add the coercion in 0.
The coercion is called nat_to_int. We define the notation
_ i to make it easier to write
*)
Notation 100 _ i : nat_to_int
Axiom H2 : (g a) > 0i

Theorem T1 : (g b) > 0i := Subst (λ x, (g x) > 0i) H2 H1
Show Environment 2
