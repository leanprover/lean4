Variable a : Bool
Variable b : Bool
(* Conjunctions *)
Show a && b
Show a && b && a
Show a /\ b
Show a ∧ b
Show (and a b)
Show and a b
(* Disjunctions *)
Show a || b
Show a \/ b
Show a ∨ b
Show (or a b)
Show or a (or a b)
(* Simple Formulas *)
Show a => b => a
Check a => b
Eval a => a
Eval true => a
(* Simple proof *)
Axiom H1 : a
Axiom H2 : a => b
Check MP::explicit
Show MP H2 H1
Check MP H2 H1
