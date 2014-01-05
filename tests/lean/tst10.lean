Variable a : Bool
Variable b : Bool
-- Conjunctions
print a && b
print a && b && a
print a /\ b
print a ∧ b
print (and a b)
print and a b
-- Disjunctions
print a || b
print a \/ b
print a ∨ b
print (or a b)
print or a (or a b)
-- Simple Formulas
print a => b => a
Check a => b
Eval a => a
Eval true => a
-- Simple proof
Axiom H1 : a
Axiom H2 : a => b
Check @MP
print MP H2 H1
Check MP H2 H1
