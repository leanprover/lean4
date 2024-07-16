
-- A refexive type, with multiple parameters to make sure
-- we get the order right

inductive N where
 | cons : (Nat -> Bool → N) -> N


-- set_option trace.Elab.definition.structural true
mutual
def f : N -> List Nat → List Bool → Nat
 | .cons a, _, _ => g (a 32 true) [true] [1] + 1
termination_by structural n => n
def g : N -> List Bool → List Nat → Nat
 | .cons a, _, _ => f (a 42 false) [1] [true] + 1
termination_by structural  n => n
end
