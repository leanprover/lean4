module

/-! Regression tests for #15226: export complete axiom sets for inductive blocks. -/

public noncomputable def pick : Nat := Classical.choice ⟨0⟩

public structure S9 where
  x : Fin (pick + 1)

mutual
public inductive M1 where
  | mk : Fin (pick + 1) → M2 → M1
public inductive M2 where
  | mk : M1 → M2
end

public inductive Nested where
  | mk : Fin (pick + 1) → List Nested → Nested

public theorem usesS9 (_ : S9) : True := trivial

/-- info: 'S9' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms S9

/-- info: 'M2' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms M2

/-- info: 'Nested' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Nested
