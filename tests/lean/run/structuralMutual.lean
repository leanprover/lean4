namespace MutualIndNonMutualFun

mutual
inductive A
  | self : A → A
  | other : B → A
  | empty
inductive B
  | self : B → B
  | other : A → B
  | empty
end

/--
error: argument #1 cannot be used for structural recursion
  Structural non-mutual recursion over a mutual inductive data type is not supported
-/
#guard_msgs in
def A.self_size : A → Nat
  | .self a => a.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x

/--
error: argument #1 cannot be used for structural recursion
  Structural non-mutual recursion over a mutual inductive data type is not supported
-/
#guard_msgs in
def B.self_size : B → Nat
  | .self b => b.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x

mutual
def A.size : A → Nat
  | .self a => a.size + 1
  | .other b => b.size + 1
  | .empty => 0
termination_by structurally x => x
def B.size : B → Nat
  | .self b => b.size + 1
  | .other a => a.size + 1
  | .empty => 0
termination_by structurally x => x
end

mutual
def A.subs : (a : A) → (Fin a.size → A ⊕ B)
  | .self a => Fin.lastCases (.inl a) (a.subs)
  | .other b => Fin.lastCases (.inr b) (b.subs)
  | .empty => Fin.elim0
termination_by structurally x => x
def B.subs : (b : B) → (Fin b.size → A ⊕ B)
  | .self b => Fin.lastCases (.inr b) (b.subs)
  | .other a => Fin.lastCases (.inl a) (a.subs)
  | .empty => Fin.elim0
termination_by structurally x => x
end

theorem A_size_eq1 (a : A) : (A.self a).size = a.size + 1 := rfl
theorem A_size_eq2 (b : B) : (A.other b).size = b.size + 1 := rfl
theorem A_size_eq3 : A.empty.size = 0  := rfl
theorem B_size_eq1 (b : B) : (B.self b).size = b.size + 1 := rfl
theorem B_size_eq2 (a : A) : (B.other a).size = a.size + 1 := rfl
theorem B_size_eq3 : B.empty.size = 0  := rfl

end MutualIndNonMutualFun
