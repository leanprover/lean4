reset_grind_attrs%

example {P Q : Prop} [Decidable P] [Decidable Q] : (decide P || decide Q) = decide (P ∨ Q) := by grind

@[grind] theorem eq_head_or_mem_tail_of_mem_cons {a b : α} {l : List α} :
    a ∈ b :: l → a = b ∨ a ∈ l := List.mem_cons.mp

attribute [grind] List.mem_cons_self List.mem_cons_of_mem

example [DecidableEq α] {l : List α} :
    (y ∈ a :: l) = (y = a) ∨ y ∈ l := by -- This one is not `(y ∈ a :: l) = (y = a ∨ y ∈ l)`
  grind

example [DecidableEq α] {l : List α} :
    (y ∈ a :: l) = (y = a ∨ y ∈ l) := by
  grind

-- but inserting some `decide`s fails:
example [BEq α] [LawfulBEq α] {l : List α} :
    decide (y ∈ a :: l) = (y == a || decide (y ∈ l)) := by
  grind

example [BEq α] (a b : α) : (a == b && a == b) = (a == b) := by
  rw [Bool.eq_iff_iff]
  grind

example [BEq α] (a b : α) : (a == b && a == b) = (a == b) := by
  grind

example (a b : List Nat) : (a == b && b == a) = (a == b) := by
  grind
