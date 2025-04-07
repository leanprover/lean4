---

example {P Q : Prop} [Decidable P] [Decidable Q] : (decide P || decide Q) = decide (P ∨ Q) := by grind

---

@[grind] theorem eq_head_or_mem_tail_of_mem_cons {a b : α} {l : List α} :
    a ∈ b :: l → a = b ∨ a ∈ l := List.mem_cons.mp

attribute [grind] List.mem_cons_self, List.mem_cons_of_mem

-- This succeeds:
example [DecidableEq α] {l : List α} :
    (y ∈ a :: l) = (y = a) ∨ y ∈ l := by
  grind


-- but inserting some `decide`s fails:
example [BEq α] [LawfulBEq α] {l : List α} :
    decide (y ∈ a :: l) = (y == a || decide (y ∈ l)) := by
  grind
