/- Lean also support E-matching: a heuristic lemma instantiation procedure
   that is available in many SMT solvers.
   Goals such as mk_mem_list can also be discharged using heuristic instantiation. -/
open list tactic

universe variable u
lemma in_tail  {α : Type u} {a : α} (b : α) {l : list α}        : a ∈ l → a ∈ b::l   := mem_cons_of_mem _
lemma in_head  {α : Type u} (a : α) (l : list α)                : a ∈ a::l           := mem_cons_self _ _
lemma in_left  {α : Type u} {a : α}   {l : list α} (r : list α) : a ∈ l → a ∈ l ++ r := mem_append_left _
lemma in_right {α : Type u} {a : α}   (l : list α) {r : list α} : a ∈ r → a ∈ l ++ r := mem_append_right _

/- Using ematching -/
example (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
begin [smt]
  intros,
  iterate { ematch_using [in_left, in_right, in_head, in_tail], try {close} }
end

/- We mark lemmas for ematching. -/
attribute [ematch] in_left in_right in_head in_tail

example (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
begin [smt]
  intros,
  iterate {ematch, try {close}}
end

example (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
begin [smt]
  intros, eblast
end

/- The following example is not provable -/
example (a b c : nat) (l₁ l₂ : list nat) : a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
begin [smt]
  intros,
  iterate {ematch, try {close}},
  admit /- finish the proof admiting the goal -/
end
