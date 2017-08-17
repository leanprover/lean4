/- Lean has a backward chaining tactic that can be configured using
   attributes. -/
open list tactic

universe variable u
lemma in_tail  {α : Type u} {a : α} (b : α) {l : list α}        : a ∈ l → a ∈ b::l   := mem_cons_of_mem _
lemma in_head  {α : Type u} (a : α) (l : list α)                : a ∈ a::l           := mem_cons_self _ _
lemma in_left  {α : Type u} {a : α}   {l : list α} (r : list α) : a ∈ l → a ∈ l ++ r := mem_append_left _
lemma in_right {α : Type u} {a : α}   (l : list α) {r : list α} : a ∈ r → a ∈ l ++ r := mem_append_right _

/- It is trivial to define mk_mem_list using backward chaining -/
attribute [intro] in_tail in_head in_left in_right

meta def mk_mem_list : tactic unit :=
solve1 (back_chaining)

example (a b c : nat) : a ∈ [b, c] ++ [b, a, b] :=
by mk_mem_list

set_option trace.tactic.back_chaining true

example (a b c : nat) : a ∈ [b, c] ++ [b, a, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, c, c] ++ [b, a, b] :=
by mk_mem_list

example (a b c : nat) (l : list nat) : a ∈ l → a ∈ [b, c] ++ b::l :=
begin intros, mk_mem_list end

example (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
begin intros, mk_mem_list end
