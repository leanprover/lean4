universe variable u

constant in_tail  {α : Type u} {a : α}   (b : α)      {l : list α} : a ∈ l → a ∈ b::l
constant in_head  {α : Type u} (a : α)   (l : list α)              : a ∈ a::l
constant in_left  {α : Type u} {a : α}   {l : list α} (r : list α) : a ∈ l → a ∈ l ++ r
constant in_right {α : Type u} {a : α}   (l : list α) {r : list α} : a ∈ r → a ∈ l ++ r

open expr tactic

local attribute [intro] in_tail in_head in_left in_right

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
by tactic.intros >> mk_mem_list

example (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
by tactic.intros >> mk_mem_list
