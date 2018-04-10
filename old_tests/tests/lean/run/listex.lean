universe variable u

constant in_tail  {α : Type u} {a b : α} {l : list α}              : a ∈ l → a ∈ b::l
constant in_head  {α : Type u} {a : α}   {l : list α}              : a ∈ a::l
constant in_left  {α : Type u} {a : α}   {l : list α} (r : list α) : a ∈ l → a ∈ l ++ r
constant in_right {α : Type u} {a : α}   (l : list α) {r : list α} : a ∈ r → a ∈ l ++ r

open expr tactic

meta def search_mem_list : expr → expr → tactic expr
| a e :=
(do m ← mk_app ``has_mem.mem [a, e], find_assumption m)
<|>
(do [_, _, l, r] ← match_app_of e ``has_append.append | failed, h ← search_mem_list a l, mk_app `in_left [l, r, h])
<|>
(do [_, _, l, r] ← match_app_of e ``has_append.append | failed, h ← search_mem_list a r, mk_app `in_right [l, r, h])
<|>
(do [_, b, t] ← match_app_of e ``list.cons | failed, is_def_eq a b, mk_app `in_head [b, t])
<|>
(do [_, b, t] ← match_app_of e ``list.cons | failed, h ← search_mem_list a t, mk_app `in_tail [a, b, t, h])

meta def mk_mem_list : tactic unit :=
do t ← target,
   [_, _, _, a, e] ← match_app_of t ``has_mem.mem | failed,
   search_mem_list a e >>= exact

example (a b c : nat) : a ∈ [b, c] ++ [b, a, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, a+0, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, c, c] ++ [b, a+0, b] :=
by mk_mem_list

example (a b c : nat) (l : list nat) : a ∈ l → a ∈ [b, c] ++ b::l :=
by tactic.intros >> mk_mem_list

example (a b c : nat) (l : list nat) : a ∈ l → a ∈ b::b::c::l ++ [c, c, b] :=
by tactic.intros >> mk_mem_list
