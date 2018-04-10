universe variable u

constant in_tail  {α : Type u} {a : α}   (b : α)      {l : list α} : a ∈ l → a ∈ b::l
constant in_head  {α : Type u} (a : α)   (l : list α)              : a ∈ a::l
constant in_left  {α : Type u} {a : α}   {l : list α} (r : list α) : a ∈ l → a ∈ l ++ r
constant in_right {α : Type u} {a : α}   (l : list α) {r : list α} : a ∈ r → a ∈ l ++ r

open expr tactic

declare_trace search_mem_list

meta def match_append (e : expr) : tactic (expr × expr) :=
do [_, _, l, r] ← match_app_of e ``has_append.append | failed, return (l, r)

meta def match_cons (e : expr) : tactic (expr × expr) :=
do [_, a, t] ← match_app_of e ``list.cons | failed, return (a, t)

meta def match_mem (e : expr) : tactic (expr × expr) :=
do [_, _, _, a, t] ← match_app_of e ``has_mem.mem | failed, return (a, t)

meta def search_mem_list : expr → expr → tactic expr
| a e := when_tracing `search_mem_list (do f₁ ← pp a, f₂ ← pp e, trace (to_fmt "search " ++ f₁ ++ to_fmt " in " ++ f₂)) >>
(do m ← to_expr ``(%%a ∈ %%e), find_assumption m)
<|>
(do (l, r) ← match_append e, h ← search_mem_list a l, to_expr ``(in_left %%r %%h))
<|>
(do (l, r) ← match_append e, h ← search_mem_list a r, to_expr ``(in_right %%l %%h))
<|>
(do (b, t) ← match_cons e, is_def_eq a b,             to_expr ``(in_head %%b %%t))
<|>
(do (b, t) ← match_cons e, h ← search_mem_list a t,   to_expr ``(in_tail %%b %%h))

meta def mk_mem_list : tactic unit :=
do t ← target,
   (a, l) ← match_mem t,
   search_mem_list a l >>= exact

example (a b c : nat) : a ∈ [b, c] ++ [b, a, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, a+0, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, c, c] ++ [b, a+0, b] :=
by mk_mem_list

example (a b c : nat) (l : list nat) : a ∈ l → a ∈ [b, c] ++ b::l :=
by tactic.intros >> mk_mem_list

set_option trace.search_mem_list true

lemma ex1 (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
by tactic.intros >> mk_mem_list

set_option trace.smt.ematch true

/- Using ematching -/
lemma ex2 (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
begin [smt]
  intros,
  add_lemma [in_left, in_right, in_head, in_tail],
  iterate {ematch} -- It will loop if there is a matching loop
end
