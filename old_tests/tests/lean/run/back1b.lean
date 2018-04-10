/- In this example, we demonstrate how to add tracing to
   the tactic implemented in the file back.lean.
   We also use quotations to build terms. -/
open list expr tactic

universe variable u

/- We change the implicit arguments of in_tail and in_head.
   The goal is to allow us to create in_tail and in_head application using
   quotation without having information about the expected type. -/
lemma in_tail  {α : Type u} {a : α} (b : α) {l : list α}      : a ∈ l → a ∈ b::l :=
mem_cons_of_mem _

lemma in_head  {α : Type u} (a : α) (l : list α)              : a ∈ a::l :=
mem_cons_self _ _

lemma in_left  {α : Type u} {a : α}   {l : list α} (r : list α) : a ∈ l → a ∈ l ++ r :=
mem_append_left _

lemma in_right {α : Type u} {a : α}   (l : list α) {r : list α} : a ∈ r → a ∈ l ++ r :=
mem_append_right _

meta def match_cons (e : expr) : tactic (expr × expr) :=
do [_, h, t] ← match_app_of e `list.cons | failed, return (h, t)

meta def match_append (e : expr) : tactic (expr × expr) :=
do [_, _, l, r] ← match_app_of e `has_append.append | failed, return (l, r)

/- The command `declare_trace` add a new trace.search_mem_list to Lean -/
declare_trace search_mem_list

/- The tactic (search_mem_list a e) tries to build a proof-term for (a ∈ e). -/
meta def search_mem_list : expr → expr → tactic expr
| a e :=
/- The tactic (when_tracing id tac) executes the tactic `tac` if
   the option trace.id is set to true. -/
when_tracing `search_mem_list (do
   /- The tactic (pp e) pretty-prints the given expression.
      It returns the formatting object for `e`. It will
      format it with respect to the local context and environment associated
      with the main goal. -/
   a_fmt ← pp a,
   e_fmt ← pp e,
   trace (to_fmt "search " ++ a_fmt ++ to_fmt " in " ++ e_fmt))
>>
(do m ← mk_app `has_mem.mem [a, e], find_assumption m)
<|>
/-
  A quoted term `(t) is a pre-term. The tactic to_expr elaborates a pre-term
  with respect to the current main goal. The notation %%t is an anti-quotation.
-/
(do (l, r) ← match_append e, h ← search_mem_list a l, to_expr ``(in_left %%r %%h))
<|>
(do (l, r) ← match_append e, h ← search_mem_list a r, to_expr ``(in_right %%l %%h))
<|>
(do (b, t) ← match_cons e, is_def_eq a b, to_expr ``(in_head %%b %%t))
<|>
(do (b, t) ← match_cons e, h ← search_mem_list a t, to_expr ``(in_tail %%b %%h))

/- The tactic mk_mem_list tries to close the current goal using search_mem_list
   if it is of the form (a ∈ e).
   We can view mk_mem_list as an "overloaded lemma" as described by Gonthier et al.
   in the paper "How to make ad hoc proof automation less ad hoc"
-/
meta def mk_mem_list : tactic unit :=
do t ← target,
   [_, _, _, a, e] ← match_app_of t `has_mem.mem | failed,
   search_mem_list a e >>= exact

example (a b c : nat) : a ∈ [b, c] ++ [b, a, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, a+0, b] :=
by mk_mem_list

/- We can enable/disable the tracing messages
   using the set_option command.
   Later, we demonstrate how to use the Lean debugger and VM monitor. -/
set_option trace.search_mem_list true

example (a b c : nat) : a ∈ [b, c] ++ [b, c, c] ++ [b, a+0, b] :=
by mk_mem_list

set_option trace.search_mem_list false

example (a b c : nat) (l : list nat) : a ∈ l → a ∈ [b, c] ++ b::l :=
by tactic.intros >> mk_mem_list

example (a b c : nat) (l : list nat) : a ∈ l → a ∈ b::b::c::l ++ [c, c, b] :=
by tactic.intros >> mk_mem_list

/- We can use mk_mem_list nested in our proofs -/
example (a b c : nat) (l₁ l₂ : list nat) : (a ∈ l₁ ∨ a ∈ l₂) → a ∈ b::l₂ ∨ a ∈ b::c::l₁ ++ [b, c]
| (or.inl h) := or.inr (by mk_mem_list)
| (or.inr r) := or.inl (by mk_mem_list)

/- We can prove the same theorem using just tactics. -/
example (a b c : nat) (l₁ l₂ : list nat) : (a ∈ l₁ ∨ a ∈ l₂) → a ∈ b::l₂ ∨ a ∈ b::c::l₁ ++ [b, c] :=
begin
  intro h, cases h,
  {apply or.inr, mk_mem_list},
  {apply or.inl, mk_mem_list}
end
