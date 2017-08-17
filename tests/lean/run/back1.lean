/- In this example, we show how to write a simple tactic for performing
   backward chaining.
   The tactic builds list membership proofs for goals such as
        a ∈ [b, c] ++ [b, a, b]
-/
open list expr tactic

universe variable u

/- The tactic uses the following 4 theorems from the standard library.
   Here, we just give them shorter names, and state their types. -/
lemma in_tail  {α : Type u} {a b : α} {l : list α}              : a ∈ l → a ∈ b::l :=
mem_cons_of_mem _

lemma in_head  {α : Type u} {a : α}   {l : list α}              : a ∈ a::l :=
mem_cons_self _ _

lemma in_left  {α : Type u} {a : α}   {l : list α} (r : list α) : a ∈ l → a ∈ l ++ r :=
mem_append_left _

lemma in_right {α : Type u} {a : α}   (l : list α) {r : list α} : a ∈ r → a ∈ l ++ r :=
mem_append_right _

/- Now, we define two helper tactics for matching cons/append-applications.
   For example, (match_cons e) succeeds and return a pair (h, t) iff
   it is of the form (h::t).
-/
meta def match_cons (e : expr) : tactic (expr × expr) :=
/- The tactic (match_app_of e `list.cons) succeeds if e is a list-cons application,
   and returns a list of arguments.
   The notation `list.cons is a "name quotation".
   It is a shorthand for
      (name.mk_string "cons" (name.mk_string "list" name.anonymous))
   We can pattern match in the do-notation. This definition is equivalent to
   do args ← match_app_of e `list.cons,
      match args with
      | [_, h, t] := return (h, t)
      | _         := failed
      end
  It is quite convenient when we have many nested patterns.
-/
do [_, h, t] ← match_app_of e `list.cons | failed, return (h, t)

meta def match_append (e : expr) : tactic (expr × expr) :=
do [_, _, l, r] ← match_app_of e `has_append.append | failed, return (l, r)

/- The tactic (search_mem_list a e) tries to build a proof-term for (a ∈ e). -/
meta def search_mem_list : expr → expr → tactic expr
| a e :=
/- First, we check if there is an assumption with type (a ∈ e).
   We use the helper tactic mk_app. It infers implicit arguments using type inference and
   type class resolution. Note that the type of mem is:
      Π {α : Type u₁} {γ : Type u₁ → Type u₂} [s : has_mem α γ], α → γ α → Prop
   It has 2 universe variables and 3 implicit arguments, where one of them is a type class instance.
   So, it is quite inconvenient to create mem-applications by hand. The tactic mk_app
   hides this complexity.
   The tactic (find_assumption m) succeeds if there is a hypothesis (h : m) in
   the local context of the main goal. It is implemented in Lean, and we can
   jump to its definition by using `M-.` (on Emacs) and `F12` (on VS Code).
   On VS Code, we can also "peek" on its definition by typing (Alt-F12).
 -/
(do m ← mk_app `has_mem.mem [a, e], find_assumption m)
<|>
/- If e is of the form l++r, then we try to build a proof for (a ∈ l),
   if we succeed, we built a proof for (a ∈ l++r) using the lemma in_left. -/
(do (l, r) ← match_append e, h ← search_mem_list a l, mk_app `in_left [l, r, h])
<|>
(do (l, r) ← match_append e, h ← search_mem_list a r, mk_app `in_right [l, r, h])
<|>
(do (b, t) ← match_cons e, is_def_eq a b, mk_app `in_head [b, t])
<|>
(do (b, t) ← match_cons e, h ← search_mem_list a t, mk_app `in_tail [a, b, t, h])

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

example (a b c : nat) : a ∈ [b, c] ++ [b, c, c] ++ [b, a+0, b] :=
by mk_mem_list

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
