/- The tactic search_mem_list defined at back.lean does
   not update the tactic_state. More importantly, it does not change
   the set of goals that need to be solved.
   It is also possible to write a very compact search_mem_list on top of the
   apply tactic. This version will create subgoals while searching for
   a proof of (a ∈ e). -/
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

/- The command `declare_trace` add a new trace.search_mem_list to Lean -/
declare_trace search_mem_list

/- In Lean, we can only reference a function 'f' while defining 'f' when we use
   recursive equation compiler. This is true also for meta definitions.
   Thus, we cannot write a tactic such as
       meta def f : tactic unit :=
       ... f ...
   that invokes itself but it is not defined using the equational compiler.
   We workaround this issue by defining it as
       meta def f : unit → tactic unit
       | () := ... f () ...
-/

meta def mk_mem_list_rec : unit → tactic unit
| () :=
when_tracing `search_mem_list (do t ← target, f ← pp t, trace (to_fmt "search " ++ f))
>> (assumption
    <|>
    /- The notation `[t] allows us to use the Lean "tactic interactive mode" inside regular tactic.
       In the following example `[apply in_left] is syntax sugar for
           tactic.interactive.apply `(in_left)
    -/
    (`[apply in_left] >> mk_mem_list_rec ())
    <|>
    (`[apply in_right] >> mk_mem_list_rec ())
    <|>
    (`[apply in_head])
    <|>
    (`[apply in_tail] >> mk_mem_list_rec ()))
/- The tactic `now` fails if we still have goals to be solved -/
>> done

meta def mk_mem_list : tactic unit :=
solve1 (mk_mem_list_rec ())

set_option trace.search_mem_list true

example (a b c : nat) : a ∈ [b, c] ++ [b, a, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, a+0, b] :=
by mk_mem_list

example (a b c : nat) : a ∈ [b, c] ++ [b, c, c] ++ [b, a+0, b] :=
by mk_mem_list

example (a b c : nat) (l : list nat) : a ∈ l → a ∈ [b, c] ++ b::l :=
begin intros, mk_mem_list end

example (a b c : nat) (l₁ l₂ : list nat) : a ∈ l₁ → a ∈ b::b::c::l₂ ++ b::c::l₁ ++ [c, c, b] :=
begin intros, mk_mem_list end
