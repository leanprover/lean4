declare_trace mini_crush

namespace mini_crush
open smt_tactic

meta def snapshot := smt_state × tactic_state

meta def save : smt_tactic snapshot :=
smt_tactic.read

meta def restore : snapshot → smt_tactic unit :=
smt_tactic.write

meta def try_and_save {α} (t : smt_tactic α) : smt_tactic (option (α × nat × snapshot)) :=
do {
  s     ← save,
  a     ← t,
  new_s ← save,
  n     ← num_goals,
  restore s,
  return (a, n, new_s)
} <|> return none

meta def updt {α β} : option (α × nat × snapshot) → β → option (β × nat × snapshot)
| none             b := none
| (some (a, n, s)) b := some (b, n, s)

meta def merge {α} (o₁ o₂ : option (α × nat × snapshot)) : option (α × nat × snapshot) :=
match o₁, o₂ with
| none,              _                 := o₂
| _,                 none              := o₁
| (some (_, n₁, _)), (some (_, n₂, _)) := if n₂ < n₁ then o₂ else o₁
end

meta def best_core {α} (ts : α → smt_tactic unit) : list α → option (α × nat × snapshot) → smt_tactic α
| []      none             := failed
| []      (some (v, _, s)) := restore s >> return v
| (v::vs) b                := do
  r ← try_and_save (ts v),
  best_core vs (merge b (updt r v))

meta def best {α} (vs : list α) (ts : α → smt_tactic unit) : smt_tactic α :=
best_core ts vs none

open tactic (pp)

meta def close_easy : smt_tactic unit :=
all_goals (repeat_at_most 5 (ematch >> try close))

meta def destruct_and_close (e  : expr) : smt_tactic unit :=
destruct e >> close_easy

meta def destruct_best (es : list expr) : smt_tactic expr :=
do e ← best es $ λ e,
          when_tracing `mini_crush (do p ← pp e, trace (to_fmt "[mini_crush] Candidate: " ++ p))
       >> destruct_and_close e
       >> when_tracing `mini_crush (do n ← num_goals, trace ("[mini_crush] Num goals: " ++ to_string n)),
   when_tracing `mini_crush (do
     p ← pp e,
     tactic.trace (to_fmt "destructed: " ++ p)),
   return e

end mini_crush

/- Testing -/
open smt_tactic mini_crush

lemma nil_append {α} (a : list α) : [] ++ a = a :=
rfl

attribute [ematch_lhs] nil_append

set_option trace.smt.ematch true
set_option trace.mini_crush true


example (a b c : list nat) : (a ++ []) ++ b = a ++ b :=
begin [smt]
  do { monad.mapm to_expr [`(b), `(a), `(c)] >>= destruct_best },

end
