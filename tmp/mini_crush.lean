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
  match r with
  | some (_, 0, s) := restore s >> return v /- done -/
  | _              := best_core vs (merge b (updt r v))
  end

meta def best {α} (vs : list α) (ts : α → smt_tactic unit) : smt_tactic α :=
best_core ts vs none

open tactic (pp)

def nrounds := 5

meta def close_easy : smt_tactic unit :=
all_goals (repeat_at_most nrounds (ematch >> try close))

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

meta def induction_and_close (e : expr) : smt_tactic unit :=
smt_tactic.induction e >> close_easy

meta def induction_best (es : list expr) : smt_tactic expr :=
best es induction_and_close

meta def expr_set := expr_map unit
meta def expr_set.mk := expr_map.mk unit
meta def expr_set.insert (S : expr_set) (e : expr) : expr_set :=
rb_map.insert S e ()

open expr tactic

meta def is_inductive (e : expr) : tactic bool :=
do type ← infer_type e,
   C    ← return type^.get_app_fn,
   env  ← get_env,
   return $ C^.is_constant && env^.is_inductive C^.const_name

open monad

meta def collect_inductive_aux : expr_set → expr → tactic expr_set
| S e :=
  if S^.contains e then return S
  else do
    new_S ← cond (is_inductive e) (return $ S^.insert e) (return S),
    if e^.is_app
    then fold_explicit_args e new_S collect_inductive_aux
    else return new_S

meta def collect_inductive : expr → tactic expr_set :=
collect_inductive_aux expr_set.mk

meta def collect_inductive_as_list : tactic (list expr) :=
do S ← target >>= collect_inductive, return $ S^.to_list^.for prod.fst

end mini_crush

/- Testing -/
open smt_tactic mini_crush tactic

lemma nil_append {α} (a : list α) : [] ++ a = a :=
begin [smt]
  collect_inductive_as_list >>= induction_best
end

attribute [ematch_lhs] nil_append

set_option trace.smt.ematch true
set_option trace.mini_crush true


example (a b c : list nat) : (a ++ []) ++ b = a ++ b :=
begin [smt]
  do { monad.mapm to_expr [`(b), `(a), `(c)] >>= destruct_best },

end
