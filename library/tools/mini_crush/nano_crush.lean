/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

We implement a crush-like strategy using simplifier,
SMT gadgets, and robust simplifier.

This is just a demo.
-/
namespace nano_crush
open tactic

meta def size (e : expr) : nat :=
e.fold 1 (λ e _ n, n+1)

/- Collect relevant functions -/

meta def is_auto_construction : name → bool
| (name.mk_string "brec_on" p)      := tt
| (name.mk_string "cases_on" p)     := tt
| (name.mk_string "rec_on" p)       := tt
| (name.mk_string "no_confusion" p) := tt
| (name.mk_string "below" p)        := tt
| _                                 := ff

meta def is_relevant_fn (n : name) : tactic bool :=
do env ← get_env,
   if ¬env.is_definition n ∨ is_auto_construction n then return ff
   else if env.in_current_file n then return tt
   else in_open_namespaces n

meta def collect_revelant_fns_aux : name_set → expr → tactic name_set
| s e :=
e.mfold s $ λ t _ s,
  match t with
  | expr.const c _ :=
    if s.contains c then return s
    else mcond (is_relevant_fn c)
      (do new_s ← return $ if c.is_internal then s else s.insert c,
          d     ← get_decl c,
          collect_revelant_fns_aux new_s d.value)
      (return s)
  | _              := return s
  end

meta def collect_revelant_fns : tactic name_set :=
do ctx ← local_context,
   s₁  ← ctx.mfoldl (λ s e, infer_type e >>= collect_revelant_fns_aux s) mk_name_set,
   target >>= collect_revelant_fns_aux s₁

meta def add_relevant_eqns (hs : hinst_lemmas) : tactic hinst_lemmas :=
do fns ← collect_revelant_fns,
   fns.mfold hs (λ fn hs, get_eqn_lemmas_for tt fn >>= mfoldl (λ hs d, hs.add <$> hinst_lemma.mk_from_decl d) hs)

/- Collect terms that are inductive datatypes -/

meta def is_inductive (e : expr) : tactic bool :=
do type ← infer_type e,
   C    ← return type.get_app_fn,
   env  ← get_env,
   return $ C.is_constant && env.is_inductive C.const_name

open expr

meta def collect_inductive_aux : expr_set → expr → tactic expr_set
| S e :=
  if S.contains e then return S
  else do
    new_S ← mcond (is_inductive e) (return $ S.insert e) (return S),
    match e with
    | app _ _    := fold_explicit_args e new_S collect_inductive_aux
    | pi _ _ d b := if e.is_arrow then collect_inductive_aux S d >>= flip collect_inductive_aux b else return new_S
    | _          := return new_S
    end

meta def collect_inductive : expr → tactic expr_set :=
collect_inductive_aux mk_expr_set

open list

meta def collect_inductive_from_target : tactic (list expr) :=
do S ← target >>= collect_inductive,
   return $ qsort (λ x y, size x < size y) S.to_list

meta def collect_inductive_hyps : tactic (list expr) :=
local_context >>= mfoldl (λ r h, mcond (is_inductive h) (return $ h::r) (return r)) []

/- Induction -/

meta def try_list_aux {α} (s : tactic_state) (tac : α → tactic unit) : list α → tactic unit
| []      := failed
| (e::es) := (write s >> tac e >> done) <|> try_list_aux es

meta def try_list {α} (tac : α → tactic unit) (es : list α) : tactic unit :=
do s ← read, try_list_aux s tac es

meta def induct (tac : tactic unit) : tactic unit :=
collect_inductive_hyps >>= try_list (λ e, induction' e; tac)

meta def split (tac : tactic unit) : tactic unit :=
collect_inductive_from_target >>= try_list (λ e, cases e; tac)

meta def search (tac : tactic unit) : nat → tactic unit
| 0     := all_goals tac >> done
| (d+1) := all_goals (try tac) >> (done <|> split (search d))

meta def rsimp' (hs : hinst_lemmas) : tactic unit :=
rsimp {} hs

meta def mk_relevant_lemmas : tactic hinst_lemmas :=
add_relevant_eqns hinst_lemmas.mk

end nano_crush

open tactic nano_crush

meta def nano_crush (depth : nat := 1) :=
do hs ← mk_relevant_lemmas,
   induct $ search (rsimp' hs) depth
