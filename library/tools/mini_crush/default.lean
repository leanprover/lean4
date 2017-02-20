/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

We implement a crush-like strategy using simplifier,
SMT gadgets, and robust simplifier.

This is just a demo.
-/
declare_trace mini_crush

namespace mini_crush
open tactic

meta def size (e : expr) : nat :=
e^.fold 1 (λ e _ n, n+1)

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
   if ¬env^.is_definition n ∨ is_auto_construction n then return ff
   else if env^.in_current_file n then return tt
   else in_open_namespaces n

meta def collect_revelant_fns_aux : name_set → expr → tactic name_set
| s e :=
e^.mfold s $ λ t _ s,
  match t with
  | expr.const c _ :=
    if s^.contains c then return s
    else mcond (is_relevant_fn c)
      (do new_s ← return $ if c^.is_internal then s else s^.insert c,
          d     ← get_decl c,
          collect_revelant_fns_aux new_s d^.value)
      (return s)
  | _              := return s
  end

meta def collect_revelant_fns : tactic name_set :=
do ctx ← local_context,
   s₁  ← mfoldl (λ s e, infer_type e >>= collect_revelant_fns_aux s) mk_name_set ctx,
   target >>= collect_revelant_fns_aux s₁

meta def add_relevant_eqns (s : simp_lemmas) : tactic simp_lemmas :=
do fns ← collect_revelant_fns,
   fns^.mfold s (λ fn s, get_eqn_lemmas_for tt fn >>= mfoldl simp_lemmas.add_simp s)

/- Collect terms that are inductive datatypes -/

meta def is_inductive (e : expr) : tactic bool :=
do type ← infer_type e,
   C    ← return type^.get_app_fn,
   env  ← get_env,
   return $ C^.is_constant && env^.is_inductive C^.const_name

meta def collect_inductive_aux : expr_set → expr → tactic expr_set
| S e :=
  if S^.contains e then return S
  else do
    new_S ← mcond (is_inductive e) (return $ S^.insert e) (return S),
    match e with
    | expr.app _ _    := fold_explicit_args e new_S collect_inductive_aux
    | expr.pi _ _ d b := if e^.is_arrow then collect_inductive_aux S d >>= flip collect_inductive_aux b else return new_S
    | _               := return new_S
    end

meta def collect_inductive : expr → tactic expr_set :=
collect_inductive_aux mk_expr_set

meta def collect_inductive_from_target : tactic (list expr) :=
do S ← target >>= collect_inductive,
   return $ list.qsort (λ e₁ e₂, size e₁ < size e₂) $ S^.to_list

meta def collect_inductive_hyps : tactic (list expr) :=
local_context >>= mfoldl (λ r h, mcond (is_inductive h) (return $ h::r) (return r)) []

/- Induction -/

meta def try_induction_aux (cont : expr → tactic unit) : list expr → tactic unit
| []      := failed
| (e::es) := (step (induction e); cont e; now) <|> try_induction_aux es

meta def try_induction (cont : expr → tactic unit) : tactic unit :=
focus1 $ collect_inductive_hyps >>= try_induction_aux cont

meta def report {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
when_tracing `mini_crush $ trace a

meta def report_failure (s : name) (e : option expr := none) : tactic unit :=
when_tracing `mini_crush $
  match e with
  | none   := trace ("FAILED '" ++ to_string s ++ "' at")
  | some e := (do p ← pp e, trace (to_fmt "FAILED '" ++ to_fmt s ++ "' processing '" ++ p ++ to_fmt "' at")) <|> trace ("FAILED '" ++ to_string s ++ "' at")
  end
  >> trace_state >> trace "--------------"

meta def close_or_fail (s : name) (e : option expr) : tactic unit :=
    now
<|> triv           <|> reflexivity reducible <|> contradiction
<|> (rsimp >> now) <|> try_for 1000 reflexivity
<|> (report_failure s e >> failed)

meta def simple (s : simp_lemmas) (cfg : simp_config) (s_name : name) (h : option expr) : tactic unit :=
simph_intros_using s cfg >> close_or_fail s_name h

meta def mk_simp_lemmas (s : option simp_lemmas := none) : tactic simp_lemmas :=
match s with
| some s := return s
| none   := simp_lemmas.mk_default >>= add_relevant_eqns
end

meta def strategy_1 (cfg : simp_config := {}) (s : option simp_lemmas := none) (s_name : name := "strategy 1") : tactic unit :=
do s ← mk_simp_lemmas s,
   try_induction (λ h, simple s cfg s_name (some h))

meta def strategy_2_aux (cfg : simp_config) : simp_lemmas → tactic unit
| s :=
  do s ← simp_intro_aux cfg tt s tt [`_], -- Introduce next hypothesis
     h ← list.ilast <$> local_context,
     try $ solve1 (mwhen (is_inductive h) $ induction' h; simple s cfg "strategy 2" (some h)),
     now <|> strategy_2_aux s

meta def strategy_2 (cfg : simp_config := {}) (s : option simp_lemmas := none) : tactic unit :=
do s ← mk_simp_lemmas s,
   strategy_2_aux cfg s

end mini_crush

open tactic mini_crush

meta def mini_crush (cfg : simp_config := {}) :=
do s ← mk_simp_lemmas,
strategy_1 cfg (some s)
<|>
strategy_2 cfg (some s)
