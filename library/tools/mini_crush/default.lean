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

meta def add_relevant_eqns (s : simp_lemmas) : tactic simp_lemmas :=
do fns ← collect_revelant_fns,
   fns.mfold s (λ fn s, get_eqn_lemmas_for tt fn >>= mfoldl simp_lemmas.add_simp s)

meta def add_relevant_eqns_h (hs : hinst_lemmas) : tactic hinst_lemmas :=
do fns ← collect_revelant_fns,
   fns.mfold hs (λ fn hs, get_eqn_lemmas_for tt fn >>= mfoldl (λ hs d, hs.add <$> hinst_lemma.mk_from_decl d) hs)

/- Collect terms that are inductive datatypes -/

meta def is_inductive (e : expr) : tactic bool :=
do type ← infer_type e,
   C    ← return type.get_app_fn,
   env  ← get_env,
   return $ C.is_constant && env.is_inductive C.const_name

meta def collect_inductive_aux : expr_set → expr → tactic expr_set
| S e :=
  if S.contains e then return S
  else do
    new_S ← mcond (is_inductive e) (return $ S.insert e) (return S),
    match e with
    | expr.app _ _    := fold_explicit_args e new_S collect_inductive_aux
    | expr.pi _ _ d b := if e.is_arrow then collect_inductive_aux S d >>= flip collect_inductive_aux b else return new_S
    | _               := return new_S
    end

meta def collect_inductive : expr → tactic expr_set :=
collect_inductive_aux mk_expr_set

meta def collect_inductive_from_target : tactic (list expr) :=
do S ← target >>= collect_inductive,
   return $ list.qsort (λ e₁ e₂, size e₁ < size e₂) $ S.to_list

meta def collect_inductive_hyps : tactic (list expr) :=
local_context >>= mfoldl (λ r h, mcond (is_inductive h) (return $ h::r) (return r)) []

/- Induction -/

meta def try_induction_aux (cont : expr → tactic unit) : list expr → tactic unit
| []      := failed
| (e::es) := (step (induction e); cont e; done) <|> try_induction_aux es

meta def try_induction (cont : expr → tactic unit) : tactic unit :=
focus1 $ collect_inductive_hyps >>= try_induction_aux cont

/- Trace messages -/

meta def report {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
when_tracing `mini_crush $ trace a

meta def report_failure (s : name) (e : option expr := none) : tactic unit :=
when_tracing `mini_crush $
  match e with
  | none   := trace ("FAILED '" ++ to_string s ++ "' at")
  | some e := (do p ← pp e, trace (to_fmt "FAILED '" ++ to_fmt s ++ "' processing '" ++ p ++ to_fmt "' at")) <|> trace ("FAILED '" ++ to_string s ++ "' at")
  end
  >> trace_state >> trace "--------------"

/- Simple tactic -/
meta def close_aux (hs : hinst_lemmas) : tactic unit :=
    triv           <|> reflexivity reducible <|> contradiction
<|> try_for 1000 (rsimp {} hs >> done) <|> try_for 1000 reflexivity

meta def close (hs : hinst_lemmas) (s : name) (e : option expr) : tactic unit :=
    done
<|> close_aux hs
<|> report_failure s e >> failed

meta def simple (s : simp_lemmas) (hs : hinst_lemmas) (cfg : simp_config) (s_name : name) (h : option expr) : tactic unit :=
simph_intros_using s cfg >> close hs s_name h

/- Best first search -/

meta def snapshot := tactic_state

meta def save : tactic snapshot :=
tactic.read

meta def restore : snapshot → tactic unit :=
tactic.write

meta def try_snapshots {α} (cont : α → tactic unit) : list (α × snapshot) → tactic unit
| []           := failed
| ((a, s)::ss) := (restore s >> cont a >> done) <|> try_snapshots ss

meta def search {α} (max_depth : nat) (act : nat → α → tactic (list (α × snapshot))) : nat → α → tactic unit
| n s := do
  done
  <|>
  if n > max_depth then when_tracing `mini_crush (trace "max depth reached" >> trace_state) >> failed
  else all_goals $ try intros >> act n s >>= try_snapshots (search (n+1))

meta def try_and_save {α} (t : tactic α) : tactic (option (α × nat × snapshot)) :=
do {
  s     ← save,
  a     ← t,
  new_s ← save,
  n     ← num_goals,
  restore s,
  return (a, n, new_s)
} <|> return none

meta def try_all_aux {α β : Type} (ts : α → tactic β) : list α → list (α × β × nat × snapshot) → tactic (list (α × β × nat × snapshot))
| []      [] := failed
| []      rs := return rs.reverse
| (v::vs) rs := do
  r ← try_and_save (ts v),
  match r with
  | some (b, 0, s) := return [(v, b, 0, s)]
  | some (b, n, s) := try_all_aux vs ((v, b, n, s)::rs)
  | none           := try_all_aux vs rs
  end

meta def try_all {α β : Type} (ts : α → tactic β) (vs : list α) : tactic (list (α × β × nat × snapshot)) :=
try_all_aux ts vs []

/- Destruct and simplify -/

meta def try_cases (s : simp_lemmas) (hs : hinst_lemmas) (cfg : simp_config) (s_name : name) : tactic (list (unit × snapshot)) :=
do es ← collect_inductive_from_target,
   rs ← try_all (λ e, do
     when_tracing `mini_crush (do p ← pp e, trace (to_fmt "Splitting on '" ++ p ++ to_fmt "'")),
     cases e; simph_intros_using s cfg; try (close_aux hs)) es,
   rs ← return $ flip list.qsort rs (λ ⟨e₁, _, n₁, _⟩ ⟨e₂, _, n₂, _⟩, if n₁ ≠ n₂ then n₁ < n₂ else size e₁ < size e₂),
   return $ rs.map (λ ⟨_, _, _, s⟩, ((), s))


meta def search_cases (max_depth : nat) (s : simp_lemmas) (hs : hinst_lemmas) (cfg : simp_config) (s_name : name) : tactic unit :=
search max_depth (λ d _, do
  when_tracing `mini_crush (trace ("Depth #" ++ to_string d)),
  try_cases s hs cfg s_name) 0 ()

/- Strategies -/

meta def mk_simp_lemmas (s : option simp_lemmas := none) : tactic simp_lemmas :=
match s with
| some s := return s
| none   := simp_lemmas.mk_default >>= add_relevant_eqns
end

meta def mk_hinst_lemmas (s : option hinst_lemmas := none) : tactic hinst_lemmas :=
match s with
| some s := return s
| none   := add_relevant_eqns_h hinst_lemmas.mk
end

meta def strategy_1 (cfg : simp_config := {}) (s : option simp_lemmas := none) (hs : option hinst_lemmas := none) (s_name : name := "strategy 1") : tactic unit :=
do s  ← mk_simp_lemmas s,
   hs ← mk_hinst_lemmas hs,
   try_induction (λ h, simple s hs cfg s_name (some h))

meta def strategy_2_aux (cfg : simp_config) (hs : hinst_lemmas) : simp_lemmas → tactic unit
| s :=
  do s ← simp_intro_aux cfg tt s tt [`_], -- Introduce next hypothesis
     h ← list.ilast <$> local_context,
     try $ solve1 (mwhen (is_inductive h) $ induction' h; simple s hs cfg "strategy 2" (some h)),
     done <|> strategy_2_aux s

meta def strategy_2 (cfg : simp_config := {}) (s : option simp_lemmas := none) (hs : option hinst_lemmas := none) : tactic unit :=
do s ← mk_simp_lemmas s,
   hs ← mk_hinst_lemmas hs,
   strategy_2_aux cfg hs s

meta def strategy_3 (cfg : simp_config := {}) (max_depth : nat := 1) (s : option simp_lemmas := none) (hs : option hinst_lemmas := none) : tactic unit :=
do s ← mk_simp_lemmas s,
   hs ← mk_hinst_lemmas hs,
   try_induction (λ h, try (simph_intros_using s cfg); try (close_aux hs); (done <|> search_cases max_depth s hs cfg "strategy 3"))

end mini_crush

open tactic mini_crush

meta def mini_crush (cfg : simp_config := {}) (max_depth : nat := 1) :=
do s  ← mk_simp_lemmas,
   hs ← mk_hinst_lemmas,
strategy_1 cfg (some s) (some hs)
<|>
strategy_2 cfg (some s) (some hs)
<|>
strategy_3 cfg max_depth (some s) (some hs)
