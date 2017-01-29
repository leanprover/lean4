/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .clause_ops
import .prover_state .misc_preprocessing
open expr list tactic monad decidable

universe variable u

namespace super

meta def try_option {a : Type u} (tac : tactic a) : tactic (option a) :=
lift some tac <|> return none

private meta def normalize : expr → tactic expr | e := do
e' ← whnf_core transparency.reducible e,
args' ← monad.for e'^.get_app_args normalize,
return $ app_of_list e'^.get_app_fn args'

meta def inf_normalize_l (c : clause) : tactic (list clause) :=
on_first_left c $ λtype, do
  type' ← normalize type,
  guard $ type' ≠ type,
  h ← mk_local_def `h type',
  return [([h], h)]

meta def inf_normalize_r (c : clause) : tactic (list clause) :=
on_first_right c $ λha, do
  a' ← normalize ha^.local_type,
  guard $ a' ≠ ha^.local_type,
  hna ← mk_local_def `hna (imp a' c^.local_false),
  return [([hna], app hna ha)]

set_option eqn_compiler.max_steps 500

meta def inf_false_l (c : clause) : tactic (list clause) :=
first $ do i ← list.range c^.num_lits,
  if c^.get_lit i = clause.literal.left false_
  then [return []]
  else []

meta def inf_false_r (c : clause) : tactic (list clause) :=
on_first_right c $ λhf,
  if hf^.local_type = c^.local_false
  then return [([], hf)]
  else match hf^.local_type with
  | const ``false [] := do
    pr ← mk_app ``false.rec [c^.local_false, hf],
    return [([], pr)]
  | _ := failed
  end

meta def inf_true_l (c : clause) : tactic (list clause) :=
on_first_left c $ λt,
  match t with
  | (const ``true []) := return [([], const ``true.intro [])]
  | _ := failed
  end

meta def inf_true_r (c : clause) : tactic (list clause) :=
first $ do i ← list.range c^.num_lits,
  if c^.get_lit i = clause.literal.right (const ``true [])
  then [return []]
  else []

meta def inf_not_l (c : clause) : tactic (list clause) :=
on_first_left c $ λtype,
  match type with
  | app (const ``not []) a := do
    hna ← mk_local_def `h (imp a false_),
    return [([hna], hna)]
  | _ := failed
  end

meta def inf_not_r (c : clause) : tactic (list clause) :=
on_first_right c $ λhna,
  match hna^.local_type with
  | app (const ``not []) a := do
    hnna ← mk_local_def `h (imp (imp a false_) c^.local_false),
    return [([hnna], app hnna hna)]
  | _ := failed
  end

meta def inf_and_l (c : clause) : tactic (list clause) :=
on_first_left c $ λab,
  match ab with
  | (app (app (const ``and []) a) b) := do
    ha ← mk_local_def `l a,
    hb ← mk_local_def `r b,
    pab ← mk_mapp ``and.intro [some a, some b, some ha, some hb],
    return [([ha, hb], pab)]
  | _ := failed
  end

meta def inf_and_r (c : clause) : tactic (list clause) :=
on_first_right' c $ λhyp, do
  pa ← mk_mapp ``and.left [none, none, some hyp],
  pb ← mk_mapp ``and.right [none, none, some hyp],
  return [([], pa), ([], pb)]

meta def inf_iff_l (c : clause) : tactic (list clause) :=
on_first_left c $ λab,
  match ab with
  | (app (app (const ``iff []) a) b) := do
    hab ← mk_local_def `l (imp a b),
    hba ← mk_local_def `r (imp b a),
    pab ← mk_mapp ``iff.intro [some a, some b, some hab, some hba],
    return [([hab, hba], pab)]
  | _ := failed
  end

meta def inf_iff_r (c : clause) : tactic (list clause) :=
on_first_right' c $ λhyp, do
  pa ← mk_mapp ``iff.mp [none, none, some hyp],
  pb ← mk_mapp ``iff.mpr [none, none, some hyp],
  return [([], pa), ([], pb)]

meta def inf_or_r (c : clause) : tactic (list clause) :=
on_first_right c $ λhab,
  match hab^.local_type with
  | (app (app (const ``or []) a) b) := do
    hna ← mk_local_def `l (imp a c^.local_false),
    hnb ← mk_local_def `r (imp b c^.local_false),
    proof ← mk_app ``or.elim [a, b, c^.local_false, hab, hna, hnb],
    return [([hna, hnb], proof)]
  | _ := failed
  end

meta def inf_or_l (c : clause) : tactic (list clause) :=
on_first_left c $ λab,
  match ab with
  | (app (app (const ``or []) a) b) := do
    ha ← mk_local_def `l a,
    hb ← mk_local_def `l b,
    pa ← mk_mapp ``or.inl [some a, some b, some ha],
    pb ← mk_mapp ``or.inr [some a, some b, some hb],
    return [([ha], pa), ([hb], pb)]
  | _ := failed
  end

meta def inf_all_r (c : clause) : tactic (list clause) :=
on_first_right' c $ λhallb,
  match hallb^.local_type with
  | (pi n bi a b) := do
    ha ← mk_local_def `x a,
    return [([ha], app hallb ha)]
  | _ := failed
  end

lemma imp_l {F a b} [decidable a] : ((a → b) → F) → ((a → F) → F) :=
λhabf haf, decidable.by_cases
    (assume ha :   a, haf ha)
    (assume hna : ¬a, habf (take ha, absurd ha hna))

lemma imp_l' {F a b} [decidable F] : ((a → b) → F) → ((a → F) → F) :=
λhabf haf, decidable.by_cases
    (assume hf :   F, hf)
    (assume hnf : ¬F, habf (take ha, absurd (haf ha) hnf))

lemma imp_l_c {F : Prop} {a b} : ((a → b) → F) → ((a → F) → F) :=
λhabf haf, classical.by_cases
    (assume hf :   F, hf)
    (assume hnf : ¬F, habf (take ha, absurd (haf ha) hnf))

meta def inf_imp_l (c : clause) : tactic (list clause) :=
on_first_left_dn c $ λhnab,
  match hnab^.local_type with
  | (pi _ _ (pi _ _ a b) _) :=
    if b^.has_var then failed else do
    hna ← mk_local_def `na (imp a c^.local_false),
    pf ← first (do r ← [``super.imp_l, ``super.imp_l', ``super.imp_l_c],
                 [mk_app r [hnab, hna]]),
    hb ← mk_local_def `b b,
    return [([hna], pf), ([hb], app hnab (lam `a binder_info.default a hb))]
  | _ := failed
  end

meta def inf_ex_l (c : clause) : tactic (list clause) :=
on_first_left c $ λexp,
  match exp with
  | (app (app (const ``Exists [u]) dom) pred) := do
    hx ← mk_local_def `x dom,
    predx ← whnf $ app pred hx,
    hpx ← mk_local_def `hpx predx,
    return [([hx,hpx], app_of_list (const ``exists.intro [u])
                       [dom, pred, hx, hpx])]
  | _ := failed
  end

lemma demorgan' {F a} {b : a → Prop} : ((∀x, b x) → F) → (((∃x, b x → F) → F) → F) :=
assume hab hnenb,
  classical.by_cases
    (assume h : ∃x, ¬b x, begin cases h with x, apply hnenb, existsi x, intros, contradiction end)
    (assume h : ¬∃x, ¬b x, hab (take x,
      classical.by_cases
        (assume bx : b x, bx)
        (assume nbx : ¬b x, begin assert hf : false, apply h, existsi x, assumption, contradiction end)))

meta def inf_all_l (c : clause) : tactic (list clause) :=
on_first_left_dn c $ λhnallb,
  match hnallb^.local_type with
  | pi _ _ (pi n bi a b) _ := do
    enb ← mk_mapp ``Exists [none, some $ lam n binder_info.default a (imp b c^.local_false)],
    hnenb ← mk_local_def `h (imp enb c^.local_false),
    pr ← mk_app ``super.demorgan' [hnallb, hnenb],
    return [([hnenb], pr)]
  | _ := failed
  end

meta def inf_ex_r  (c : clause) : tactic (list clause) := do
(qf, ctx) ← c^.open_constn c^.num_quants,
skolemized ← on_first_right' qf $ λhexp,
  match hexp^.local_type with
  | (app (app (const ``Exists [_]) d) p) := do
    sk_sym_name_pp ← get_unused_name `sk (some 1),
    inh_lc ← mk_local' `w binder_info.implicit d,
    sk_sym ← mk_local_def sk_sym_name_pp (pis (ctx ++ [inh_lc]) d),
    sk_p ← whnf_core transparency.none $ app p (app_of_list sk_sym (ctx ++ [inh_lc])),
    sk_ax ← mk_mapp ``Exists [some (local_type sk_sym),
      some (lambdas [sk_sym] (pis (ctx ++ [inh_lc]) (imp hexp^.local_type sk_p)))],
    sk_ax_name ← get_unused_name `sk_axiom (some 1), assert sk_ax_name sk_ax,
    nonempt_of_inh ← mk_mapp ``nonempty.intro [some d, some inh_lc],
    eps ← mk_mapp ``classical.epsilon [some d, some nonempt_of_inh, some p],
    existsi (lambdas (ctx ++ [inh_lc]) eps),
    eps_spec ← mk_mapp ``classical.epsilon_spec [some d, some p],
    exact (lambdas (ctx ++ [inh_lc]) eps_spec),
    sk_ax_local ← get_local sk_ax_name, cases_using sk_ax_local [sk_sym_name_pp, sk_ax_name],
    sk_ax' ← get_local sk_ax_name,
    return [([inh_lc], app_of_list sk_ax' (ctx ++ [inh_lc, hexp]))]
  | _ := failed
  end,
return $ skolemized^.for (λs, s^.close_constn ctx)

meta def first_some {a : Type} : list (tactic (option a)) → tactic (option a)
| [] := return none
| (x::xs) := do xres ← x, match xres with some y := return (some y) | none := first_some xs end

private meta def get_clauses_core' (rules : list (clause → tactic (list clause)))
     : list clause → tactic (list clause) | cs :=
lift list.join $ do
for cs $ λc, do first $
rules^.for (λr, r c >>= get_clauses_core') ++ [return [c]]

meta def get_clauses_core (rules : list (clause → tactic (list clause))) (initial : list clause)
     : tactic (list clause) := do
clauses ← get_clauses_core' rules initial,
filter (λc, lift bnot $ is_taut c) $ list.nub_on clause.type clauses

meta def clausification_rules_intuit : list (clause → tactic (list clause)) :=
[ inf_false_l, inf_false_r, inf_true_l, inf_true_r,
  inf_not_l, inf_not_r,
  inf_and_l, inf_and_r,
  inf_iff_l, inf_iff_r,
  inf_or_l, inf_or_r,
  inf_ex_l,
  inf_normalize_l, inf_normalize_r ]

meta def clausification_rules_classical : list (clause → tactic (list clause)) :=
[ inf_false_l, inf_false_r, inf_true_l, inf_true_r,
  inf_not_l, inf_not_r,
  inf_and_l, inf_and_r,
  inf_iff_l, inf_iff_r,
  inf_or_l, inf_or_r,
  inf_imp_l, inf_all_r,
  inf_ex_l,
  inf_all_l, inf_ex_r,
  inf_normalize_l, inf_normalize_r ]

meta def get_clauses_classical : list clause → tactic (list clause) :=
get_clauses_core clausification_rules_classical
meta def get_clauses_intuit : list clause → tactic (list clause) :=
get_clauses_core clausification_rules_intuit

meta def as_refutation : tactic unit := do
repeat (do intro1, skip),
tgt ← target,
if tgt^.is_constant || tgt^.is_local_constant then skip else do
local_false_name ← get_unused_name `F none, tgt_type ← infer_type tgt,
definev local_false_name tgt_type tgt, local_false ← get_local local_false_name,
target_name ← get_unused_name `target none,
assertv target_name (imp tgt local_false) (lam `hf binder_info.default tgt $ mk_var 0),
change local_false

meta def clauses_of_context : tactic (list clause) := do
local_false ← target,
l ← local_context,
monad.for l (clause.of_proof local_false)

meta def clausify_pre := preprocessing_rule $ take new, lift list.join $ for new $ λ dc, do
cs ← get_clauses_classical [dc^.c],
if cs^.length ≤ 1 then
  return (for cs $ λ c, { dc with c := c })
else
  for cs (λc, mk_derived c dc^.sc)

-- @[super.inf]
meta def clausification_inf : inf_decl := inf_decl.mk 0 $
λgiven, list.foldr orelse (return ()) $
        do r ← clausification_rules_classical,
           [do cs ← r given^.c,
               cs' ← get_clauses_classical cs,
               for' cs' (λc, mk_derived c given^.sc^.sched_now >>= add_inferred),
               remove_redundant given^.id []]


end super
