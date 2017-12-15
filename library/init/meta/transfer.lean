/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl (CMU)
-/
prelude
import init.meta.tactic init.meta.match_tactic init.relator init.meta.mk_dec_eq_instance
import init.data.list.instances

namespace transfer
open tactic expr list monad

/- Transfer rules are of the shape:

  rel_t : {u} Πx, R t₁ t₂

where `u` is a list of universe parameters, `x` is a list of dependent variables, and `R` is a
relation.  Then this rule will translate `t₁` (depending on `u` and `x`) into `t₂`.  `u` and `x`
will be called parameters. When `R` is a relation on functions lifted from `S` and `R` the variables
bound by `S` are called arguments. `R` is generally constructed using `⇒` (i.e. `relator.lift_fun`).

As example:

  rel_eq : (R ⇒ R ⇒ iff) eq t

transfer will match this rule when it sees:

  (@eq α a b)      and transfer it to    (t a b)

Here `α` is a parameter and `a` and `b` are arguments.


TODO: add trace statements

TODO: currently the used relation must be fixed by the matched rule or through type class
  inference. Maybe we want to replace this by type inference similar to Isabelle's transfer.

-/


private meta structure rel_data :=
(in_type : expr)
(out_type : expr)
(relation : expr)

meta instance has_to_tactic_format_rel_data : has_to_tactic_format rel_data :=
⟨λr, do
  R ← pp r.relation,
  α ← pp r.in_type,
  β ← pp r.out_type,
  return format!"({R}: rel ({α}) ({β}))" ⟩

private meta structure rule_data :=
(pr      : expr)
(uparams : list name)              -- levels not in pat
(params  : list (expr × bool))     -- fst : local constant, snd = tt → param appears in pattern
(uargs   : list name)              -- levels not in pat
(args    : list (expr × rel_data)) -- fst : local constant
(pat     : pattern)                -- `R c`
(output  : expr)                   -- right-hand side `d` of rel equation `R c d`

meta instance has_to_tactic_format_rule_data : has_to_tactic_format rule_data :=
⟨λr, do
  pr ← pp r.pr,
  up ← pp r.uparams,
  mp ← pp r.params,
  ua ← pp r.uargs,
  ma ← pp r.args,
  pat ← pp r.pat.target,
  output ← pp r.output,
  return format!"{{ ⟨{pat}⟩ pr: {pr} → {output}, {up} {mp} {ua} {ma} }" ⟩

private meta def get_lift_fun : expr → tactic (list rel_data × expr)
| e :=
  do {
    guardb (is_constant_of (get_app_fn e) ``relator.lift_fun),
    [α, β, γ, δ, R, S] ← return $ get_app_args e,
    (ps, r) ← get_lift_fun S,
    return (rel_data.mk α β R :: ps, r)} <|>
  return ([], e)

private meta def mark_occurences (e : expr) : list expr → list (expr × bool)
| []       := []
| (h :: t) := let xs := mark_occurences t in
  (h, occurs h e || any xs (λ⟨e, oc⟩, oc && occurs h e)) :: xs

private meta def analyse_rule (u' : list name) (pr : expr) : tactic rule_data := do
  t ← infer_type pr,
  (params, app (app r f) g) ← mk_local_pis t,
  (arg_rels, R) ← get_lift_fun r,
  args    ← (enum arg_rels).mmap $ λ⟨n, a⟩,
    prod.mk <$> mk_local_def (mk_simple_name ("a_" ++ repr n)) a.in_type <*> pure a,
  a_vars  ← return $ prod.fst <$> args,
  p       ← head_beta (app_of_list f a_vars),
  p_data  ← return $ mark_occurences (app R p) params,
  p_vars  ← return $ list.map prod.fst (p_data.filter (λx, ↑x.2)),
  u       ← return $ collect_univ_params (app R p) ∩ u',
  pat     ← mk_pattern (level.param <$> u) (p_vars ++ a_vars) (app R p) (level.param <$> u) (p_vars ++ a_vars),
  return $ rule_data.mk pr (u'.remove_all u) p_data u args pat g

private meta def analyse_decls : list name → tactic (list rule_data) :=
mmap (λn, do
  d ← get_decl n,
  c ← return d.univ_params.length,
  ls ← (repeat () c).mmap (λ_, mk_fresh_name),
  analyse_rule ls (const n (ls.map level.param)))

private meta def split_params_args : list (expr × bool) → list expr → list (expr × option expr) × list expr
| ((lc, tt) :: ps) (e :: es) := let (ps', es') := split_params_args ps es in ((lc, some e) :: ps', es')
| ((lc, ff) :: ps) es        := let (ps', es') := split_params_args ps es in ((lc, none) :: ps', es')
| _ es := ([], es)

private meta def param_substitutions (ctxt : list expr) :
  list (expr × option expr) → tactic (list (name × expr) × list expr)
| (((local_const n _ bi t), s) :: ps) := do
  (e, m)  ← match s with
  | (some e) := return (e, [])
  | none     :=
    let ctxt' := list.filter (λv, occurs v t) ctxt in
    let ty := pis ctxt' t in
    if bi = binder_info.inst_implicit then do
      guard (bi = binder_info.inst_implicit),
      e ← instantiate_mvars ty >>= mk_instance,
      return (e, [])
    else do
      mv ← mk_meta_var ty,
      return (app_of_list mv ctxt', [mv])
  end,
  sb ← return $ instantiate_local n e,
  ps ← return $ prod.map sb ((<$>) sb) <$> ps,
  (ms, vs) ← param_substitutions ps,
  return ((n, e) :: ms, m ++ vs)
| _ := return ([], [])

/- input expression a type `R a`, it finds a type `b`, s.t. there is a proof of the type `R a b`.
It return (`a`, pr : `R a b`) -/
meta def compute_transfer : list rule_data → list expr → expr → tactic (expr × expr × list expr)
| rds ctxt e := do
  -- Select matching rule
  (i, ps, args, ms, rd) ← first (rds.map (λrd, do
    (l, m)     ← match_pattern rd.pat e semireducible,
    level_map  ← rd.uparams.mmap $ λl, prod.mk l <$> mk_meta_univ,
    inst_univ  ← return $ λe, instantiate_univ_params e (level_map ++ zip rd.uargs l),
    (ps, args) ← return $ split_params_args (rd.params.map (prod.map inst_univ id)) m,
    (ps, ms)   ← param_substitutions ctxt ps, /- this checks type class parameters -/
    return (instantiate_locals ps ∘ inst_univ, ps, args, ms, rd))) <|>
  (do trace e, fail "no matching rule"),

  (bs, hs, mss) ← (zip rd.args args).mmap (λ⟨⟨_, d⟩, e⟩, do
    -- Argument has function type
    (args, r) ← get_lift_fun (i d.relation),
    ((a_vars, b_vars), (R_vars, bnds)) ← (enum args).mmap (λ⟨n, arg⟩, do
      a ← mk_local_def sformat!"a{n}" arg.in_type,
      b ← mk_local_def sformat!"b{n}" arg.out_type,
      R ← mk_local_def sformat!"R{n}" (arg.relation a b),
      return ((a, b), (R, [a, b, R]))) >>= (return ∘ prod.map unzip unzip ∘ unzip),
    rds'      ← R_vars.mmap (analyse_rule []),

    -- Transfer argument
    a           ← return $ i e,
    a'          ← head_beta (app_of_list a a_vars),
    (b, pr, ms) ← compute_transfer (rds ++ rds') (ctxt ++ a_vars) (app r a'),
    b'          ← head_eta (lambdas b_vars b),
    return (b', [a, b', lambdas (list.join bnds) pr], ms)) >>= (return ∘ prod.map id unzip ∘ unzip),

  -- Combine
  b  ← head_beta (app_of_list (i rd.output) bs),
  pr ← return $ app_of_list (i rd.pr) (prod.snd <$> ps ++ list.join hs),
  return (b, pr, ms ++ mss.join)

meta def transfer (ds : list name) : tactic unit := do
  rds ← analyse_decls ds,
  tgt ← target,

  (guard (¬ tgt.has_meta_var) <|>
    fail "Target contains (universe) meta variables. This is not supported by transfer."),

  (new_tgt, pr, ms) ← compute_transfer rds [] ((const `iff [] : expr) tgt),
  new_pr ← mk_meta_var new_tgt,

  /- Setup final tactic state -/
  exact ((const `iff.mpr [] : expr) tgt new_tgt pr new_pr),
  ms ← ms.mmap (λm, (get_assignment m >> return []) <|> return [m]),
  gs ← get_goals,
  set_goals (ms.join ++ new_pr :: gs)

end transfer
