/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl (CMU)
-/
prelude
import init.meta.expr init.meta.tactic init.meta.constructor_tactic init.meta.attribute
import init.meta.interactive

namespace name

def last_string : name → string
| anonymous        := "[anonymous]"
| (mk_string s _)  := s
| (mk_numeral _ n) := last_string n

end name

namespace expr
open expr

meta def replace_with (e : expr) (s : expr) (s' : expr) : expr :=
e.replace $ λc d, if c = s then some (s'.lift_vars 0 d) else none

meta def local_binder_info : expr → binder_info
| (local_const x n bi t) := bi
| e                      := binder_info.default

meta def to_implicit_binder : expr → expr
| (local_const n₁ n₂ _ d) := local_const n₁ n₂ binder_info.implicit d
| (lam n _ d b) := lam n binder_info.implicit d b
| (pi n _ d b) := pi n binder_info.implicit d b
| e  := e

meta def get_app_fn_args_aux : list expr → expr → expr × list expr
| r (app f a) := get_app_fn_args_aux (a::r) f
| r e         := (e, r)

meta def get_app_fn_args : expr → expr × list expr :=
get_app_fn_args_aux []

end expr

namespace tactic
open level expr tactic

meta def mk_local_pisn : expr → nat → tactic (list expr × expr)
| (pi n bi d b) (c + 1) := do
  p ← mk_local' n bi d,
  (ps, r) ← mk_local_pisn (b.instantiate_var p) c,
  return ((p :: ps), r)
| e 0 := return ([], e)
| _ _ := failed

meta def drop_pis : list expr → expr → tactic expr
| (list.cons v vs) (pi n bi d b) := do
  t ← infer_type v,
  guard (t =ₐ d),
  drop_pis vs (b.instantiate_var v)
| [] e := return e
| _  _ := failed

meta def mk_theorem (n : name) (ls : list name) (t : expr) (e : expr) : declaration :=
declaration.thm n ls t (task.pure e)

meta def add_theorem_by (n : name) (ls : list name) (type : expr) (tac : tactic unit) : tactic expr := do
  ((), body) ← solve_aux type tac,
  body ← instantiate_mvars body,
  add_decl $ mk_theorem n ls type body,
  return $ const n $ ls.map param

meta def mk_exists_lst (args : list expr) (inner : expr) : tactic expr :=
args.mfoldr (λarg i:expr, do
    t ← infer_type arg,
    sort l ← infer_type t,
    return $ if arg.occurs i ∨ l ≠ level.zero
      then (const `Exists [l] : expr) t (i.lambdas [arg])
      else (const `and [] : expr) t i)
  inner

meta def mk_op_lst (op : expr) (empty : expr) : list expr → expr
| []        := empty
| [e]       := e
| (e :: es) := op e $ mk_op_lst es

meta def mk_and_lst : list expr → expr := mk_op_lst `(and) `(true)

meta def mk_or_lst : list expr → expr := mk_op_lst `(or) `(false)

meta def elim_gen_prod : nat → expr → list expr → tactic (list expr × expr)
| 0       e hs := return (hs, e)
| (n + 1) e hs := do
  [(_, [h, h'], _)] ← induction e [],
  elim_gen_prod n h' (hs ++ [h])

private meta def elim_gen_sum_aux : nat → expr → list expr → tactic (list expr × expr)
| 0       e hs := return (hs, e)
| (n + 1) e hs := do
  [(_, [h], _), (_, [h'], _)] ← induction e [],
  swap,
  elim_gen_sum_aux n h' (h::hs)

meta def elim_gen_sum (n : nat) (e : expr) : tactic (list expr) := do
  (hs, h') ← elim_gen_sum_aux n e [],
  gs ← get_goals,
  set_goals $ (gs.take (n+1)).reverse ++ gs.drop (n+1),
  return $ hs.reverse ++ [h']

end tactic

section
universe u

@[user_attribute]
meta def monotonicity : user_attribute := { name := `monotonicity, descr := "Monotonicity rules for predicates" }

lemma monotonicity.pi {α : Sort u} {p q : α → Prop} (h : ∀a, implies (p a) (q a)) :
  implies (Πa, p a) (Πa, q a) :=
assume h' a, h a (h' a)

lemma monotonicity.imp {p p' q q' : Prop} (h₁ : implies p' q') (h₂ : implies q p) :
  implies (p → p') (q → q') :=
assume h, h₁ ∘ h ∘ h₂

@[monotonicity]
lemma monotonicity.const (p : Prop) : implies p p := id

@[monotonicity]
lemma monotonicity.true (p : Prop) : implies p true := assume _, trivial

@[monotonicity]
lemma monotonicity.false (p : Prop) : implies false p := false.elim

@[monotonicity]
lemma monotonicity.exists {α : Sort u} {p q : α → Prop} (h : ∀a, implies (p a) (q a)) :
  implies (∃a, p a) (∃a, q a) :=
exists_imp_exists h

@[monotonicity]
lemma monotonicity.and {p p' q q' : Prop} (hp : implies p p') (hq : implies q q') :
  implies (p ∧ q) (p' ∧ q') :=
and.imp hp hq

@[monotonicity]
lemma monotonicity.or {p p' q q' : Prop} (hp : implies p p') (hq : implies q q') :
  implies (p ∨ q) (p' ∨ q') :=
or.imp hp hq

@[monotonicity]
lemma monotonicity.not {p q : Prop} (h : implies p q) :
  implies (¬ q) (¬ p) :=
mt h

end

namespace tactic
open expr tactic

/- TODO: use backchaining -/
private meta def mono_aux (ns : list name) (hs : list expr) : tactic unit := do
  intros,
  (do
    `(implies %%p %%q) ← target,
    (do is_def_eq p q, eapplyc `monotone.const) <|>
    (do
      (expr.pi pn pbi pd pb) ← whnf p,
      (expr.pi qn qbi qd qb) ← whnf q,
      sort u ← infer_type pd,
      (do is_def_eq pd qd,
        let p' := expr.lam pn pbi pd pb,
        let q' := expr.lam qn qbi qd qb,
        eapply ((const `monotonicity.pi [u] : expr) pd p' q'),
        skip) <|>
      (do guard $ u = level.zero ∧ is_arrow p ∧ is_arrow q,
        let p' := pb.lower_vars 0 1,
        let q' := qb.lower_vars 0 1,
        eapply ((const `monotonicity.imp []: expr) pd p' qd q'),
        skip))) <|>
  first (hs.map $ λh, apply_core h {md := transparency.none, new_goals := new_goals.non_dep_only} >> skip) <|>
  first (ns.map $ λn, do c ← mk_const n, apply_core c {md := transparency.none, new_goals := new_goals.non_dep_only}, skip),
  all_goals mono_aux

meta def mono (e : expr) (hs : list expr) : tactic unit := do
  t ← target,
  t' ← infer_type e,
  ns ← attribute.get_instances `monotonicity,
  ((), p) ← solve_aux `(implies %%t' %%t) (mono_aux ns hs),
  exact (p e)

end tactic

/-
The coinductive predicate `pred`:

  coinductive {u} pred (A) : a → Prop
  | r : ∀A b, pred A p

where
  `u` is a list of universe parameters
  `A` is a list of global parameters
  `pred` is a list predicates to be defined
  `a` are the indices for each `pred`
  `r` is a list of introduction rules for each `pred`
  `b` is a list of parameters for each rule in `r` and `pred`
  `p` is are the instances of `a` using `A` and `b`

`pred` is compiled to the following defintions:

  inductive {u} pred.functional (A) ([pred'] : a → Prop) : a → Prop
  | r : ∀a [f], b[pred/pred'] → pred.functional a [f] p

  lemma {u} pred.functional.mono (A) ([pred₁] [pred₂] : a → Prop) [(h : ∀b, pred₁ b → pred₂ b)] :
    ∀p, pred.functional A pred₁ p → pred.functional A pred₂ p

  def {u} pred_i (A) (a) : Prop :=
  ∃[pred'], (Λi, ∀a, pred_i a → pred_i.functional A [pred] a) ∧ pred'_i a

  lemma {u} pred_i.corec_functional (A) [Λi, C_i : a_i → Prop] [Λi, h : ∀a, C_i a → pred_i.functional A C_i a] :
    ∀a, C_i a → pred_i A a

  lemma {u} pred_i.destruct (A) (a) : pred A a → pred.functional A [pred A] a

  lemma {u} pred_i.construct (A) : ∀a, pred_i.functional A [pred A] a → pred_i A a

  lemma {u} pred_i.cases_on (A) (C : a → Prop) {a} (h : pred_i a) [Λi, ∀a, b → C p] → C a

  lemma {u} pred_i.corec_on (A) [(C : a → Prop)] (a) (h : C_i a)
    [Λi, h_i : ∀a, C_i a → [V j ∃b, a = p]] : pred_i A a

  lemma {u} pred.r (A) (b) : pred_i A p
-/

namespace tactic
open level expr tactic

namespace add_coinductive_predicate

/- private -/ meta structure coind_rule : Type :=
(orig_nm  : name)
(func_nm  : name)
(type     : expr)
(loc_type : expr)
(args     : list expr)
(loc_args : list expr)
(concl    : expr)
(insts    : list expr)

/- private -/ meta structure coind_pred : Type :=
(u_names  : list name)
(params   : list expr)
(pd_name  : name)
(type     : expr)
(intros   : list coind_rule)
(locals   : list expr)
(f₁ f₂    : expr)
(u_f      : level)

namespace coind_pred

meta def u_params (pd : coind_pred) : list level :=
pd.u_names.map param

meta def f₁_l (pd : coind_pred) : expr :=
pd.f₁.app_of_list pd.locals

meta def f₂_l (pd : coind_pred) : expr :=
pd.f₂.app_of_list pd.locals

meta def pred (pd : coind_pred) : expr :=
const pd.pd_name pd.u_params

meta def func (pd : coind_pred) : expr :=
const (pd.pd_name ++ "functional") pd.u_params

meta def func_g (pd : coind_pred) : expr :=
pd.func.app_of_list $ pd.params

meta def pred_g (pd : coind_pred) : expr :=
pd.pred.app_of_list $ pd.params

meta def impl_locals (pd : coind_pred) : list expr :=
pd.locals.map to_implicit_binder

meta def impl_params (pd : coind_pred) : list expr :=
pd.params.map to_implicit_binder

meta def le (pd : coind_pred) (f₁ f₂ : expr) : expr :=
(imp (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis pd.impl_locals

meta def corec_functional (pd : coind_pred) : expr :=
const (pd.pd_name ++ "corec_functional") pd.u_params

meta def mono (pd : coind_pred) : expr :=
const (pd.func.const_name ++ "mono") pd.u_params

meta def rec' (pd : coind_pred) : tactic expr :=
do let c := pd.func.const_name ++ "rec",
   env  ← get_env,
   decl ← env.get c,
   let num := decl.univ_params.length,
   return (const c $ if num = pd.u_params.length then pd.u_params else level.zero :: pd.u_params)
  -- ^^ `rec`'s universes are not always `u_params`, e.g. eq, wf, false

meta def construct (pd : coind_pred) : expr :=
const (pd.pd_name ++ "construct") pd.u_params

meta def destruct (pd : coind_pred) : expr :=
const (pd.pd_name ++ "destruct") pd.u_params

meta def add_theorem (pd : coind_pred) (n : name) (type : expr) (tac : tactic unit) : tactic expr :=
add_theorem_by n pd.u_names type tac

end coind_pred

end add_coinductive_predicate

open add_coinductive_predicate

/- compact_relation bs as_ps: Product a relation of the form:
  R := λ as, ∃ bs, Λ_i a_i = p_i[bs]
This relation is user visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`. -/
private meta def compact_relation :
  list expr → list (expr × expr) → list expr × list (expr × expr)
| [] ps      := ([], ps)
| (list.cons b bs) ps :=
  match ps.span (λap:expr × expr, ¬ ap.2 =ₐ b) with
    | (_, [])           := let (bs, ps) := compact_relation bs ps in (b::bs, ps)
    | (ps₁, list.cons (a, _) ps₂) := let i := a.instantiate_local b.local_uniq_name in
      compact_relation (bs.map i) ((ps₁ ++ ps₂).map (λ⟨a, p⟩, (a, i p)))
  end

meta def add_coinductive_predicate
  (u_names : list name) (params : list expr) (preds : list $ expr × list expr) : command := do
  let params_names := params.map local_pp_name,
  let u_params := u_names.map param,

  pre_info ← preds.mmap (λ⟨c, is⟩, do
    (ls, t) ← mk_local_pis c.local_type,
    (is_def_eq t `(Prop) <|>
      fail (format! "Type of {c.local_pp_name} is not Prop. Currently only " ++
                    "coinductive predicates are supported.")),
    let n := if preds.length = 1 then "" else "_" ++ c.local_pp_name.last_string,
    f₁ ← mk_local_def (mk_simple_name $ "C" ++ n) c.local_type,
    f₂ ← mk_local_def (mk_simple_name $ "C₂" ++ n) c.local_type,
    return (ls, (f₁, f₂))),

  let fs := pre_info.map prod.snd,
  let fs₁ := fs.map prod.fst,
  let fs₂ := fs.map prod.snd,

  pds ← (preds.zip pre_info).mmap (λ⟨⟨c, is⟩, ls, f₁, f₂⟩, do
    sort u_f ← infer_type f₁ >>= infer_type,
    let pred_g := λc:expr, (const c.local_uniq_name u_params : expr).app_of_list params,
    intros ← is.mmap (λi, do
      (args, t') ← mk_local_pis i.local_type,
      (name.mk_string sub p) ← return i.local_uniq_name,
      let loc_args := args.map $ λe, (fs₁.zip preds).foldl (λ(e:expr) ⟨f, c, _⟩,
        e.replace_with (pred_g c) f) e,
      let t' := t'.replace_with (pred_g c) f₂,
      return { tactic.add_coinductive_predicate.coind_rule .
        orig_nm  := i.local_uniq_name,
        func_nm  := (p ++ "functional") ++ sub,
        type     := i.local_type,
        loc_type := t'.pis loc_args,
        concl    := t',
        loc_args := loc_args,
        args     := args,
        insts    := t'.get_app_args }),
    return { tactic.add_coinductive_predicate.coind_pred .
      pd_name := c.local_uniq_name, type := c.local_type, f₁ := f₁, f₂ := f₂, u_f := u_f,
      intros := intros, locals := ls, params := params, u_names := u_names }),

  /- Introduce all functionals -/
  pds.mmap' (λpd:coind_pred, do
    let func_f₁ := pd.func_g.app_of_list $ fs₁,
    let func_f₂ := pd.func_g.app_of_list $ fs₂,

    /- Define functional for `pd` as inductive predicate -/
    func_intros ← pd.intros.mmap (λr:coind_rule, do
      let t := instantiate_local pd.f₂.local_uniq_name (pd.func_g.app_of_list fs₁) r.loc_type,
      return (r.func_nm, r.orig_nm, t.pis $ params ++ fs₁)),
    add_inductive pd.func.const_name u_names
      (params.length + preds.length) (pd.type.pis $ params ++ fs₁) (func_intros.map $ λ⟨t, _, r⟩, (t, r)),

    /- Prove monotonicity rule -/
    mono_params ← pds.mmap (λpd, do
      h ← mk_local_def `h $ pd.le pd.f₁ pd.f₂,
      return [pd.f₁, pd.f₂, h]),
    pd.add_theorem (pd.func.const_name ++ "mono")
      ((pd.le func_f₁ func_f₂).pis $ params ++ mono_params.join)
      (do
      ps ← intro_lst $ params.map expr.local_pp_name,
      fs ← pds.mmap (λpd, do
        [f₁, f₂, h] ← intro_lst [pd.f₁.local_pp_name, pd.f₂.local_pp_name, `h],
        -- the type of h' reduces to h
        let h' := local_const h.local_uniq_name h.local_pp_name h.local_binder_info $
          (((const `implies [] : expr)
            (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis pd.locals).instantiate_locals $
          (ps.zip params).map $ λ⟨lv, p⟩, (p.local_uniq_name, lv),
        return (f₂, h')),
      m ← pd.rec',
      eapply $ m.app_of_list ps, -- somehow `induction` / `cases` doesn't work?
      func_intros.mmap' (λ⟨n, pp_n, t⟩, solve1 $ do
        bs ← intros,
        ms ← apply_core ((const n u_params).app_of_list $ ps ++ fs.map prod.fst) {new_goals := new_goals.all},
        params ← (ms.zip bs).enum.mfilter (λ⟨n, m, d⟩, bnot <$> is_assigned m.2),
        params.mmap' (λ⟨n, m, d⟩, mono d (fs.map prod.snd) <|>
          fail format! "failed to prove montonoicity of {n+1}. parameter of intro-rule {pp_n}")))),

  pds.mmap' (λpd, do
    let func_f := λpd:coind_pred, pd.func_g.app_of_list $ pds.map coind_pred.f₁,

    /- define final predicate -/
    pred_body ← mk_exists_lst (pds.map coind_pred.f₁) $
      mk_and_lst $ (pds.map $ λpd, pd.le pd.f₁ (func_f pd)) ++ [pd.f₁.app_of_list pd.locals],
    add_decl $ mk_definition pd.pd_name u_names (pd.type.pis $ params) $
      pred_body.lambdas $ params ++ pd.locals,

    /- prove `corec_functional` rule -/
    hs ← pds.mmap $ λpd:coind_pred, mk_local_def `hc $ pd.le pd.f₁ (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "corec_functional")
      ((pd.le pd.f₁ pd.pred_g).pis $ params ++ fs₁ ++ hs)
      (do
      intro_lst $ params.map local_pp_name,
      fs ← intro_lst $ fs₁.map local_pp_name,
      hs ← intro_lst $ hs.map local_pp_name,
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      whnf_target,
      fs.mmap' existsi,
      hs.mmap' (λf, econstructor >> exact f),
      exact h)),

  let func_f := λpd : coind_pred, pd.func_g.app_of_list $ pds.map coind_pred.pred_g,

  /- prove `destruct` rules -/
  pds.enum.mmap' (λ⟨n, pd⟩, do
    let destruct := pd.le pd.pred_g (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "destruct") (destruct.pis params) (do
      ps ← intro_lst $ params.map local_pp_name,
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      (fs, h) ← elim_gen_prod pds.length h [],
      (hs, h) ← elim_gen_prod pds.length h [],
      eapply $ pd.mono.app_of_list ps,
      pds.mmap' (λpd:coind_pred, focus1 $ do
        eapply $ pd.corec_functional,
        focus $ hs.map exact),
      some h' ← return $ hs.nth n,
      eapply h',
      exact h)),

  /- prove `construct` rules -/
  pds.mmap' (λpd,
    pd.add_theorem (pd.pred.const_name ++ "construct")
      ((pd.le (func_f pd) pd.pred_g).pis params) (do
      ps ← intro_lst $ params.map local_pp_name,
      let func_pred_g := λpd:coind_pred,
        pd.func.app_of_list $ ps ++ pds.map (λpd:coind_pred, pd.pred.app_of_list ps),
      eapply $ pd.corec_functional.app_of_list $ ps ++ pds.map func_pred_g,
      pds.mmap' (λpd:coind_pred, solve1 $ do
        eapply $ pd.mono.app_of_list ps,
        pds.mmap' (λpd, solve1 $ eapply (pd.destruct.app_of_list ps) >> skip)))),

  /- prove `cases_on` rules -/
  pds.mmap' (λpd, do
    let C := pd.f₁.to_implicit_binder,
    h ← mk_local_def `h $ pd.pred_g.app_of_list pd.locals,
    rules ← pd.intros.mmap (λr:coind_rule, do
      mk_local_def (mk_simple_name r.orig_nm.last_string) $ (C.app_of_list r.insts).pis r.args),
    cases_on ← pd.add_theorem (pd.pred.const_name ++ "cases_on")
      ((C.app_of_list pd.locals).pis $ params ++ [C] ++ pd.impl_locals ++ [h] ++ rules)
      (do
        ps ← intro_lst $ params.map local_pp_name,
        C  ← intro `C,
        ls ← intro_lst $ pd.locals.map local_pp_name,
        h  ← intro `h,
        rules  ← intro_lst $ rules.map local_pp_name,
        func_rec ← pd.rec',
        eapply $ func_rec.app_of_list $ ps ++ pds.map (λpd, pd.pred.app_of_list ps) ++ [C] ++ rules,
        eapply $ pd.destruct,
        exact h),
    set_basic_attribute `elab_as_eliminator cases_on.const_name),

  /- prove `corec_on` rules -/
  pds.mmap' (λpd, do
    rules ← pds.mmap (λpd, do
      intros ← pd.intros.mmap (λr, do
        let (bs, eqs) := compact_relation r.loc_args $ pd.locals.zip r.insts,
        eqs ← eqs.mmap (λ⟨l, i⟩, do
          sort u ← infer_type l.local_type,
          return $ (const `eq [u] : expr) l.local_type i l),
        match bs, eqs with
        | [], [] := return ((0, 0), mk_true)
        | _, []  := prod.mk (bs.length, 0) <$> mk_exists_lst bs.init bs.ilast.local_type
        | _, _   := prod.mk (bs.length, eqs.length) <$> mk_exists_lst bs (mk_and_lst eqs)
        end),
      let shape  := intros.map prod.fst,
      let intros := intros.map prod.snd,
      prod.mk shape <$>
        mk_local_def (mk_simple_name $ "h_" ++ pd.pd_name.last_string)
          (((pd.f₁.app_of_list pd.locals).imp (mk_or_lst intros)).pis pd.locals)),
    let shape := rules.map prod.fst,
    let rules := rules.map prod.snd,
    h ← mk_local_def `h $ pd.f₁.app_of_list pd.locals,
    pd.add_theorem (pd.pred.const_name ++ "corec_on")
      ((pd.pred_g.app_of_list $ pd.locals).pis $ params ++ fs₁ ++ pd.impl_locals ++ [h] ++ rules)
      (do
        ps ← intro_lst $ params.map local_pp_name,
        fs ← intro_lst $ fs₁.map local_pp_name,
        ls ← intro_lst $ pd.locals.map local_pp_name,
        h  ← intro `h,
        rules  ← intro_lst $ rules.map local_pp_name,
        eapply $ pd.corec_functional.app_of_list $ ps ++ fs,
        (pds.zip $ rules.zip shape).mmap (λ⟨pd, hr, s⟩, solve1 $ do
          ls ← intro_lst $ pd.locals.map local_pp_name,
          h' ← intro `h,
          h' ← note `h' none $ hr.app_of_list ls h',
          match s.length with
          | 0     := induction h' >> skip -- h' : false
          | (n+1) := do
            hs ← elim_gen_sum n h',
            (hs.zip $ pd.intros.zip s).mmap' (λ⟨h, r, n_bs, n_eqs⟩, solve1 $ do
              (as, h) ← elim_gen_prod (n_bs - (if n_eqs = 0 then 1 else 0)) h [],
              if n_eqs > 0 then do
                (eqs, eq') ← elim_gen_prod (n_eqs - 1) h [],
                (eqs ++ [eq']).mmap' subst
              else skip,
              eapply ((const r.func_nm u_params).app_of_list $ ps ++ fs),
              iterate assumption)
          end),
        exact h)),

  /- prove constructors -/
  pds.mmap' (λpd, pd.intros.mmap' (λr,
    pd.add_theorem r.orig_nm (r.type.pis params) $ do
      ps ← intro_lst $ params.map local_pp_name,
      bs ← intros,
      eapply $ pd.construct,
      exact $ (const r.func_nm u_params).app_of_list $ ps ++ pds.map (λpd, pd.pred.app_of_list ps) ++ bs)),

  pds.mmap' (λpd:coind_pred, set_basic_attribute `irreducible pd.pd_name),

  try triv -- we setup a trivial goal for the tactic framework

open lean.parser
open interactive

@[user_command]
meta def coinductive_predicate (meta_info : decl_meta_info) (_ : parse $ tk "coinductive") : lean.parser unit := do
  decl ← inductive_decl.parse meta_info,
  add_coinductive_predicate decl.u_names decl.params $ decl.decls.map $ λ d, (d.sig, d.intros),
  decl.decls.mmap' $ λ d, do {
    get_env >>= λ env, set_env $ env.add_namespace d.name,
    meta_info.attrs.apply d.name,
    d.attrs.apply d.name,
    some doc_string ← pure meta_info.doc_string | skip,
    add_doc_string d.name doc_string
  }

/-- Prepares coinduction proofs. This tactic constructs the coinduction invariant from
the quantifiers in the current goal.

Current version: do not support mutual inductive rules (i.e. only a since C -/
meta def coinduction (rule : expr) : tactic unit := focus1 $
do
  ctxts' ← intros,
  ctxts ← ctxts'.mmap (λv,
    local_const v.local_uniq_name v.local_pp_name v.local_binder_info <$> infer_type v),
  mvars ← apply_core rule {approx := ff, new_goals := new_goals.all},
  -- analyse relation
  g ← list.head <$> get_goals,
  (list.cons _ m_is) ← return $ mvars.drop_while (λv, v.2 ≠ g),
  tgt ← target,
  (is, ty) ← mk_local_pis tgt,

  -- construct coinduction predicate
  (bs, eqs) ← compact_relation ctxts <$>
    ((is.zip m_is).mmap (λ⟨i, m⟩, prod.mk i <$> instantiate_mvars m.2)),

  solve1 (do
    eqs ← mk_and_lst <$> eqs.mmap (λ⟨i, m⟩, mk_app `eq [m, i] >>= instantiate_mvars),
    rel ← mk_exists_lst bs eqs,
    exact (rel.lambdas is)),

  -- prove predicate
  solve1 (do
    target >>= instantiate_mvars >>= change, -- TODO: bug in existsi & constructor when mvars in hyptohesis
    bs.mmap existsi,
    iterate (econstructor >> skip)),

  -- clean up remaining coinduction steps
  all_goals (do
    ctxts'.reverse.mmap clear,
    target >>= instantiate_mvars >>= change, -- TODO: bug in subst when mvars in hyptohesis
    is ← intro_lst $ is.map expr.local_pp_name,
    h ← intro1,
    (_, h) ← elim_gen_prod (bs.length - (if eqs.length = 0 then 1 else 0)) h [],
    (match eqs with
    | [] := clear h
    | (e::eqs) := do
      (hs, h) ← elim_gen_prod eqs.length h [],
      (h::(hs.reverse)).mmap' subst
    end))

namespace interactive
open interactive interactive.types expr lean.parser
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def coinduction (corec_name : parse ident)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit := do
  rule ← mk_const corec_name,
  locals ← mmap tactic.get_local $ revert.get_or_else [],
  revert_lst locals,
  tactic.coinduction rule,
  skip

end interactive

end tactic
