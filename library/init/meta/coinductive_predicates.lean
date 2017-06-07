/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl (CMU)
-/
prelude
import init.meta.expr init.meta.tactic init.meta.constructor_tactic init.meta.attribute

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

meta def add_theorem_by (n : name) (ls : list name) (type : expr) (locals : list expr) (tac : tactic unit) :
  tactic expr := do
  ((), body) ← solve_aux type tac,
  body ← instantiate_mvars body,
  add_decl $ mk_theorem n ls (type.pis locals) (body.lambdas locals),
  return $ const n $ ls.map param

meta def is_assigned (m : expr): tactic bool :=
((get_assignment m >> return ff) <|> return tt)

meta def mk_exists_lst (args : list expr) (inner : expr) : tactic expr :=
args.mfoldr (λarg i:expr, do
    sort l ← infer_type arg.local_type,
    return $ (const `Exists [l] : expr) arg.local_type (i.lambdas [arg]))
  inner

meta def mk_op_lst (op : expr) (empty : expr) : list expr → expr
| []         := empty
| (hd :: tl) := tl.foldr (λa c, op a c) hd

meta def mk_and_lst : list expr → expr := mk_op_lst `(and) `(true)

meta def mk_or_lst : list expr → expr := mk_op_lst `(or) `(false)

meta def elim_gen_prod : nat → expr → list expr → tactic (list expr × expr)
| 0       e hs := return (hs, e)
| (n + 1) e hs := do
  [([h, h'], _)] ← induction e [],
  elim_gen_prod n h' (hs ++ [h])

private meta def elim_gen_sum_aux : nat → expr → list expr → tactic (list expr × expr)
| 0       e hs := return (hs, e)
| (n + 1) e hs := do
  [([h], _), ([h'], _)] ← induction e [],
  swap,
  elim_gen_sum_aux n h (h'::hs)

meta def elim_gen_sum (n : nat) (e : expr) : tactic (list expr) := do
  (hs, h') ← elim_gen_sum_aux n e [],
  gs ← get_goals,
  set_goals ((gs.taken n).reverse ++ gs.dropn n),
  return $ hs.reverse ++ [h']

end tactic

section
universe u

def monotonicity := { user_attribute . name := `monotonicity, descr := "Monotonicity rules for predicates" }
run_cmd register_attribute `monotonicity

lemma monotonicity.pi {α : Sort u} {p q : α → Prop} (h : ∀a, implies (p a) (q a)) :
  implies (Πa, p a) (Πa, q a) :=
take h' a, h a (h' a)

lemma monotonicity.imp {p p' q q' : Prop} (h₁ : implies p' q') (h₂ : implies q p) :
  implies (p → p') (q → q') :=
take h, h₁ ∘ h ∘ h₂

@[monotonicity]
lemma monotonicity.const (p : Prop) : implies p p := id

@[monotonicity]
lemma monotonicity.true (p : Prop) : implies p true := take _, trivial

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
    (do is_def_eq p q, applyc `monotone.const) <|>
    (do
      (expr.pi pn pbi pd pb) ← return p,
      (expr.pi qn qbi qd qb) ← return q,
      sort u ← infer_type pd,
      (do is_def_eq pd qd,
        let p' := expr.lam pn pbi pd pb,
        let q' := expr.lam qn qbi qd qb,
        apply $ (const `monotonicity.pi [u] : expr) pd p' q') <|>
      (do guard $ u = level.zero ∧ is_arrow p ∧ is_arrow q,
        let p' := pb.lower_vars 0 1,
        let q' := qb.lower_vars 0 1,
        apply $ (const `monotonicity.imp []: expr) pd p' qd q'))) <|>
  first (hs.map $ λh, apply_core h { md := transparency.none } >> skip) <|>
  first (ns.map $ λn, do c ← mk_const n, apply_core c { md := transparency.none }, skip),
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
(const (pd.pd_name ++ "corec_functional") pd.u_params).app_of_list pd.params

meta def mono (pd : coind_pred) : expr :=
(const (pd.func.const_name ++ "mono") pd.u_params).app_of_list pd.params

meta def rec' (pd : coind_pred) : tactic expr :=
do let c := pd.func.const_name ++ "rec",
   env  ← get_env,
   decl ← env.get c,
   let num := decl.univ_params.length,
   return (const c $ if num = pd.u_params.length then pd.u_params else level.zero :: pd.u_params)
  -- ^^ `rec`'s universes are not always `u_params`, e.g. eq, wf, false

meta def construct (pd : coind_pred) : expr :=
(const (pd.pd_name ++ "construct") pd.u_params).app_of_list pd.params

meta def destruct (pd : coind_pred) : expr :=
(const (pd.pd_name ++ "destruct") pd.u_params).app_of_list pd.params

meta def add_theorem (pd : coind_pred) (n : name) (type : expr) (locals : list expr) (tac : tactic unit) :
  tactic expr :=
add_theorem_by n pd.u_names type (pd.impl_params ++ locals) tac

end coind_pred

end add_coinductive_predicate

open add_coinductive_predicate

meta def add_coinductive_predicate
  (u_names : list name) (params : list expr) (preds : list $ expr × list expr) : command := do
  let params_names := params.map local_pp_name,
  let u_params := u_names.map param,

  pre_info ← preds.mmap (λ⟨c, is⟩, do
    (ls, `(Prop)) ← mk_local_pis c.local_type,
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
      return (r.func_nm, t.pis $ params ++ fs₁)),
    add_inductive pd.func.const_name u_names
      (params.length + preds.length) (pd.type.pis $ params ++ fs₁) func_intros,

    /- Prove monotonicity rule -/
    monos ← pds.mmap (λpd, do
      h ← mk_local_def `h $ pd.le pd.f₁ pd.f₂,
      -- the type of h' reduces to h
      let h' := local_const h.local_uniq_name h.local_pp_name h.local_binder_info $
        ((const `implies [] : expr) (pd.f₁.app_of_list pd.locals) (pd.f₂.app_of_list pd.locals)).pis pd.locals,
      return ([pd.f₁, pd.f₂, h], h')),
    let mono_params := monos.map prod.fst,
    let mono_rules  := monos.map prod.snd,
    pd.add_theorem (pd.func.const_name ++ "mono") (pd.le func_f₁ func_f₂) mono_params.join (do
      m ← pd.rec',
      apply $ m.app_of_list params, -- somehow `induction` / `cases` doesn't work?
      func_intros.mmap' (λ⟨n, t⟩, solve1 $ do
        bs ← intros,
        ms ← apply_core ((const n u_params).app_of_list $ params ++ fs₂) { all := tt },
        params ← (ms.zip bs).mfilter (λ⟨m, d⟩, is_assigned m),
        params.mmap' (λ⟨m, d⟩, mono d mono_rules)))),

  pds.mmap' (λpd:coind_pred, do
    let func_f := λpd:coind_pred, pd.func_g.app_of_list $ pds.map coind_pred.f₁,

    /- define final predicate -/
    pred_body ← (do
      corec ← pds.reverse.mfoldl
        (λcont pd, to_expr ``(%%(pd.le pd.f₁ (func_f pd)) ∧ %%cont))
        (pd.f₁.app_of_list pd.locals),
      pds.reverse.mfoldl (λcont pd, to_expr ``(@Exists %%pd.type %%(cont.lambdas [pd.f₁]))) corec),
    add_decl $ mk_definition pd.pd_name u_names (pd.type.pis $ params) $
      pred_body.lambdas $ params ++ pd.locals,

    /- prove `corec_functional` rule -/
    hs ← pds.mmap $ λpd:coind_pred, mk_local_def `hc $ pd.le pd.f₁ (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "corec_functional") (pd.le pd.f₁ pd.pred_g) (fs₁ ++ hs) (do
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      whnf_target,
      fs₁.mmap' existsi,
      hs.mmap' (λf, constructor >> exact f),
      exact h)),

  let func_f := λpd : coind_pred, pd.func_g.app_of_list $ pds.map coind_pred.pred_g,

  /- prove `destruct` rules -/
  pds.enum.mmap' (λ⟨n, pd⟩, do
    let destruct := pd.le pd.pred_g (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "destruct") destruct [] (do
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      (fs, h) ← elim_gen_prod pds.length h [],
      (hs, h) ← elim_gen_prod pds.length h [],
      apply $ pd.mono,
      pds.mmap' (λpd:coind_pred, focus1 $ do
        apply $ pd.corec_functional,
        focus $ hs.map exact),
      some h' ← return $ hs.nth n,
      apply h',
      exact h)),

  /- prove `construct` rules -/
  pds.mmap' (λpd:coind_pred,
    pd.add_theorem (pd.pred.const_name ++ "construct") (pd.le (func_f pd) pd.pred_g) [] (do
      let func_pred_g := λpd:coind_pred,
        pd.func.app_of_list $ params ++ pds.map (λpd:coind_pred, pd.pred.app_of_list params),
      apply $ pd.corec_functional.app_of_list $ pds.map func_pred_g,
      pds.mmap' (λpd:coind_pred, solve1 $ do
        apply pd.mono,
        pds.mmap' (λpd, solve1 $ apply pd.destruct)))),

  /- prove `cases_on` rules -/
  pds.mmap' (λpd:coind_pred, do
    let C := pd.f₁.to_implicit_binder,
    h ← mk_local_def `h $ pd.pred_g.app_of_list pd.locals,
    rules ← pd.intros.mmap (λr:coind_rule, do
      mk_local_def (mk_simple_name r.orig_nm.last_string) $ (C.app_of_list r.insts).pis r.args),
    cases_on ← pd.add_theorem (pd.pred.const_name ++ "cases_on")
      (C.app_of_list pd.locals) ([C] ++ pd.impl_locals ++ [h] ++ rules)
      (do
        func_rec ← pd.rec',
        apply $ func_rec.app_of_list $ params ++ pds.map coind_pred.pred_g ++ [C] ++ rules,
        apply $ pd.destruct,
        exact h),
    set_basic_attribute `elab_as_eliminator cases_on.const_name),

  /- prove `corec_on` rules -/
  pds.mmap' (λpd:coind_pred, do
    rules ← pds.mmap (λpd, do
      intros ← pd.intros.mmap (λr:coind_rule, do
        eqs ← (list.zip pd.locals r.insts).mmap (λ⟨l, i⟩, do
          sort u ← infer_type l.local_type,
          return $ (const `eq [u] : expr) l.local_type i l),
        mk_exists_lst r.loc_args $ mk_and_lst eqs),
      mk_local_def (mk_simple_name $ "h_" ++ pd.pd_name.last_string) $
        ((pd.f₁.app_of_list pd.locals).imp (mk_or_lst intros)).pis pd.locals),
    h ← mk_local_def `h $ pd.f₁.app_of_list pd.locals,
    pd.add_theorem (pd.pred.const_name ++ "corec_on")
      (pd.pred_g.app_of_list pd.locals) (fs₁ ++ pd.impl_locals ++ [h] ++ rules)
      (do
        apply $ pd.corec_functional.app_of_list fs₁,
        (pds.zip rules).mmap (λ⟨pd, hr⟩, solve1 $ do
          ls ← intro_lst $ pd.locals.map local_pp_name,
          h' ← intro `h,
          h' ← note `h' none $ hr.app_of_list ls h',
          match pd.intros.length with
          | 0     := induction h' >> skip -- h' : false
          | (n+1) := do
            hs ← elim_gen_sum n h',
            (hs.zip pd.intros).mmap (λ⟨h, r⟩, solve1 $ do
              (as, h)    ← elim_gen_prod (r.args.length) h [],
              (eqs, eq') ← elim_gen_prod (pd.locals.length - 1) h [],
              let eqs := eqs ++ [eq'],
              eqs.mmap subst,
              apply ((const r.func_nm u_params).app_of_list $ params ++ fs₁ ++ as)),
            skip
          end),
        exact h)),

  /- prove constructors -/
  pds.mmap' (λpd:coind_pred, pd.intros.mmap' (λr,
    pd.add_theorem r.orig_nm r.type [] $ do
      bs ← intros,
      apply $ pd.construct,
      exact $ (const r.func_nm u_params).app_of_list $ params ++ pds.map coind_pred.pred_g ++ bs)),

  pds.mmap' (λpd:coind_pred, set_basic_attribute `irreducible pd.pd_name),

  try triv -- we setup a trivial goal for the tactic framework

end tactic
