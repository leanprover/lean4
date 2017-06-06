/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl (CMU)
-/
prelude
import init.meta.expr init.meta.tactic init.meta.constructor_tactic

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
    ∀p, pred.functional A pred₁ p → pred.functional A pred₂ p :=
  pred.functional.rec A f (pred.functional A f')
    (take p, pred.functional.r A f' p[mono with h])

  def {u} pred_i (A) (a) : Prop :=
  ∃[pred'], (Λi, ∀a, pred_i a → pred_i.functional A [pred] a) ∧ pred'_i a

  lemma {u} pred_i.corec_functional (A) [Λi, C_i : a_i → Prop] [Λi, h : ∀a, C_i a → pred_i.functional A C_i a] :
    ∀a, C_i a → pred_i A a :=
  take a ha, ⟨[C], [h], ha⟩

  lemma {u} pred_i.destruct (A) (a) : pred A a → pred.functional A [pred A] a :=
  Exists.rec (a → Prop) (λf, (∀a, f a → pred.functional A f a) ∧ f a)
    (pred.functional A (pred A a) a) h $
  take f, and.rec.{0} (∀a, f a → pred.functional A f a) (f a) $
    assume h₁ : ∀a, f a → pred.functional A f a, assume h₂ : f a,
    pred.functional.mono A f (pred A) (pred.corec_functional A f h₁) a (h₁ a h₂))

  lemma {u} pred_i.construct (A) : ∀a, pred_i.functional A [pred A] a → pred_i A a :=
  pred.corec_functional A (pred.functional A (pred A))
    (pred.functional.mono A (pred A) (pred.functional A (pred A)) (pred.destruct A))

  lemma {u} pred_i.cases_on (A) (C : a → Prop) {a} (h : pred_i a) [Λi, ∀a, b → C p] → C a

  -- TODO:
  lemma {u} pred_i.corec_on (A) [(C : a → Prop)] (a) (h : C_i a)
    [Λi, h_i : ∀a, C_i a → [V j ∃b, a = p]] :
    pred_i A a

  lemma {u} pred.r (A) (b) : pred_i A p :=
  pred_i.construct A p $ pred_i.functional.r A [pred A] b
-/

open level expr tactic

namespace add_coinductive_predicate

/- private -/ meta structure pred_predata : Type :=
(u_names  : list name)
(params   : list expr)
(pd_name  : name)
(pred     : expr)
(type     : expr)
(intros   : list (name × expr))
(locals   : list expr)
(f₁ f₂    : expr)
(u_f      : level)
(func     : expr)

namespace pred_predata

meta def u_params (pd : pred_predata) : list level :=
pd.u_names.map param

meta def f₁_l (pd : pred_predata) : expr :=
pd.f₁.app_of_list pd.locals

meta def f₂_l (pd : pred_predata) : expr :=
pd.f₂.app_of_list pd.locals

meta def func_g (pd : pred_predata) : expr :=
pd.func.app_of_list $ pd.params

meta def pred_g (pd : pred_predata) : expr :=
pd.pred.app_of_list $ pd.params

meta def impl_locals (pd : pred_predata) : list expr :=
pd.locals.map to_implicit_binder

meta def impl_params (pd : pred_predata) : list expr :=
pd.params.map to_implicit_binder

meta def le (pd : pred_predata) (f₁ f₂ : expr) : expr :=
(imp (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis pd.impl_locals

meta def corec (pd : pred_predata) : expr :=
const (pd.pd_name ++ "corec_functional") pd.u_params

meta def mono (pd : pred_predata) : expr :=
const (pd.func.const_name ++ "mono") pd.u_params

meta def rec' (pd : pred_predata) : tactic expr :=
mk_const (pd.func.const_name ++ "rec")
  -- ^^ `rec`'s universes are not always `u_params`, e.g. eq, wf, false

meta def construct (pd : pred_predata) : expr :=
const (pd.pd_name ++ "construct") pd.u_params

meta def destruct (pd : pred_predata) : expr :=
const (pd.pd_name ++ "destruct") pd.u_params

meta def add_theorem (pd : pred_predata) (n : name) (type : expr) (locals : list expr) (tac : tactic unit) :
  tactic expr :=
add_theorem_by n pd.u_names type (pd.impl_params ++ locals) tac

end pred_predata

end add_coinductive_predicate

open add_coinductive_predicate

meta def add_coinductive_predicate
  (u_params : list name) (params : list expr) (preds : list $ expr × list expr) : command := do
  let params_names := params.map local_pp_name,
  let u_params' := u_params.map param,

  pds ← preds.mmap (λ⟨c, is⟩, do
    (ls, `(Prop)) ← mk_local_pis c.local_type,
    let n := if preds.length = 1 then "" else "_" ++ c.local_pp_name.last_string,
    f₁ ← mk_local_def (mk_simple_name $ "C" ++ n) c.local_type,
    f₂ ← mk_local_def (mk_simple_name $ "C₂" ++ n) c.local_type,
    sort u_f ← infer_type f₁ >>= infer_type,
    let func : expr := const (c.local_uniq_name ++ "functional") u_params',
    return {tactic.add_coinductive_predicate.pred_predata .
      pd_name := c.local_uniq_name,
      pred := const c.local_uniq_name u_params', type := c.local_type,
      intros := is.map (λi, (i.local_uniq_name, i.local_type)),
      locals := ls, params := params, u_names := u_params,
      f₁ := f₁, f₂ := f₂, u_f := u_f, func := func}),

  let f₁ := pds.map pred_predata.f₁,
  let f₂ := pds.map pred_predata.f₂,

  /- Introduce all functionals -/
  pds.mmap (λpd:pred_predata, do
    let func_f₁ := pd.func_g.app_of_list $ f₁,
    let func_f₂ := pd.func_g.app_of_list $ f₂,

    /- Define functional for `pd` as inductive predicate -/
    func_intros ← pd.intros.mmap (λ⟨nr, t⟩, do
      (bs, t') ← mk_local_pis t,
      (name.mk_string sub p) ← return $ nr,
      let bs := bs.map $ λe, pds.foldl (λ(e:expr) (pd:pred_predata),
        e.replace_with pd.pred_g pd.f₁) e,
      let t' := t'.replace_with pd.pred_g (pd.func_g.app_of_list $ f₁),
      return ((p ++ "functional") ++ sub, t'.pis $ params ++ f₁ ++ bs)),
    let func_type := pd.type.pis $ params ++ f₁,
    add_inductive pd.func.const_name u_params (params.length + preds.length) func_type func_intros,

    /- Prove monotonicity rule -/
    let mono_type :=
      pds.reverse.foldl (λc (pd:pred_predata), ((pd.le pd.f₁ pd.f₂).imp c).pis [pd.f₁, pd.f₂]) $
      pd.le func_f₁ func_f₂,
    pd.add_theorem (pd.func.const_name ++ "mono") mono_type [] (do
      hf ← pds.mmap (λpd, do
        [f₁, f₂, hf] ← intro_lst [pd.f₁.local_pp_name, pd.f₂.local_pp_name, `hf],
        return (f₂, hf)),
      let fs₂ := hf.map prod.fst,
      let hfs := hf.map prod.snd,
      m ← pd.rec',
      apply $ m.app_of_list params, -- somehow `induction` / `cases` doesn't work?
      focus $ func_intros.map (λ⟨n, t⟩, do
        bs ← intros,
        ms ← apply_core ((const n u_params').app_of_list $ params ++ fs₂) { all := tt },
        params ← (ms.zip bs).mfilter (λ⟨m, d⟩, is_assigned m),
        focus $ params.map (λ⟨m, d⟩, apply d <|> first (hfs.map $ λ hf, apply hf >> apply d))))),

  pds.mmap (λpd:pred_predata, do
    let func_f := λpd:pred_predata, pd.func_g.app_of_list $ pds.map pred_predata.f₁,

    /- define final predicate -/
    pred_body ← (do
      corec ← pds.reverse.mfoldl
        (λcont pd, to_expr ``(%%(pd.le pd.f₁ (func_f pd)) ∧ %%cont))
        (pd.f₁.app_of_list pd.locals),
      pds.reverse.mfoldl (λcont pd, to_expr ``(@Exists %%pd.type %%(cont.lambdas [pd.f₁]))) corec),
    add_decl $ mk_definition pd.pd_name u_params (pd.type.pis $ params) $
      pred_body.lambdas $ params ++ pd.locals,

    /- prove `corec_functional` rule -/
    hs ← pds.mmap $ λpd:pred_predata, mk_local_def `hc $ pd.le pd.f₁ (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "corec_functional") (pd.le pd.f₁ pd.pred_g) (f₁ ++ hs) (do
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      whnf_target,
      f₁.mmap existsi,
      hs.mmap (λf, constructor >> exact f),
      exact h)),
 
  let func_f := λpd : pred_predata, pd.func_g.app_of_list $ pds.map pred_predata.pred_g,

  /- prove `destruct` rules -/
  pds.enum.mmap (λd:ℕ × pred_predata, do
    let n := d.1,
    let pd := d.2,
    let destruct := pd.le pd.pred_g (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "destruct") destruct [] (do
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      (fs, h) ← pds.reverse.mfoldl (λ(c:list expr × expr) (pd:pred_predata), do
          [([f, hf], [])] ← induction c.2 [`f, `hf],
          return (c.1 ++ [f], hf))
        ([], h),
      (hs, h) ← pds.reverse.mfoldl (λ(c:list expr × expr) (pd:pred_predata), do
          [([h, h'], [])] ← induction c.2 [`h, `h'],
          return (c.1 ++ [h], h'))
        ([], h),
      apply $ pd.mono.app_of_list $ params,
      pds.mmap (λpd:pred_predata, focus1 $ do
        apply $ pd.corec.app_of_list $ params,
        focus $ hs.map exact),
      some h' ← return $ hs.nth n,
      apply h',
      exact h)),

  /- prove `construct` rules -/
  pds.mmap (λpd:pred_predata,
    pd.add_theorem (pd.pred.const_name ++ "construct") (pd.le (func_f pd) pd.pred_g) [] (do
      let func_pred_g := λpd:pred_predata,
        pd.func.app_of_list $ params ++ pds.map (λpd:pred_predata, pd.pred.app_of_list params),
      apply $ pd.corec.app_of_list $ params ++ pds.map func_pred_g,
      focus $ pds.map (λpd:pred_predata, do
        apply $ pd.mono.app_of_list $ params,
        focus $ pds.map (λpd, apply pd.destruct)))),

  /- prove `cases_on` rules -/
  pds.mmap (λpd:pred_predata, do
    let motiv := (sort level.zero : expr).pis $ pd.locals,
    C ← mk_local' `C binder_info.implicit motiv,
    h ← mk_local_def `h $ pd.pred_g.app_of_list pd.locals,
    rules ← pd.intros.mmap (λp:name × expr, do
      (args, concl) ← mk_local_pis p.2,
      mk_local_def p.1 $ (C.app_of_list $ concl.get_app_args.dropn params.length).pis args),
    cases_on ← pd.add_theorem (pd.pred.const_name ++ "cases_on")
      (C.app_of_list $ pd.locals) ([C] ++ pd.impl_locals ++ [h] ++ rules)
      (do
        func_rec ← pd.rec',
        apply $ func_rec.app_of_list $ params ++ pds.map pred_predata.pred_g ++ [C] ++ rules,
        apply $ const (pd.pred.const_name ++ "destruct") u_params',
        exact h),
    set_basic_attribute `elab_as_eliminator cases_on.const_name),

  /- prove constructors -/
  pds.mmap (λpd:pred_predata, do
    pd.intros.mmap (λ⟨nr, t⟩, do
      let t := t.instantiate_locals $ pds.map $ λpd:pred_predata, (pd.pd_name, pd.pred_g),
      pd.add_theorem nr t [] $ do
        (name.mk_string sub p) ← return nr,
        bs ← intros,
        apply $ pd.construct.app_of_list $ params,
        exact $ (const ((p ++ "functional") ++ sub) u_params').app_of_list $
          params ++ pds.map pred_predata.pred_g ++ bs)),

  pds.mmap (λpd:pred_predata, do
    set_basic_attribute `irreducible pd.pd_name),

  try triv -- we setup a trivial goal for the tactic framework

end tactic
