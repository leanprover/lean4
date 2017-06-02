/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl (CMU)
-/
prelude
import init.meta.expr init.meta.tactic

namespace expr
open expr

meta def replace_with (e : expr) (s : expr) (s' : expr) : expr :=
e.replace $ λc d, if c = s then some s' else none

meta def local_binder_info : expr → binder_info
| (local_const x n bi t) := bi
| e                      := binder_info.default

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
  body ← mk_theorem n ls type <$> instantiate_mvars body,
  add_decl body,
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
  `a` are the indices
  `r` is a list of introduction rules
  `b` is a list of parameters for each rule in `r`
  `p` is are the instances of `a` using `A` and `b`

`pred` is compiled to the following defintions:

  inductive {u} pred.functional (A) (f : a → Prop) : a → Prop
  | r : ∀a f, b[pred/f] → pred.functional a f p

  lemma {u} pred.functional.mono (A) (f f' : a → Prop) (h : ∀b, f b → f' b) :
    ∀p, pred.functional A f p → pred.functional A f' p :=
  pred.functional.rec A f (pred.functional A f')
    (take p, pred.functional.r A f' p[mono with h])

  def {u} pred (A) (a) : Prop :=
  ∃f, (∀a, f a → pred.functional A f a) ∧ f a

  lemma {u} pred.corec_functional (A) (C : a → Prop) (h : ∀a, C a → pred.functional A C a) :
    ∀a, C a → pred A a :=
  take a ha, ⟨C, h, ha⟩

  lemma {u} pred.destruct (A) (a) : pred A a → pred.functional A (pred A) a :=
  Exists.rec (a → Prop) (λf, (∀a, f a → pred.functional A f a) ∧ f a)
    (pred.functional A (pred A a) a) h $
  take f, and.rec.{0} (∀a, f a → pred.functional A f a) (f a) $
    assume h₁ : ∀a, f a → pred.functional A f a, assume h₂ : f a,
    pred.functional.mono A f (pred A) (pred.corec_functional A f h₁) a (h₁ a h₂))

  lemma {u} pred.construct (A) : ∀a, pred.functional A (pred A) a → pred A a :=
  pred.corec_functional A (pred.functional A (pred A))
    (pred.functional.mono A (pred A) (pred.functional A (pred A)) (pred.destruct A))

  lemma {u} pred.r (A) (b) : pred A p :=
  pred.construct A p $ pred.functional.r A (pred A) b

-/

meta def add_coinductive_predicate
  (n : name) (us : list name) (p : nat) (type : expr) (irules : list (name × expr)) : command := do
  let us' := us.map param,

  /- introduce locals to represent global parameters -/
  (gs, type') ← mk_local_pisn type p,
  (ls, `(Prop)) ← mk_local_pis type',
  let gs_names := gs.map local_pp_name,
  let ls_names := ls.map local_pp_name,

  -- vv this will be two lists of functions to support mutual induction
  f ← mk_local_def `f type',
  f₂ ← mk_local_def `f' type',
  sort u_f ← infer_type f >>= infer_type,

  /- define often occuring subterms -/
  let pred : expr := const n us',
  let pred_g      := pred.app_of_list gs,
  let pred_gl     := pred_g.app_of_list ls,

  let func_type   := type'.pis $ gs ++ [f],
  let func_name   := n ++ "functional",
  let func : expr := const func_name us',
  let func_g      := func.app_of_list gs,
  let func_f      := func_g f,
  let func_f₂     := func_g f₂,
  let func_pred_l := func.app_of_list $ gs ++ [pred_g] ++ ls,

  let f_l         := f.app_of_list ls,
  let f₂_l        := f₂.app_of_list ls,
  let f_le_func := (f_l.imp $ func_f.app_of_list ls).pis ls,

  /- define `functional` as inductive predicate -/
  func_intros   ← irules.mmap (λ⟨nr, t⟩, do
    (ls, t') ← drop_pis gs t >>= mk_local_pis,
    let ls' := ls.map $ λe, e.replace_with pred_g f,
    let t'  := t'.replace_with pred_g func_f,
    (name.mk_string sub p) ← return $ nr,
    return ((p ++ "functional") ++ sub, t'.pis $ gs ++ [f] ++ ls')),
  add_inductive func_name us (p + 1) func_type func_intros,

  /- prove monotonicity of `functional` -/
  let mono_func : expr := (imp (func_f.app_of_list ls) (func_f₂.app_of_list ls)).pis ls,
  mono ← add_theorem_by (func_name ++ "mono") us
    ((imp ((imp f_l f₂_l).pis ls) mono_func).pis $ gs ++ [f, f₂]) (do
      gs ← intro_lst gs_names,
      [f₁, f₂, hf] ← intro_lst [`f₁, `f₂, `hf],
      m ← mk_const (func_name ++ "rec"), -- `rec`'s universes are not always `us`, e.g. eq, wf, false
      apply $ m.app_of_list gs, -- somhow `induction` / `cases` doesn't work?
      focus $ func_intros.map (λ⟨n, t⟩, do
        bs ← intros,
        ms ← apply_core ((const n us').app_of_list $ gs ++ [f₂]) { all := tt },
        gs ← (ms.zip bs).mfilter (λ⟨m, d⟩, is_assigned m),
        focus $ gs.map (λ⟨m, d⟩, apply d <|> (apply hf >> apply d)))),

  /- define `pred` as fixed point of `functional` -/
  add_decl $ mk_definition n us type $
    (((const `Exists [u_f] : expr) type' ((`(and) f_le_func f_l).lambdas [f])).lambdas $ gs ++ ls),

  /- prove `corec_functional` rule -/
  corec ← add_theorem_by (n ++ "corec_functional") us
    ((f_le_func.imp ((imp f_l pred_gl).pis ls)).pis $ gs ++ [f]) (do
      intro_lst gs_names, [C, hC] ← intro_lst [`C, `hC], intro_lst ls_names, hls ← intro `hls,
      refine ``(exists.intro %%C (and.intro %%hC %%hls))),

  /- prove `destruct` rule -/
  destruct ← add_theorem_by (n ++ "destruct") us ((imp pred_gl func_pred_l).pis $ gs ++ ls) (do
    gs ← intro_lst gs_names, ls ← intro_lst ls_names, h ← intro `h,
    [([f, hf], [])] ← induction h [`f, `hf],
    [([h₁, h₂], [])] ← induction hf [`h₁, `h₂],
    apply $ mono.app_of_list $ gs ++ [f],
    exact $ corec.app_of_list $ gs ++ [f, h₁],
    exact $ h₁.app_of_list $ ls ++ [h₂]),

  /- prove `construct` rule -/
  let construct_type := (imp func_pred_l pred_gl).pis $ gs ++ ls,
  construct ← add_theorem_by (n ++ "construct") us construct_type (do
    gs ← intro_lst gs_names,
    let pred := pred.app_of_list gs,
    let func_pred := func.app_of_list $ gs ++ [pred],
    apply $ corec.app_of_list $ gs ++ [func_pred],
    apply $ mono.app_of_list $ gs ++ [pred, func_pred],
    exact $ destruct.app_of_list gs),

  /- prove constructors -/
  irules.mmap (λ⟨nr, t⟩, add_theorem_by nr us t $ do
    (name.mk_string sub p) ← return nr,
    let func_rule : expr := (const ((p ++ "functional") ++ sub) us'),
    gs ← intro_lst gs_names, bs ← intros,
    apply $ construct.app_of_list $ gs,
    exact $ func_rule.app_of_list $ gs ++ [pred.app_of_list gs] ++ bs),

  return ()

end tactic
