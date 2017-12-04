/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.smt_tactic init.meta.fun_info init.meta.rb_map

open tactic

private meta def add_lemma (m : transparency) (h : name) (hs : hinst_lemmas) : tactic hinst_lemmas :=
(do h ← hinst_lemma.mk_from_decl_core m h tt, return $ hs.add h) <|> return hs

private meta def to_hinst_lemmas (m : transparency) (ex : name_set) : list name → hinst_lemmas → tactic hinst_lemmas
| []      hs := return hs
| (n::ns) hs :=
  if ex.contains n then to_hinst_lemmas ns hs else
  let add n := add_lemma m n hs >>= to_hinst_lemmas ns
  in do eqns   ← tactic.get_eqn_lemmas_for tt n,
  match eqns with
  | []  := add n
  | _   := mcond (is_prop_decl n) (add n) (to_hinst_lemmas eqns hs >>= to_hinst_lemmas ns)
  end

/-- Create a rsimp attribute named `attr_name`, the attribute declaration is named `attr_decl_name`.
    The cached hinst_lemmas structure is built using the lemmas marked with simp attribute `simp_attr_name`,
    but *not* marked with `ex_attr_name`.

    We say `ex_attr_name` is the "exception set". It is useful for excluding lemmas in `simp_attr_name`
    which are not good or redundant for ematching. -/
meta def mk_hinst_lemma_attr_from_simp_attr (attr_decl_name attr_name : name) (simp_attr_name : name) (ex_attr_name : name) : command :=
do let t := `(user_attribute hinst_lemmas),
   let v := `({name     := attr_name,
               descr    := sformat!"hinst_lemma attribute derived from '{simp_attr_name}'",
               cache_cfg := {
                 mk_cache := λ ns,
                 let aux := simp_attr_name in
                 let ex_attr := ex_attr_name in
                 do {
                   hs   ← to_hinst_lemmas reducible mk_name_set ns hinst_lemmas.mk,
                   ss   ← attribute.get_instances aux,
                   ex   ← get_name_set_for_attr ex_attr,
                   to_hinst_lemmas reducible ex ss hs
                 },
                 dependencies := [`reducibility, simp_attr_name]}} : user_attribute hinst_lemmas),
   add_decl (declaration.defn attr_decl_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_decl_name

run_cmd mk_name_set_attr `no_rsimp
run_cmd mk_hinst_lemma_attr_from_simp_attr `rsimp_attr `rsimp `simp `no_rsimp

/- The following lemmas are not needed by rsimp, and they actually hurt performance since they generate a lot of
   instances. -/
attribute [no_rsimp]
  id.def ne.def not_true not_false_iff ne_self_iff_false eq_self_iff_true heq_self_iff_true iff_not_self not_iff_self
  true_iff_false false_iff_true and.comm and.assoc and.left_comm and_true true_and and_false false_and not_and_self and_not_self
  and_self or.comm or.assoc or.left_comm or_true true_or or_false false_or or_self iff_true true_iff iff_false false_iff
  iff_self implies_true_iff false_implies_iff if_t_t if_true if_false

namespace rsimp

meta def is_value_like : expr → bool
| e :=
  if ¬ e.is_app then ff
  else let fn    := e.get_app_fn in
   if ¬ fn.is_constant then ff
   else let nargs := e.get_app_num_args,
            fname := fn.const_name in
     if      fname = ``has_zero.zero ∧ nargs = 2 then tt
     else if fname = ``has_one.one ∧ nargs = 2 then tt
     else if fname = ``bit0 ∧ nargs = 3 then is_value_like e.app_arg
     else if fname = ``bit1 ∧ nargs = 4 then is_value_like e.app_arg
     else if fname = ``char.of_nat ∧ nargs = 1 then is_value_like e.app_arg
     else ff

/-- Return the size of term by considering only explicit arguments. -/
meta def explicit_size : expr → tactic nat
| e :=
  if ¬ e.is_app then return 1
  else if is_value_like e then return 1
  else fold_explicit_args e 1
    (λ n arg, do r ← explicit_size arg, return $ r + n)

/-- Choose smallest element (with respect to explicit_size) in `e`s equivalence class. -/
meta def choose (ccs : cc_state) (e : expr) : tactic expr :=
do sz ← explicit_size e,
   p  ← ccs.mfold_eqc e (e, sz) $ λ p e',
     if p.2 = 1 then return p
     else do {
       sz' ← explicit_size e',
       if sz' < p.2 then return (e', sz')
       else return p
     },
   return p.1

meta def repr_map := expr_map expr
meta def mk_repr_map := expr_map.mk expr

meta def to_repr_map (ccs : cc_state) : tactic repr_map :=
ccs.roots.mfoldl (λ S e, do r ← choose ccs e, return $ S.insert e r) mk_repr_map

meta def rsimplify (ccs : cc_state) (e : expr) (m : option repr_map := none) : tactic (expr × expr) :=
do m ← match m with
       | none   := to_repr_map ccs
       | some m := return m
       end,
   r ← simplify_top_down () (λ _ t,
         do root  ← return $ ccs.root t,
            new_t ← m.find root,
            guard (¬ new_t =ₐ t),
            prf   ← ccs.eqv_proof t new_t,
            return ((), new_t, prf))
         e,
   return r.2

structure config :=
(attr_name   := `rsimp_attr)
(max_rounds  := 8)

open smt_tactic

meta def collect_implied_eqs (cfg : config := {}) (extra := hinst_lemmas.mk) : tactic cc_state :=
do focus1 $ using_smt_with {em_attr := cfg.attr_name} $
   do
     add_lemmas_from_facts,
     add_lemmas extra,
     iterate_at_most cfg.max_rounds (ematch >> try smt_tactic.close),
     (done >> return cc_state.mk)
     <|>
     to_cc_state

meta def rsimplify_goal (ccs : cc_state) (m : option repr_map := none) : tactic unit :=
do t           ← target,
   (new_t, pr) ← rsimplify ccs t m,
   try (replace_target new_t pr)

meta def rsimplify_at (ccs : cc_state) (h : expr) (m : option repr_map := none) : tactic unit :=
do when (expr.is_local_constant h = ff) (tactic.fail "tactic rsimplify_at failed, the given expression is not a hypothesis"),
   htype            ← infer_type h,
   (new_htype, heq) ← rsimplify ccs htype m,
   try $ do assert (expr.local_pp_name h) new_htype,
            mk_eq_mp heq h >>= exact,
            try $ clear h
end rsimp

open rsimp

namespace tactic

meta def rsimp (cfg : config := {}) (extra := hinst_lemmas.mk) : tactic unit :=
do ccs ← collect_implied_eqs cfg extra,
   try $ rsimplify_goal ccs

meta def rsimp_at (h : expr) (cfg : config := {}) (extra := hinst_lemmas.mk) : tactic unit :=
do ccs ← collect_implied_eqs cfg extra,
   try $ rsimplify_at ccs h

namespace interactive

/- TODO(Leo): allow user to provide extra lemmas manually -/
meta def rsimp : tactic unit :=
tactic.rsimp

end interactive
end tactic
