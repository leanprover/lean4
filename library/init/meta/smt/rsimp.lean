/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.smt_tactic init.meta.fun_info init.meta.rb_map

open tactic

meta def mk_hinst_lemma_attr_from_simp_attr (attr_decl_name attr_name : name) (simp_attr_name : name) : command :=
do t  ← to_expr `(caching_user_attribute hinst_lemmas),
   v  ← to_expr `({ name     := %%(quote attr_name),
                    descr    := "hinst_lemma attribute derived from '" ++ to_string %%(quote simp_attr_name) ++ "'",
                    mk_cache := λ ns,
                    let aux := %%(quote simp_attr_name) in
                    do {
                      hs   ← to_hinst_lemmas_core reducible tt tt ns hinst_lemmas.mk,
                      ss   ← attribute.get_instances aux,
                      to_hinst_lemmas_core reducible tt tt ss hs
                    },
                    dependencies := [`reducibility, %%(quote simp_attr_name)]} : caching_user_attribute hinst_lemmas),
   add_decl (declaration.defn attr_decl_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_decl_name

run_command mk_hinst_lemma_attr_from_simp_attr `rsimp_attr `rsimp `simp

namespace rsimp

meta def is_value_like : expr → bool
| e :=
  if ¬ e^.is_app then ff
  else let fn    := e^.get_app_fn in
   if ¬ fn^.is_constant then ff
   else let nargs := e^.get_app_num_args,
            fname := fn^.const_name in
     if      fname = `zero ∧ nargs = 2 then tt
     else if fname = `one ∧ nargs = 2 then tt
     else if fname = `bit0 ∧ nargs = 3 then is_value_like e^.app_arg
     else if fname = `bit1 ∧ nargs = 4 then is_value_like e^.app_arg
     else if fname = `char.of_nat ∧ nargs = 1 then is_value_like e^.app_arg
     else ff

/-- Return the size of term by considering only explicit arguments. -/
meta def explicit_size : expr → tactic nat
| e :=
  if ¬ e^.is_app then return 1
  else if is_value_like e then return 1
  else fold_explicit_args e 1
    (λ n arg, do r ← explicit_size arg, return $ r + n)

/-- Choose smallest element (with respect to explicit_size) in `e`s equivalence class. -/
meta def choose (ccs : cc_state) (e : expr) : tactic expr :=
do sz ← explicit_size e,
   p  ← ccs^.mfold_eqc e (e, sz) $ λ p e',
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
mfoldl (λ S e, do r ← choose ccs e, return $ S^.insert e r) mk_repr_map ccs^.roots

meta def rsimplify (ccs : cc_state) (e : expr) (m : option repr_map := none) : tactic (expr × expr) :=
do m ← match m with
       | none   := to_repr_map ccs
       | some m := return m
       end,
   r ← simplify_top_down () (λ _ t,
         do root  ← return $ ccs^.root t,
            new_t ← m^.find root,
            guard (¬ new_t =ₐ t),
            prf   ← ccs^.eqv_proof t new_t,
            return ((), new_t, prf))
         e,
   return r.2

structure config :=
(attr_name   := `rsimp_attr)
(max_rounds  := 8)

open smt_tactic

meta def collect_implied_eqs (cfg : config := {}) (extra := hinst_lemmas.mk) : tactic cc_state :=
do focus1 $ using_smt_with {em_attr := cfg^.attr_name} $
   do
     add_lemmas_from_facts,
     add_lemmas extra,
     repeat_at_most cfg^.max_rounds (ematch >> try smt_tactic.close),
     (now >> return cc_state.mk)
     <|>
     to_cc_state

meta def rsimplify_goal (ccs : cc_state) (m : option repr_map := none) : tactic unit :=
do t           ← target,
   (new_t, pr) ← rsimplify ccs t m,
   try (replace_target new_t pr)

meta def rsimplify_at (ccs : cc_state) (h : expr) (m : option repr_map := none) : tactic unit :=
do tactic.when (expr.is_local_constant h = ff) (tactic.fail "tactic rsimplify_at failed, the given expression is not a hypothesis"),
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
