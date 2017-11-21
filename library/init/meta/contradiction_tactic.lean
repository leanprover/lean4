/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic

open expr tactic decidable environment

private meta def contra_p_not_p : list expr → list expr → tactic unit
| []         Hs := failed
| (H1 :: Rs) Hs :=
  do t ← (extract_opt_auto_param <$> infer_type H1) >>= whnf,
     (do a   ← match_not t,
         H2  ← find_same_type a Hs,
         tgt ← target,
         pr  ← mk_app `absurd [tgt, H2, H1],
         exact pr)
     <|> contra_p_not_p Rs Hs

private meta def contra_false : list expr → tactic unit
| []        := failed
| (H :: Hs) :=
  do t ← extract_opt_auto_param <$> infer_type H,
     if is_false t
     then do tgt ← target,
             pr  ← mk_app `false.rec [tgt, H],
             exact pr
     else contra_false Hs

private meta def contra_not_a_refl_rel_a : list expr → tactic unit
| []        := failed
| (H :: Hs) :=
  do t ← (extract_opt_auto_param <$> infer_type H) >>= head_beta,
     (do (lhs, rhs) ← match_ne t,
         unify lhs rhs,
         tgt ← target,
         refl_pr ← mk_app `eq.refl [lhs],
         mk_app `absurd [tgt, refl_pr, H] >>= exact)
     <|>
     (do p ← match_not t,
         (refl_lemma, lhs, rhs) ← match_refl_app p,
         unify lhs rhs,
         tgt ← target,
         refl_pr ← mk_app refl_lemma [lhs],
         mk_app `absurd [tgt, refl_pr, H] >>= exact)
     <|>
     contra_not_a_refl_rel_a Hs

private meta def contra_constructor_eq : list expr → tactic unit
| []        := failed
| (H :: Hs) :=
  do t ← (extract_opt_auto_param <$> infer_type H) >>= whnf,
     match t with
     | `((%%lhs_0 : %%α) = %%rhs_0) :=
       do env ← get_env,
          lhs ← whnf lhs_0,
          rhs ← whnf rhs_0,
          if is_constructor_app env lhs ∧
             is_constructor_app env rhs ∧
             const_name (get_app_fn lhs) ≠ const_name (get_app_fn rhs)
          then do tgt    ← target,
                  I_name ← return $ name.get_prefix (const_name (get_app_fn lhs)),
                  pr ← mk_app (I_name <.> "no_confusion") [tgt, lhs, rhs, H],
                  exact pr
          else contra_constructor_eq Hs
     | _ := contra_constructor_eq Hs
     end

meta def contradiction : tactic unit :=
do try intro1,
   ctx ← local_context,
   (contra_false ctx <|>
    contra_not_a_refl_rel_a ctx <|>
    contra_p_not_p ctx ctx <|>
    contra_constructor_eq ctx <|>
    fail "contradiction tactic failed")

meta def exfalso : tactic unit :=
do fail_if_no_goals,
   assert `Hfalse (expr.const `false []),
   swap, contradiction

end tactic
