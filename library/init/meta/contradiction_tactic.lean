/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

open expr tactic option bool decidable environment

private meta_definition contra_A_not_A : list expr → list expr → tactic unit
| []         Hs := failed
| (H1 :: Rs) Hs :=
  do t ← infer_type H1,
     if is_not t = tt
     then ((do H2 ← find_same_type (app_arg t) Hs,
               tgt ← target,
               pr ← mk_app "absurd" [tgt, H2, H1],
               exact pr) <|> contra_A_not_A Rs Hs)
     else contra_A_not_A Rs Hs

private meta_definition contra_false : list expr → tactic unit
| []        := failed
| (H :: Hs) :=
  do t ← infer_type H,
     if is_false t = tt
     then do tgt ← target,
             pr  ← mk_app ("false" <.> "rec") [tgt, H],
             exact pr
     else contra_false Hs

private meta_definition contra_constructor_eq : list expr → tactic unit
| []        := failed
| (H :: Hs) :=
  do t ← infer_type H,
     match is_eq t with
     | some (lhs_0, rhs_0) :=
       do env ← get_env,
          lhs ← whnf lhs_0,
          rhs ← whnf rhs_0,
          if is_constructor_app env lhs = tt ∧
             is_constructor_app env rhs = tt ∧
             const_name (get_app_fn lhs) ≠ const_name (get_app_fn rhs)
          then do tgt    ← target,
                  I_name ← return (name.get_prefix (const_name (get_app_fn lhs))),
                  pr ← mk_app (I_name <.> "no_confusion") [tgt, lhs, rhs, H],
                  exact pr
          else contra_constructor_eq Hs
     | none := contra_constructor_eq Hs
     end

meta_definition tactic.contradiction : tactic unit :=
do ctx ← local_context,
   (contra_false ctx <|>
    contra_A_not_A ctx ctx <|>
    contra_constructor_eq ctx <|>
    fail "contradiction tactic failed")

open tactic

example : ∀ (a b : nat), (0:nat) = 1 → a = b :=
by do intros, contradiction
