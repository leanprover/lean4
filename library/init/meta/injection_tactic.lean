/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open nat tactic environment expr list

private meta def mk_intro_name : name → list name → name
| n₁ (n₂ :: ns) := n₂
| n  []         := if n = `a then `H else n

-- Auxiliary function for introducing the new equalities produced by the
-- injection tactic
private meta def injection_intro : expr → list name → tactic unit
| (pi n bi b d) ns := do
  Hname ← return $ mk_intro_name n ns,
  H ← intro Hname,
  Ht ← infer_type H,
  -- Clear new hypothesis if it is of the form (a = a)
  @try unit $ do {
    (lhs, rhs) ← match_eq Ht,
    unify lhs rhs,
    clear H },
  -- If new hypothesis is of the form (@heq A a B b) where
  -- A and B can be unified then convert it into (a = b) using
  -- the eq_of_heq lemma
  @try unit $ do {
    (A, lhs, B, rhs) ← match_heq Ht,
    unify A B,
    Heq ← mk_app `eq [lhs, rhs],
    pr  ← mk_app `eq_of_heq [H],
    assertv Hname Heq pr,
    clear H },
  injection_intro d (tail ns)
| e  ns           := skip

meta def injection_with (H : expr) (ns : list name) : tactic unit :=
do
  Ht ← infer_type H,
  (lhs, rhs) ← match_eq Ht,
  env ← get_env,
  if is_constructor_app env lhs ∧
     is_constructor_app env rhs ∧
     const_name (get_app_fn lhs) = const_name (get_app_fn rhs)
  then do
    tgt    ← target,
    I_name ← return $ name.get_prefix (const_name (get_app_fn lhs)),
    pr     ← mk_app (I_name <.> "no_confusion") [tgt, lhs, rhs, H],
    pr_type ← infer_type pr,
    pr_type ← whnf pr_type,
    apply pr,
    injection_intro (binding_domain pr_type) ns
  else fail "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor"

meta def injection (H : expr) : tactic unit :=
injection_with H []

end tactic
