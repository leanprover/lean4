/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open nat tactic option environment bool expr list

private meta_definition mk_intro_name : name → list name → name
| n₁ (n₂ :: ns) := n₂
| n  []         := if n = "a" then "H" else n

-- Auxiliary function for introducing the new equalities produced by the
-- injection tactic
private meta_definition injection_intro : expr → list name → tactic unit
| (pi n bi b d) ns := do
  Hname ← return $ mk_intro_name n ns,
  H ← intro Hname,
  Ht ← infer_type H,
  match is_eq Ht with
  | some (lhs, rhs) :=
    -- Clear new hypothesis if it is of the form (a = a)
    do {unify lhs rhs, clear H} <|> skip
  | none :=
    match is_heq Ht with
    | some (A, lhs, B, rhs) :=
      do {
        -- If new hypothesis is of the form (@heq A a B b) where
        -- A and B can be unified then convert it into (a = b) using
        -- the eq_of_heq lemma
        unify A B,
        Heq ← mk_app "eq" [lhs, rhs],
        pr  ← mk_app "eq_of_heq" [H],
        assertv Hname Heq pr,
        clear H
      }
      <|> skip
    | none                  := skip
    end
  end,
  injection_intro d (tail ns)
| e  ns           := skip

meta_definition injection_with (H : expr) (ns : list name) : tactic unit :=
do
  Ht ← infer_type H,
  match expr.is_eq Ht with
  | some (lhs, rhs) := do
    env ← get_env,
    if is_constructor_app env lhs = tt ∧
       is_constructor_app env rhs = tt ∧
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
  | none            := fail "injection tactic failed, argument must be an equality proof"
  end

meta_definition injection (H : expr) : tactic unit :=
injection_with H []

end tactic
