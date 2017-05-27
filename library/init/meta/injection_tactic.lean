/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open nat tactic environment expr list

private meta def at_end₂ (e₁ e₂ : expr) : ℕ → tactic (list (option expr))
| 2 := return [some e₁, some e₂]
| (n+3) := at_end₂ (n+2) >>= (λ xs, return (none :: xs))
| _ := fail "at_end expected arity > 1"

private meta def mk_intro_name : name → list name → name
| n₁ (n₂ :: ns) := n₂
| n  []         := if n = `a then `h else n

-- Auxiliary function for introducing the new equalities produced by the
-- injection tactic
private meta def injection_intro : expr → list name → tactic unit
| (pi n bi b d) ns := do
  hname ← return $ mk_intro_name n ns,
  h ← intro hname,
  injection_intro d (tail ns)

| e  ns           := skip

meta def injection_with (h : expr) (ns : list name) : tactic unit :=
do
  ht ← infer_type h,
  (lhs0, rhs0) ← match_eq ht,
  env ← get_env,
  lhs ← whnf lhs0,
  rhs ← whnf rhs0,
  let n_fl := const_name (get_app_fn lhs),
  let n_fr := const_name (get_app_fn rhs),
  if n_fl = n_fr then do
    let n_inj := n_fl <.> "inj_arrow",
    if env.contains n_inj then do
      c_inj  ← mk_const n_inj,
      arity  ← get_arity c_inj,
      tgt ← target,
      args   ← at_end₂ h tgt (arity - 1),
      pr     ← mk_mapp n_inj args,
      pr_type ← infer_type pr,
      pr_type ← whnf pr_type,
      apply pr,
      injection_intro (binding_domain pr_type) ns
    else fail "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor"
  else do
    tgt ← target,
    let I_name := name.get_prefix n_fl,
    mk_app (I_name <.> "no_confusion") [tgt, lhs, rhs, h] >>= exact

meta def injection (h : expr) : tactic unit :=
injection_with h []

end tactic
