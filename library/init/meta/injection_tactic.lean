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
| (n+3) :=  (λ xs, none :: xs) <$> at_end₂ (n+2)
| _ := fail "at_end expected arity > 1"

private meta def mk_next_name : name → nat → tactic (name × nat)
| n i := do
  let n' := n.append_after i,
  (get_local n' >> mk_next_name n (i+1))
  <|>
  (return (n', i+1))

/- Auxiliary function for introducing the new equalities produced by the
   injection tactic. -/
private meta def injection_intro : expr → nat → list name → tactic (list expr × list name)
| (pi n bi b d) i ns := do
  (hname, i) ← if ns.empty then mk_next_name `h i else return (head ns, i),
  h ← intro hname,
  (l, ns') ← injection_intro d i (tail ns),
  return (h :: l, ns')
| e  i ns            := return ([], ns)

/- Tries to decompose the given expression by constructor injectivity.
   Returns the list of new hypotheses, and the remaining names from the given list. -/
meta def injection_with (h : expr) (ns : list name) : tactic (list expr × list name) :=
do
  ht ← infer_type h,
  (lhs0, rhs0) ← match_eq ht,
  env ← get_env,
  lhs ← whnf_ginductive lhs0,
  rhs ← whnf_ginductive rhs0,
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
      eapply pr,
      injection_intro (binding_domain pr_type) 1 ns
    else fail "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor"
  else do
    tgt ← target,
    let I_name := name.get_prefix n_fl,
    pr ← mk_app (I_name <.> "no_confusion") [tgt, lhs, rhs, h],
    exact pr,
    return ([], ns)

meta def injection (h : expr) : tactic (list expr) :=
do (t, _) ← injection_with h [], return t

private meta def injections_with_inner : nat → list expr → list name → tactic unit
| 0     lc        ns := fail "recursion depth exceeded"
| (n+1) []        ns := skip
| (n+1) (h :: lc) ns :=
  do o ← try_core (injection_with h ns), match o with
  | none          := injections_with_inner (n+1) lc ns
  | some ([], _)  := skip -- This means that the contradiction part was triggered and the goal is done
  | some (t, ns') := injections_with_inner n (t ++ lc) ns'
  end

meta def injections_with (ns : list name) : tactic unit :=
do lc ← local_context,
   injections_with_inner 5 lc ns

end tactic
