/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive_base init.function

namespace tactic
meta structure pattern :=
/- Term to match. -/
(target : expr)
/- Set of universes that is instantiated for each successful match. -/
(uoutput : list level)
/- Set of terms that is instantiated for each successful match. -/
(moutput : list expr)
/- Number of (temporary) universe meta-variables in this pattern. -/
(nuvars : nat)
/- Number of (temporary) meta-variables in this pattern. -/
(nmvars : nat)

/-- `mk_pattern ls es t u o` creates a new pattern with (length ls) universe meta-variables and (length es) meta-variables.
   In the produced pattern p, we have that
   - `pattern.target p` is the term t where the universes ls and expressions es have been replaced with temporary meta-variables.
   - `pattern.uoutput p` is the list u where the universes ls have been replaced with temporary meta-variables.
   - `pattern.moutput p` is the list o where the universes ls and expressions es have been replaced with temporary meta-variables.
   - `pattern.nuvars p` = length ls
   - `pattern.nmvars p` = length es

   The tactic fails if o and the types of es do not contain all universes ls and expressions es. -/
meta constant mk_pattern : list level → list expr → expr → list level → list expr → tactic pattern
/-- `mk_pattern p e m` matches (pattern.target p) and e using transparency m.
   If the matching is successful, then return the instantiation of `pattern.output p`.
   The tactic fails if not all (temporary) meta-variables are assigned. -/
meta constant match_pattern (p : pattern) (e : expr) (m : transparency := reducible) : tactic (list level × list expr)

open expr

/- Helper function for converting a term (λ x_1 ... x_n, t) into a pattern
   where x_1 ... x_n are metavariables -/
private meta def to_pattern_core : expr → tactic (expr × list expr)
| (lam n bi d b) := do
   id         ← mk_fresh_name,
   let x     := local_const id n bi d,
   let new_b := instantiate_var b x,
   (p, xs) ← to_pattern_core new_b,
   return (p, x::xs)
| e              := return (e, [])

/-- Given a pre-term of the form `λ x_1 ... x_n, t[x_1, ..., x_n]`, converts it
   into the pattern `t[?x_1, ..., ?x_n]` -/
meta def pexpr_to_pattern (p : pexpr) : tactic pattern :=
do /- Remark: in the following to_expr, we allow metavars but we do *not* create new goals for them.
      mk_pattern will convert them into temporary metavars. -/
   e ← to_expr p tt ff,
   (new_p, xs) ← to_pattern_core e,
   mk_pattern [] xs new_p [] xs

/-- Convert pre-term into a pattern and try to match e.
   Given p of the form `λ x_1 ... x_n, t[x_1, ..., x_n]`, a successful
   match will produce a list of length n. -/
meta def match_expr (p : pexpr) (e : expr) (m := reducible) : tactic (list expr) :=
do new_p ← pexpr_to_pattern p,
   prod.snd <$> match_pattern new_p e m

private meta def match_subexpr_core (m : transparency) : pattern → list expr → tactic (list expr)
| p []      := failed
| p (e::es) :=
  (prod.snd <$> match_pattern p e m)
  <|>
  match_subexpr_core p es
  <|>
  if is_app e then match_subexpr_core p (get_app_args e)
  else failed

/-- Similar to match_expr, but it tries to match a subexpression of e.
   Remark: the procedure does not go inside binders. -/
meta def match_subexpr (p : pexpr) (e : expr) (m := reducible) : tactic (list expr) :=
do new_p ← pexpr_to_pattern p,
   match_subexpr_core m new_p [e]

/-- Match the main goal target. -/
meta def match_target (p : pexpr) (m := reducible) : tactic (list expr) :=
do t ← target, match_expr p t m

/-- Match a subterm in the main goal target. -/
meta def match_target_subexpr (p : pexpr) (m := reducible) : tactic (list expr) :=
do t ← target, match_subexpr p t m

private meta def match_hypothesis_core (m : transparency) : pattern → list expr → tactic (expr × list expr)
| p []      := failed
| p (h::hs) := do
  h_type ← infer_type h,
  (do r ← match_pattern p h_type m, return (h, r.snd))
  <|>
  match_hypothesis_core p hs

/-- Match hypothesis in the main goal target.
   The result is pair (hypothesis, substitution). -/
meta def match_hypothesis (p : pexpr) (m := reducible) : tactic (expr × list expr) :=
do ctx ← local_context,
   new_p ← pexpr_to_pattern p,
   match_hypothesis_core m new_p ctx

meta instance : has_to_tactic_format pattern :=
⟨λp, do
  t ← pp p.target,
  mo ← pp p.moutput,
  uo ← pp p.uoutput,
  u ← pp p.nuvars,
  m ← pp p.nmvars,
  return format!"pattern.mk ({t}) {uo} {mo} {u} {m}" ⟩

end tactic
