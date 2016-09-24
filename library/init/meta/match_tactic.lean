/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
structure pattern :=
/- Term to match. -/
(target : expr)
/- Set of terms that is instantiated for each successful match. -/
(output : list expr)
/- Number of (temporary) universe meta-variables in this pattern. -/
(nuvars : nat)
/- Number of (temporary) meta-variables in this pattern. -/
(nmvars : nat)

/- (mk_pattern ls es t o) creates a new pattern with (length ls) universe meta-variables and (length es) meta-variables.
   In the produced pattern p, we have that
   - (pattern.target p) is the term t where the universes ls and expressions es have been replaced with temporary meta-variables.
   - (pattern.output p) is the list o where the universes ls and expressions es have been replaced with temporary meta-variables.
   - (pattern.nuvars p) = length ls
   - (pattern.nmvars p) = length es

   The tactic fails if o and the types of es do not contain all universes ls and expressions es. -/
meta constant mk_pattern : list level → list expr → expr → list expr → tactic pattern
/- (mk_pattern_core m p e) matches (pattern.target p) and e using transparency m.
   If the matching is successful, then return the instantiation of (pattern.output p).
   The tactic fails if not all (temporary) meta-variables are assigned. -/
meta constant match_pattern_core : transparency → pattern → expr → tactic (list expr)

meta definition match_pattern : pattern → expr → tactic (list expr) :=
match_pattern_core semireducible

open expr

/- Helper function for converting a term (λ x_1 ... x_n, t) into a pattern
   where x_1 ... x_n are metavariables -/
private meta definition to_pattern_core : expr → tactic (expr × list expr)
| (lam n bi d b) := do
   id      ← mk_fresh_name,
   x       ← return $ local_const id n bi d,
   new_b   ← return $ instantiate_var b x,
   (p, xs) ← to_pattern_core new_b,
   return (p, x::xs)
| e             := return (e, [])

/- Given a pre-term of the form (λ x_1 ... x_n, t[x_1, ..., x_n]), converts it
   into the pattern t[?x_1, ..., ?x_n] -/
meta definition pexpr_to_pattern (p : pexpr) : tactic pattern :=
do e ← to_expr p,
   (new_p, xs) ← to_pattern_core e,
   mk_pattern [] xs new_p xs

/- Convert pre-term into a pattern and try to match e.
   Given p of the form (λ x_1 ... x_n, t[x_1, ..., x_n]), a successful
   match will produce a list of length n. -/
meta definition match_expr (p : pexpr) (e : expr) : tactic (list expr) :=
do new_p ← pexpr_to_pattern p,
   match_pattern new_p e

private meta definition match_subexpr_core : pattern → list expr → tactic (list expr)
| p []      := failed
| p (e::es) :=
  match_pattern p e
  <|>
  match_subexpr_core p es
  <|>
  if is_app e then match_subexpr_core p (get_app_args e)
  else failed

/- Similar to match_expr, but it tries to match a subexpression of e.
   Remark: the procedure does not go inside binders. -/
meta definition match_subexpr (p : pexpr) (e : expr) : tactic (list expr) :=
do new_p ← pexpr_to_pattern p,
   match_subexpr_core new_p [e]

/- Match the main goal target. -/
meta definition match_target (p : pexpr) : tactic (list expr) :=
target >>= match_expr p

/- Match a subterm in the main goal target. -/
meta definition match_target_subexpr (p : pexpr) : tactic (list expr) :=
target >>= match_subexpr p

private meta definition match_hypothesis_core : pattern → list expr → tactic (expr × list expr)
| p []      := failed
| p (h::hs) := do
  h_type ← infer_type h,
  (do r ← match_pattern p h_type, return (h, r))
  <|>
  match_hypothesis_core p hs

/- Match hypothesis in the main goal target.
   The result is pair (hypothesis, substitution). -/
meta definition match_hypothesis (p : pexpr) : tactic (expr × list expr) :=
do ctx ← local_context,
   new_p ← pexpr_to_pattern p,
   match_hypothesis_core new_p ctx

end tactic
