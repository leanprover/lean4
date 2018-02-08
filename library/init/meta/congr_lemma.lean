/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.format init.function

inductive congr_arg_kind
/- It is a parameter for the congruence lemma, the parameter occurs in the left and right hand sides. -/
| fixed
/- It is not a parameter for the congruence lemma, the lemma was specialized for this parameter.
   This only happens if the parameter is a subsingleton/proposition, and other parameters depend on it. -/
| fixed_no_param
/- The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i = b_i).
   a_i and b_i represent the left and right hand sides, and eq_i is a proof for their equality. -/
| eq
/- congr-simp lemma contains only one parameter for this kind of argument, and congr-lemmas contains two.
   They correspond to arguments that are subsingletons/propositions. -/
| cast
/- The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i == b_i).
   a_i and b_i represent the left and right hand sides, and eq_i is a proof for their heterogeneous equality. -/
| heq

meta structure congr_lemma :=
(type : expr) (proof : expr) (arg_kinds : list congr_arg_kind)

namespace tactic
/--
Create a congruence lemma for the simplifier using h,
if nargs is not none, then it tries to create a lemma for an application of arity nargs.
-/
meta constant mk_congr_lemma_simp (h : expr) (nargs : option nat := none) (md := semireducible) : tactic congr_lemma
/- Create a specialized theorem using (a prefix of) the arguments of the given application. -/
meta constant mk_specialized_congr_lemma_simp (h : expr) (md : transparency := semireducible) : tactic congr_lemma

meta constant mk_congr_lemma (h : expr) (nargs : option nat := none) (md := semireducible) : tactic congr_lemma
/- Create a specialized theorem using (a prefix of) the arguments of the given application. -/
meta constant mk_specialized_congr_lemma (h : expr) (md := semireducible) : tactic congr_lemma

meta constant mk_hcongr_lemma (h : expr) (nargs : option nat := none) (md := semireducible) : tactic congr_lemma

end tactic
