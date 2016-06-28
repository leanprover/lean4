/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.format init.function

/- Function parameter information

   Remark: specialized is tt if the result of fun_info has been specifialized
   using this argument.
   For example, consider the function

            f : Pi (A : Type), A -> A

   Now, suppse we request specialized_fun_info for the application

             f unit a

   the tactic returns two param_info values:
   1) specialized = tt,     has_fwd_dep = tt
   2) is_subsingleton = tt, back_deps = [0]

   Note that, in general, the second argument of f is not a subsingleton,
   but it is in this particular case/specialization.

   This bit is only set if it is a dependent parameter (i.e., has_fwd_dep is tt).

   Moreover, we only set specialized IF another parameter
   becomes a subsingleton or proposition. -/
structure param_info :=
(specialized      : bool)
(is_implicit      : bool)
(is_inst_implicit : bool)
(is_prop          : bool)
(is_subsingleton  : bool)
(has_fwd_deps     : bool)
(back_deps        : list nat) -- previous parameters it depends on

open format list decidable

private meta_definition ppfield {A : Type} [has_to_format A] (fname : string) (v : A) : format :=
group $ fname ++ space ++ ":=" ++ space ++ nest (length fname + 4) (to_fmt v)

private meta_definition concat_fields (f₁ f₂ : format) : format :=
if       is_nil f₁ = tt then f₂
else if  is_nil f₂ = tt then f₁
else f₁ ++ "," ++ line ++ f₂

local infix `+++`:65 := concat_fields

meta_definition param_info.to_format : param_info → format
| (param_info.mk s i ii p s d ds) :=
group ∘ cbrace $
  when s "specialized" +++
  when i  "implicit" +++
  when ii "inst_implicit" +++
  when p  "prop" +++
  when s  "subsingleton" +++
  when d  "has_fwd_deps" +++
  when (to_bool (length ds > 0)) ("back_deps := " ++ to_fmt ds)

meta_definition param_info.has_to_format [instance] : has_to_format param_info :=
has_to_format.mk param_info.to_format

structure fun_info :=
(params      : list param_info)
(result_deps : list nat) -- parameters the result type depends on

meta_definition fun_info.to_format : fun_info → format
| (fun_info.mk ps ds) :=
group ∘ dcbrace $
  ppfield "params" ps ++
  ppfield "result_deps" ds

meta_definition fun_info.has_to_format [instance] : has_to_format fun_info :=
has_to_format.mk fun_info.to_format

namespace tactic
meta_constant get_fun_info_core   : transparency → expr → tactic fun_info
/- (get_fun_info fn n) return information assuming the function has only n arguments.
   The tactic fail if n > length (params (get_fun_info fn)) -/
meta_constant get_fun_info_n_core : transparency → expr → nat → tactic fun_info
/- (get_spec_func_info t) return information for the function application t of the form
   (f a_1 ... a_n).
   This tactic is more precise than (get_fun_info f) and (get_fun_info_n f)

    Example: given (f : Pi (A : Type), A -> A), \c get_spec_func_info for

    f unit b

    returns a fun_info with two param_info
    1) specialized = tt, has_fwd_deps = tt
    2) is_subsingleton = tt, back_deps = [0]

    The second argument is marked as subsingleton only because the resulting information
    is taking into account the first argument.

    Remark: get_fun_info and get_spec_func_info return the same result for all but
    is_prop and is_subsingleton. -/
meta_constant get_spec_fun_info_core   : transparency → expr → tactic fun_info
meta_constant get_spec_prefix_size_core : transparency → expr → nat → tactic nat

meta_definition get_fun_info : expr → tactic fun_info :=
get_fun_info_core semireducible

meta_definition get_fun_info_n : expr → nat → tactic fun_info :=
get_fun_info_n_core semireducible

meta_definition get_spec_fun_info : expr → tactic fun_info :=
get_spec_fun_info_core semireducible

meta_definition get_spec_prefix_size : expr → nat → tactic nat :=
get_spec_prefix_size_core semireducible
end tactic
