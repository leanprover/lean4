/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.format init.function

structure param_info :=
(is_implicit      : bool)
(is_inst_implicit : bool)
(is_prop          : bool)
(has_fwd_deps     : bool)
(back_deps        : list nat) -- previous parameters it depends on

open format list decidable

private meta def ppfield {α : Type} [has_to_format α] (fname : string) (v : α) : format :=
group $ to_fmt fname ++ space ++ to_fmt ":=" ++ space ++ nest (fname.length + 4) (to_fmt v)

private meta def concat_fields (f₁ f₂ : format) : format :=
if       is_nil f₁ then f₂
else if  is_nil f₂ then f₁
else f₁ ++ to_fmt "," ++ line ++ f₂

local infix `+++`:65 := concat_fields

meta def param_info.to_format : param_info → format
| (param_info.mk i ii p d ds) :=
group ∘ cbrace $
  when i  "implicit" +++
  when ii "inst_implicit" +++
  when p  "prop" +++
  when d  "has_fwd_deps" +++
  when (length ds > 0) (to_fmt "back_deps := " ++ to_fmt ds)

meta instance : has_to_format param_info :=
has_to_format.mk param_info.to_format

structure fun_info :=
(params      : list param_info)
(result_deps : list nat) -- parameters the result type depends on

meta def fun_info_to_format : fun_info → format
| (fun_info.mk ps ds) :=
group ∘ dcbrace $
  ppfield "params" ps +++
  ppfield "result_deps" ds

meta instance : has_to_format fun_info :=
has_to_format.mk fun_info_to_format

/--
  specialized is true if the result of fun_info has been specifialized
  using this argument.
  For example, consider the function

             f : Pi (α : Type), α -> α

  Now, suppse we request get_specialize fun_info for the application

         f unit a

  fun_info_manager returns two param_info objects:
  1) specialized = true
  2) is_subsingleton = true

  Note that, in general, the second argument of f is not a subsingleton,
  but it is in this particular case/specialization.

  \remark This bit is only set if it is a dependent parameter.

   Moreover, we only set is_specialized IF another parameter
   becomes a subsingleton -/
structure subsingleton_info :=
(specialized     : bool)
(is_subsingleton : bool)

meta def subsingleton_info_to_format : subsingleton_info → format
| (subsingleton_info.mk s ss) :=
group ∘ cbrace $
  when s  "specialized" +++
  when ss "subsingleton"

meta instance : has_to_format subsingleton_info :=
has_to_format.mk subsingleton_info_to_format

namespace tactic

/-- If nargs is not none, then return information assuming the function has only nargs arguments. -/
meta constant get_fun_info (f : expr) (nargs : option nat := none) (md := semireducible) : tactic fun_info
meta constant get_subsingleton_info (f : expr) (nargs : option nat := none) (md := semireducible) : tactic (list subsingleton_info)

/-- `get_spec_subsingleton_info t` return subsingleton parameter
   information for the function application t of the form
      `f a_1 ... a_n`.

    This tactic is more precise than `get_subsingleton_info f` and `get_subsingleton_info_n f n`

    Example: given `f : Pi (α : Type), α -> α`, `get_spec_subsingleton_info` for

    `f unit b`

    returns a fun_info with two param_info
    1) specialized = tt
    2) is_subsingleton = tt

    The second argument is marked as subsingleton only because the resulting information
    is taking into account the first argument. -/
meta constant get_spec_subsingleton_info (t : expr) (md := semireducible) : tactic (list subsingleton_info)
meta constant get_spec_prefix_size (t : expr) (nargs : nat) (md := semireducible) : tactic nat

private meta def is_next_explicit : list param_info → bool
| []      := tt
| (p::ps) := bnot p.is_implicit && bnot p.is_inst_implicit

meta def fold_explicit_args_aux {α} (f : α → expr → tactic α) : list expr → list param_info → α → tactic α
| []      _  a := return a
| (e::es) ps a :=
  if is_next_explicit ps
  then f a e >>= fold_explicit_args_aux es ps.tail
  else fold_explicit_args_aux es ps.tail a

meta def fold_explicit_args {α} (e : expr) (a : α) (f : α → expr → tactic α) : tactic α :=
if e.is_app then do
  info ← get_fun_info e.get_app_fn (some e.get_app_num_args),
  fold_explicit_args_aux f e.get_app_args info.params a
else return a

end tactic
