prelude
import init.lean.name

/-
This is a temporary file to document all macros we have in Lean3.
Macros will not be part of Lean4, but we need to keep them until
we can bootstrap Lean4.
-/
namespace lean

structure equations_header :=
(num_fns          : nat)
(fn_names         : list name)
(fn_actual_names  : list name)
(is_private       : bool)
(is_lemma         : bool)
(is_meta          : bool)
(is_noncomputable : bool)
(aux_lemmas       : bool)
(prev_errors      : bool)
(gen_code         : bool)

/-
Cases missing:
1- projection  -- It will be a primitive
-/

inductive macro_definition
/- The following macros will be Syntax object in Lean4 -/
| equations       : equations_header → macro_definition


end lean
