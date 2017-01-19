/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.rb_map
open tactic

private meta def apply_replacement (env : environment) (replacements : name_map name) (e : expr) : expr :=
e^.replace (λ e d,
  match e with
  | expr.const n ls :=
    match replacements^.find n with
    | some new_n := some (expr.const new_n ls)
    | none       := none
    end
  | _ := none
  end)

/- Given a set of constant renamings `replacements` and a declaration name `src_decl_name`, create a new
   declaration called `new_decl_name` s.t. its type is the type of `src_decl_name` after applying the
   given constant replacement.

   Remark: the new type must be definitionally equal to the type of `src_decl_name`.

   Example:
   Assume the environment contains
        def f : nat -> nat  := ...
        def g : nat -> nat  := f
        lemma f_lemma : forall a, f a > 0 := ...

   Moreover, assume we have a mapping M containing `f -> `g
   Then, the command
        run_command copy_decl_updating_type M `f_lemma `g_lemma
   creates the declaration
        lemma g_lemma : forall a, g a > 0 := ... -/
meta def copy_decl_updating_type (replacements : name_map name) (src_decl_name : name) (new_decl_name : name) : command :=
do env       ← get_env,
   decl      ← returnex $ env^.get src_decl_name,
   new_type  ← return $ apply_replacement env replacements decl^.type,
   new_value ← return $ expr.const src_decl_name (decl^.univ_params^.for level.param),
   add_decl (((decl^.to_definition^.update_type new_type)^.update_name new_decl_name)^.update_value new_value),
   return ()

meta def copy_decl_using (replacements : name_map name) (src_decl_name : name) (new_decl_name : name) : command :=
do env       ← get_env,
   decl      ← returnex $ env^.get src_decl_name,
   new_type  ← return $ apply_replacement env replacements decl^.type,
   new_value ← return $ apply_replacement env replacements decl^.value,
   add_decl (((decl^.to_definition^.update_type new_type)^.update_name new_decl_name)^.update_value new_value),
   return ()
