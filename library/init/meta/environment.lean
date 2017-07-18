/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.declaration init.meta.exceptional init.data.option.basic
import init.meta.rb_map

meta constant environment : Type

namespace environment
/--
Information for a projection declaration
- `cname`    is the name of the constructor associated with the projection.
- `nparams`  is the number of constructor parameters
- `idx`      is the parameter being projected by this projection
- `is_class` is tt iff this is a class projection.
-/
structure projection_info :=
(cname : name)
(nparams : nat)
(idx : nat)
(is_class : bool)

/-- Create a standard environment using the given trust level -/
meta constant mk_std          : nat → environment
/-- Return the trust level of the given environment -/
meta constant trust_lvl       : environment → nat
/-- Add a new declaration to the environment -/
meta constant add             : environment → declaration → exceptional environment
/-- Retrieve a declaration from the environment -/
meta constant get             : environment → name → exceptional declaration
meta def      contains (env : environment) (d : name) : bool :=
match env.get d with
| exceptional.success _      := tt
| exceptional.exception ._ _ := ff
end
/-- Register the given name as a namespace, making it available to the `open` command -/
meta constant add_namespace   : environment → name → environment
/-- Return tt iff the given name is a namespace -/
meta constant is_namespace    : environment → name → bool
/-- Add a new inductive datatype to the environment
   name, universe parameters, number of parameters, type, constructors (name and type), is_meta -/
meta constant add_inductive   : environment → name → list name → nat → expr → list (name × expr) → bool →
                                exceptional environment
/-- Return tt iff the given name is an inductive datatype -/
meta constant is_inductive    : environment → name → bool
/-- Return tt iff the given name is a constructor -/
meta constant is_constructor  : environment → name → bool
/-- Return tt iff the given name is a recursor -/
meta constant is_recursor     : environment → name → bool
/-- Return tt iff the given name is a recursive inductive datatype -/
meta constant is_recursive    : environment → name → bool
/-- Return the name of the inductive datatype of the given constructor. -/
meta constant inductive_type_of : environment → name → option name
/-- Return the constructors of the inductive datatype with the given name -/
meta constant constructors_of : environment → name → list name
/-- Return the recursor of the given inductive datatype -/
meta constant recursor_of     : environment → name → option name
/-- Return the number of parameters of the inductive datatype -/
meta constant inductive_num_params : environment → name → nat
/-- Return the number of indices of the inductive datatype -/
meta constant inductive_num_indices : environment → name → nat
/-- Return tt iff the inductive datatype recursor supports dependent elimination -/
meta constant inductive_dep_elim : environment → name → bool
/-- Return tt iff the given name is a generalized inductive datatype -/
meta constant is_ginductive : environment → name → bool
meta constant is_projection : environment → name → option projection_info
/-- Fold over declarations in the environment -/
meta constant fold {α :Type} : environment → α → (declaration → α → α) → α
/-- `relation_info env n` returns some value if n is marked as a relation in the given environment.
   the tuple contains: total number of arguments of the relation, lhs position and rhs position. -/
meta constant relation_info : environment → name → option (nat × nat × nat)
/-- `refl_for env R` returns the name of the reflexivity theorem for the relation R -/
meta constant refl_for : environment → name → option name
/-- `symm_for env R` returns the name of the symmetry theorem for the relation R -/
meta constant symm_for : environment → name → option name
/-- `trans_for env R` returns the name of the transitivity theorem for the relation R -/
meta constant trans_for : environment → name → option name
/-- `decl_olean env d` returns the name of the .olean file where d was defined.
   The result is none if d was not defined in an imported file. -/
meta constant decl_olean : environment → name → option string
/-- `decl_pos env d` returns the source location of d if available. -/
meta constant decl_pos : environment → name → option pos
/-- Return the fields of the structure with the given name, or `none` if it is not a structure -/
meta constant structure_fields : environment → name → option (list name)
/-- `get_class_attribute_symbols env attr_name` return symbols
   occurring in instances of type classes tagged with the attribute `attr_name`.
   Example: [algebra] -/
meta constant get_class_attribute_symbols : environment → name → name_set
meta constant fingerprint : environment → nat
open expr

meta constant unfold_untrusted_macros : environment → expr → expr
meta constant unfold_all_macros : environment → expr → expr

meta def is_constructor_app (env : environment) (e : expr) : bool :=
is_constant (get_app_fn e) && is_constructor env (const_name (get_app_fn e))

meta def is_refl_app (env : environment) (e : expr) : option (name × expr × expr) :=
match (refl_for env (const_name (get_app_fn e))) with
| (some n) :=
    if get_app_num_args e ≥ 2
    then some (n, app_arg (app_fn e), app_arg e)
    else none
| none   := none
end

/-- Return true if 'n' has been declared in the current file -/
meta def in_current_file (env : environment) (n : name) : bool :=
(env.decl_olean n).is_none && env.contains n

meta def is_definition (env : environment) (n : name) : bool :=
match env.get n with
| exceptional.success (declaration.defn _ _ _ _ _ _) := tt
| _                                                  := ff
end

end environment

meta instance : has_repr environment :=
⟨λ e, "[environment]"⟩

meta instance : inhabited environment :=
⟨environment.mk_std 0⟩
