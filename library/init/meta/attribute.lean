/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic init.meta.rb_map init.meta.has_reflect init.meta.lean.parser

meta constant attribute.get_instances : name → tactic (list name)
meta constant attribute.fingerprint : name → tactic nat

meta structure user_attribute_cache_cfg (cache_ty : Type) :=
(mk_cache     : list name → tactic cache_ty)
(dependencies : list name)

meta def user_attribute.dflt_cache_cfg : tactic unit :=
tactic.exact `(⟨λ _, pure (), []⟩ : user_attribute_cache_cfg unit)
meta def user_attribute.dflt_parser : tactic unit :=
tactic.exact `(pure () : lean.parser unit)

meta structure user_attribute (cache_ty : Type := unit) (param_ty : Type := unit) :=
(name          : name)
(descr         : string)
/- Optional handler that will be called after the attribute has been applied to a declaration.
   Failing the tactic will fail the entire `attribute/def/...` command, i.e. the attribute will
   not be applied after all.
   Declaring an `after_set` handler without a `before_unset` handler will make the attribute
   non-removable. -/
(after_set    : option (Π (decl : _root_.name) (prio : nat) (persistent : bool), command) := none)
/- Optional handler that will be called before the attribute is removed from a declaration. -/
(before_unset : option (Π (decl : _root_.name) (persistent : bool), command) := none)
(cache_cfg     : user_attribute_cache_cfg cache_ty . user_attribute.dflt_cache_cfg)
[reflect_param : has_reflect param_ty]
/- Parser that will be invoked after parsing the attribute's name. The parse result will be reflected
   and stored and can be retrieved with `user_attribute.get_param`. -/
(parser        : lean.parser param_ty . user_attribute.dflt_parser)

/- Registers a new user-defined attribute. The argument must be the name of a definition of type
   `user_attribute`. -/
meta def attribute.register (decl : name) : command :=
tactic.set_basic_attribute ``user_attribute decl tt

meta constant user_attribute.get_cache {α β : Type} (attr : user_attribute α β) : tactic α

meta def user_attribute.parse_reflect {α β : Type} (attr : user_attribute α β) : lean.parser expr :=
(λ a, attr.reflect_param a) <$> attr.parser

meta constant user_attribute.get_param_untyped {α β : Type} (attr : user_attribute α β) (decl : name)
  : tactic expr
meta constant user_attribute.set_untyped {α β : Type} [reflected β] (attr : user_attribute α β) (decl : name)
  (val : expr) (persistent : bool) (prio : option nat := none) : tactic unit

meta def user_attribute.get_param {α β : Type} [reflected β] (attr : user_attribute α β) (n : name) : tactic β :=
attr.get_param_untyped n >>= tactic.eval_expr β

meta def user_attribute.set {α β : Type} [reflected β] (attr : user_attribute α β) (n : name)
  (val : β) (persistent : bool) (prio : option nat := none) : tactic unit :=
attr.set_untyped n (attr.reflect_param val) persistent prio

open tactic

meta def register_attribute := attribute.register

meta def get_attribute_cache_dyn {α : Type} [reflected α] (attr_decl_name : name) : tactic α :=
let attr : pexpr := expr.const attr_decl_name [] in
do e ← to_expr ``(user_attribute.get_cache %%attr),
   t ← eval_expr (tactic α) e,
   t

meta def mk_name_set_attr (attr_name : name) : command :=
do let t := `(user_attribute name_set),
   let v := `({name     := attr_name,
               descr    := "name_set attribute",
               cache_cfg := {
                 mk_cache := λ ns, return (name_set.of_list ns),
                 dependencies := []}} : user_attribute name_set),
   add_meta_definition attr_name [] t v,
   register_attribute attr_name

meta def get_name_set_for_attr (name : name) : tactic name_set :=
get_attribute_cache_dyn name
