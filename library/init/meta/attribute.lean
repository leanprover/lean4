/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic init.meta.rb_map init.meta.has_reflect

meta constant attribute.get_instances : name → tactic (list name)
meta constant attribute.fingerprint : name → tactic nat

meta structure user_attribute :=
(name         : name)
(descr        : string)
/- Optional handler that will be called after the attribute has been applied to a declaration.
   Failing the tactic will fail the entire `attribute/def/...` command, i.e. the attribute will
   not be applied after all.
   Declaring an `after_set` handler without a `before_unset` handler will make the attribute
   non-removable. -/
(after_set    : option (Π (decl : _root_.name) (prio : nat) (persistent : bool), command) := none)
/- Optional handler that will be called before the attribute is removed from a declaration. -/
(before_unset : option (Π (decl : _root_.name) (persistent : bool), command) := none)

/- Registers a new user-defined attribute. The argument must be the name of a definition of type
   `user_attribute` or a sub-structure. -/
meta def attribute.register (decl : name) : command :=
tactic.set_basic_attribute ``user_attribute decl tt

meta structure caching_user_attribute (α : Type) extends user_attribute :=
(mk_cache     : list _root_.name → tactic α)
(dependencies : list _root_.name)

meta constant caching_user_attribute.get_cache : Π {α : Type}, caching_user_attribute α → tactic α

open tactic

meta def register_attribute := attribute.register

meta def mk_name_set_attr (attr_name : name) : command :=
do let t := `(caching_user_attribute name_set),
   let v := `({name     := attr_name,
                 descr    := "name_set attribute",
                 mk_cache := λ ns, return (name_set.of_list ns),
                 dependencies := [] } : caching_user_attribute name_set),
   add_meta_definition attr_name [] t v,
   register_attribute attr_name

meta def get_name_set_for_attr (attr_name : name) : tactic name_set :=
do
  cnst   ← return (expr.const attr_name []),
  attr   ← eval_expr (caching_user_attribute name_set) cnst,
  caching_user_attribute.get_cache attr
