/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic init.meta.rb_map init.meta.quote

meta constant attribute.get_instances : name → tactic (list name)
meta constant attribute.fingerprint : name → tactic nat

structure user_attribute :=
(name  : name)
(descr : string)

/- Registers a new user-defined attribute. The argument must be the name of a definition of type
   `user_attribute` or a sub-structure. -/
meta constant attribute.register : name → command

meta structure caching_user_attribute (α : Type) extends user_attribute :=
(mk_cache     : list _root_.name → tactic α)
(dependencies : list _root_.name)

meta constant caching_user_attribute.get_cache : Π {α : Type}, caching_user_attribute α → tactic α

open tactic

meta def mk_name_set_attr (attr_name : name) : command :=
do t ← to_expr ``(caching_user_attribute name_set),
   v ← to_expr ``({name     := %%(quote attr_name),
                   descr    := "name_set attribute",
                   mk_cache := λ ns, return $ name_set.of_list ns,
                   dependencies := [] } : caching_user_attribute name_set),
   add_decl (declaration.defn attr_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_name

meta def get_name_set_for_attr (attr_name : name) : tactic name_set :=
do
  cnst   ← return (expr.const attr_name []),
  attr   ← eval_expr (caching_user_attribute name_set) cnst,
  caching_user_attribute.get_cache attr
