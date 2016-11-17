/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic

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
