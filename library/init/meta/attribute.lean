/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic

meta_constant attribute.get_instances : name → tactic (list name)

structure user_attribute :=
(descr : string)

/- Registers a new user-defined attribute. The argument must be the name of a definition of type
   `user_attribute`. -/
meta_constant attribute.register : name → command
