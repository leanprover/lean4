/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.environment

meta_constant attribute.get_instances : environment → name → list name

/- The structure of a user-defined attribute. To declare a new attribute, define an instance of this
   structure and annotate it with the (built-in) [user_attribute] attribute. -/
structure user_attribute :=
(descr : string)
