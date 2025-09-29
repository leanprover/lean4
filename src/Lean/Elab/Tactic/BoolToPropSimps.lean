/-
Copyright (c) 2024 University of Cambridge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Grosser
-/

module

prelude
public import Lean.Meta.Tactic.Simp.Attr

public section

builtin_initialize bool_to_prop : Lean.Meta.SimpExtension ←
  Lean.Meta.registerSimpAttr `bool_to_prop
    "simp lemmas converting boolean expressions in terms of `decide` into propositional statements"
