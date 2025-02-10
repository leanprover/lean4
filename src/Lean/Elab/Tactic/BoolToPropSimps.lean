/-
Copyright (c) 2024 University of Cambridge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Grosser
-/

prelude
import Lean.Meta.Tactic.Simp.Attr

builtin_initialize bool_to_prop : Lean.Meta.SimpExtension ←
  Lean.Meta.registerSimpAttr `bool_to_prop
    "simp lemmas converting boolean expressions in terms of `decide` into propositional statements"

@[deprecated bool_to_prop (since := "2025-02-10")]
builtin_initialize boolToPropSimps : Lean.Meta.SimpExtension ←
  Lean.Meta.registerSimpAttr `boolToPropSimps
    "simp lemmas converting boolean expressions in terms of `decide` into propositional statements"
