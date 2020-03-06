/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Lean.KeyedDeclsAttribute

namespace Lean
namespace Delaborator

abbrev Delab := Unit  -- TODO

unsafe def mkDelabAttribute : IO (KeyedDeclsAttribute Macro) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinDelab,
  name := `delab,
  descr := "delaborator",
  valueTypeName := `Lean.Delaborator.Delab
} `Lean.Delaborator.delabAttribute
@[init mkDelabAttribute] constant delabAttribute : KeyedDeclsAttribute Macro := arbitrary _

end Delaborator
end Lean
