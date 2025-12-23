/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Tactic.Grind.Main
namespace Lean.Meta.Sym
open Grind (Params)

def SymM.run (x : SymM α) (params : Params) : MetaM α := do
  x.run' {} |>.run params

def SymM.run' (x : SymM α) (config : Grind.Config := {}) : MetaM α := do
  let params ← Grind.mkDefaultParams config
  x.run params

end Lean.Meta.Sym
