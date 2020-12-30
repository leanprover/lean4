/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

def main (e : Expr) : M σ Result :=
  return { expr := e }

def simp (e : Expr) (s : σ) (config : Config := {}) (methods : Methods σ := {}) (simpLemmas : SimpLemmas := {}) : MetaM Result :=
  main e methods { config := config, simpLemmas := simpLemmas } |>.run' { user := s }

end Lean.Meta.Simp
