/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Rewrite

namespace Lean.Meta
namespace Simp

def main (e : Expr) : M σ Result :=
  return (← post e).result -- TODO: traverse term

def simp (e : Expr) (s : σ) (config : Config := {}) (methods : Methods σ := {}) (simpLemmas : SimpLemmas := {}) : MetaM Result := do
  main e methods { config := config, simpLemmas := simpLemmas } |>.run' { user := s }

end Simp

def simp (e : Expr) (simpLemmas : SimpLemmas := {}) : MetaM Simp.Result := do
  let discharge? (e : Expr) : SimpM Unit (Option Expr) := return none -- TODO: use simp, and add config option
  let pre  := (Simp.preDefault · discharge?)
  let post := (Simp.postDefault · discharge?)
  Simp.simp e () (methods := { pre := pre, post := post, discharge? := discharge? }) (simpLemmas := simpLemmas)

end Lean.Meta
