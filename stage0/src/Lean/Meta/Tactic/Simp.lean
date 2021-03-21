/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.SimpLemmas
import Lean.Meta.Tactic.Simp.CongrLemmas
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Tactic.Simp.SimpAll

namespace Lean

builtin_initialize registerTraceClass `Meta.Tactic.simp
builtin_initialize registerTraceClass `Debug.Meta.Tactic.simp

end Lean
