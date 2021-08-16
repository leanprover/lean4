/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.LazyInitExtension
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta
namespace SplitIf

builtin_initialize ext : LazyInitExtension MetaM Simp.Context ←
  registerLazyInitExtension do
    let mut s : SimpLemmas := {}
    s ← s.addConst ``if_pos
    s ← s.addConst ``if_neg
    s ← s.addConst ``dif_pos
    s ← s.addConst ``dif_neg
    return {
      simpLemmas    := s
      congrLemmas   := (← getCongrLemmas)
      config.zeta   := false
      config.beta   := false
      config.eta    := false
      config.iota   := false
      config.proj   := false
      config.decide := false
    }

def getSimpContext : MetaM Simp.Context :=
  ext.get

end SplitIf
end Lean.Meta
