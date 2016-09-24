/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
/- (flat_assoc op assoc e) -/
meta constant flat_assoc : expr → expr → expr → tactic (expr × expr)
/- (perm_ac op assoc comm e1 e2) Try to construct a proof that e1 = e2 modulo AC -/
meta constant perm_ac : expr → expr → expr → expr → expr → tactic expr
end tactic
