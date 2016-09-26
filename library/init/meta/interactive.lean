/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
namespace interactive

meta def intro (h : name) : tactic unit :=
tactic.intro h >> skip

meta def apply (q : pexpr) : tactic unit :=
to_expr q >>= tactic.apply

meta def refine : pexpr → tactic unit :=
tactic.refine

meta def assumption : tactic unit :=
tactic.assumption

meta def exact (e : pexpr) : tactic unit :=
do tgt : expr ← target,
   to_expr_strict `((%%e : %%tgt)) >>= exact

end interactive
end tactic
