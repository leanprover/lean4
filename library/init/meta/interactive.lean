/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
namespace interactive

meta definition apply (q : pexpr) : tactic unit :=
to_expr q >>= tactic.apply

meta definition refine : pexpr → tactic unit :=
tactic.refine

end interactive
end tactic
