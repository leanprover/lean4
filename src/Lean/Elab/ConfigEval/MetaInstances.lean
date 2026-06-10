/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Elab.ConfigEval.Commands
public import Lean.Elab.ConfigEval.Instances
import Lean.Elab.ConfigEval.DeriveEvalTerm
import Lean.Elab.ConfigEval.DeriveEvalExpr

/-!
# Derived evaluator instances for built-in Meta types

-/

public section

namespace Lean.Elab.ConfigEval

open Meta Term

ensure_eval_term_expr_instances ApplyNewGoals
ensure_eval_term_expr_instances EtaStructMode
ensure_eval_term_expr_instances TransparencyMode
ensure_eval_term_expr_instances Occurrences

end Lean.Elab.ConfigEval
