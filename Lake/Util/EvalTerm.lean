/-
Copyright (c) 2022 Mac Malone All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Eval

namespace Lake
open Lean Elab

unsafe def unsafeEvalTerm (α) [ToExpr α] (term : Syntax) : TermElabM α := do
  Term.evalTerm α (toTypeExpr α) term .unsafe

@[implemented_by unsafeEvalTerm]
opaque evalTerm (α) [ToExpr α] (term : Syntax) : TermElabM α

/-! ## ToExpr Instances -/

instance : ToExpr System.FilePath where
  toExpr p := mkApp (mkConst ``System.FilePath.mk) (toExpr p.toString)
  toTypeExpr := mkConst ``System.FilePath
