#lang lean4
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Recognizers
import Lean.Meta.Basic

namespace Lean.Meta

def matchEq? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
match e.eq? with
| r@(some _) => pure r
| none       => pure (← whnf e).eq?

end Lean.Meta
