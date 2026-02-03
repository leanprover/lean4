/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Basic
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Theorems


namespace Lean.Meta.Tactic.Cbv

open Lean.Meta.Sym.Simp

public structure CbvTheoremsLookupState where
  /-- Cache for function equations (from getEqnsFor?) -/
  eqnTheorems : NameMap Theorems := {}
  /-- Cache for unfold equations (from getUnfoldEqnFor?) -/
  unfoldTheorems : NameMap Theorem := {}
  /-- Cache for match equations (from Match.getEquationsFor) -/
  matchTheorems : NameMap Theorems := {}
  deriving Inhabited

end Lean.Meta.Tactic.Cbv
