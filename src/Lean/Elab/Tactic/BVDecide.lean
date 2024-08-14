/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Bitblast

/-!
This directory implements the `bv_decide` tactic as a verified bitblaster with subterm sharing.
It makes use of proof by reflection and `ofReduceBool`, thus adding the Lean compiler to the trusted
code base.
-/
