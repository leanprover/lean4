/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude

/-!
This module contains infrastructure for proofs by native evaluation (`native decide`, `bv_decide`).
Such proofs involve a native computation using the Lean kernel, and then asserting the result
of that computation as an axiom towards the logic.
-/
