/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: logic.examples.instances_test
Author: Jeremy Avigad

Illustrates substitution and congruence with iff.
-/

import ..instances
open relation
open relation.general_subst
open relation.iff_ops
open eq.ops

example (a b : Prop) (H : a ↔ b) (H1 : a) : b := mp H H1

set_option class.conservative false

example (a b c d e : Prop) (H1 : a ↔ b) (H2 : a ∨ c → ¬(d → a)) : b ∨ c → ¬(d → b) :=
subst iff H1 H2

/-
exit
example (a b c d e : Prop) (H1 : a ↔ b) (H2 : a ∨ c → ¬(d → a)) : b ∨ c → ¬(d → b) :=
H1 ▸ H2

example (a b c d e : Prop) (H1 : a ↔ b) : (a ∨ c → ¬(d → a)) ↔ (b ∨ c → ¬(d → b)) :=
is_congruence.congr iff (λa, (a ∨ c → ¬(d → a))) H1

example (T : Type) (a b c d : T) (H1 : a = b) (H2 : c = b) (H3 : c = d) : a = d :=
H1 ⬝ H2⁻¹ ⬝ H3

example (a b c d : Prop) (H1 : a ↔ b) (H2 : c ↔ b) (H3 : c ↔ d) : a ↔ d :=
H1 ⬝ (H2⁻¹ ⬝ H3)

example (T : Type) (a b c d : T) (H1 : a = b) (H2 : c = b) (H3 : c = d) : a = d :=
H1 ⬝ H2⁻¹ ⬝ H3

example (a b c d : Prop) (H1 : a ↔ b) (H2 : c ↔ b) (H3 : c ↔ d) : a ↔ d :=
H1 ⬝ H2⁻¹ ⬝ H3
-/
