/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Performance test to ensure quadratic blowup is avoided.
-/


class AppendList {α : Type} (xs₁ xs₂ : List α) (out : outParam $ List α) : Type :=
(u : Unit := ())

instance AppendBase {α : Type} (xs₂ : List α) : AppendList [] xs₂ xs₂ :=
{}

instance AppendStep {α : Type} (x : α) (xs₁ xs₂ out : List α) [AppendList xs₁ xs₂ out] : AppendList (x::xs₁) xs₂ (x::out) :=
{}

#synth AppendList
[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
[200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211]
[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211]
