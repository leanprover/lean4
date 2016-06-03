/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
inductive cmp_result :=
| lt | eq | gt

open cmp_result

definition cmp_result.has_to_string [instance] : has_to_string cmp_result :=
has_to_string.mk (λ s, match s with | lt := "lt" | eq := "eq" | gt := "gt" end)

definition nat.cmp (a b : nat) : cmp_result :=
if a < b      then lt
else if a = b then eq
else               gt
