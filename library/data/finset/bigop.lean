/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.finset
Author: Leonardo de Moura

Finite sets big operators
-/
import algebra.group data.finset.basic
open algebra finset function binary quot

namespace finset
variables {A B : Type}
variable  [g : comm_group B]
include g

protected definition mulf (f : A → B) : B → A → B :=
λ b a, b * f a

protected theorem mulf_rcomm (f : A → B) : right_commutative (mulf f) :=
right_commutative_compose_right (@has_mul.mul B g) f (@mul.right_comm B g)

definition bigop (s : finset A) (f : A → B) : B :=
acc (mulf f) (mulf_rcomm f) 1 s
end finset
