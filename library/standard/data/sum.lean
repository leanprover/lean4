-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

namespace sum
inductive sum (A : Type) (B : Type) : Type :=
| inl : A → sum A B
| inr : B → sum A B

infixr `+`:25 := sum

theorem induction_on {A : Type} {B : Type} {C : Prop} (s : A + B) (H1 : A → C) (H2 : B → C) : C :=
sum_rec H1 H2 s
end