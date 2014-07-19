-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic decidable
using decidable

namespace unit
inductive unit : Type :=
| tt : unit

theorem unit_eq (a b : unit) : a = b
:= unit_rec (unit_rec (refl tt) b) a

theorem inhabited_unit [instance] : inhabited unit
:= inhabited_intro tt

using decidable
theorem decidable_eq [instance] (a b : unit) : decidable (a = b)
:= inl (unit_eq a b)
end