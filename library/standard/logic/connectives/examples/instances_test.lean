--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad

import ..instances

using relation


section

using relation.operations

theorem test1 (a b : Prop) (H : a ↔ b) (H1 : a) : b := mp H H1

end


section

using gensubst

theorem test2 (a b c d e : Prop) (H1 : a ↔ b) (H2 : a ∨ c → ¬(d → a)) : b ∨ c → ¬(d → b) :=
subst H1 H2

theorem test3 (a b c d e : Prop) (H1 : a ↔ b) (H2 : a ∨ c → ¬(d → a)) : b ∨ c → ¬(d → b) :=
H1 ▸ H2

end


theorem test4 (a b c d e : Prop) (H1 : a ↔ b) : (a ∨ c → ¬(d → a)) ↔ (b ∨ c → ¬(d → b)) :=
congr.infer iff iff (λa, (a ∨ c → ¬(d → a))) H1


section

using relation.symbols

theorem test5 (T : Type) (a b c d : T) (H1 : a = b) (H2 : c = b) (H3 : c = d) : a = d :=
H1 ⬝ H2⁻¹ ⬝ H3

theorem test6 (a b c d : Prop) (H1 : a ↔ b) (H2 : c ↔ b) (H3 : c ↔ d) : a ↔ d :=
H1 ⬝ (H2⁻¹ ⬝ H3)

end
