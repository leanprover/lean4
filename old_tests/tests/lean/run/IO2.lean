import system.io
open list io

/- B and unit must be in the same universe
   So, we must put B at Type₁ or use poly_unit
   since unit is at Type₁
-/

definition foreach {A : Type} {B : Type} : list A → (A → io B) → io punit
| []      f := return punit.star
| (x::xs) f := do f x, foreach xs f

#eval foreach [1,2,3,4,5] (λ i, do put_str "value: ", print i, put_str "\n")
