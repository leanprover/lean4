module

/-!
Tests kernel reduction of derived `Vector` equality across a module boundary.
-/

example : (#v[] : Vector Nat 0) = #v[] := by decide
example : decide ((#v[] : Vector Nat 0) = #v[]) = true := by rfl
example : (#v[] : Vector Nat 0) = #v[] := by decide +kernel
