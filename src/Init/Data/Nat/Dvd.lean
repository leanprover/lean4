prelude
import Init.NotationExtra

/--
Divisibility of natural numbers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Nat := ⟨fun a b => ∃ c, b = a * c⟩
