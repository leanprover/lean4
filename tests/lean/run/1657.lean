namespace X1

inductive wrap (A : Type) : Type
| mk : A → wrap

inductive type : Type
| mk : list type → type
| refinement : type → (bool → type) → type

end X1

namespace X2

inductive type : Type
| mk : (bool → type) → list type → ℕ → type
| refinement : list type → type → ℕ → (∀ (b : bool), b = tt → type) → (bool → type) → type

end X2

namespace X3

mutual inductive type, term
with type : Type
| fn : list type → type
| refinement : type → (string → type) → type
with term : Type
| apply : term

end X3
