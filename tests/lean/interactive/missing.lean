import logic

inductive tree (A : Type) :=
leaf : A → tree A|
node : tree A → tree A → tree A

namespace tree

definition below_rec {A : Type} (t : tree A) {P : tree A → Type} (iH : Π (t : tree A), P t) : P t :=
have general : ∀ (t : tree A),
  P t, from
  -- take t, iH t,
  sorry,
general t

end tree
