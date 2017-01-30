constant p {α : Type} [has_zero α] : α → Prop
constant pax {α : Type} [has_zero α] : p (0:α)

lemma ex : p (0:nat) :=
@pax int _
