import Lean

/-!
  #2564. `match` reduction currently has some special cases.
  When combined with nonlinear functions like `List.insert` below,
  it is crucial to preserve sharing during reduction. -/

section decidability_instances

variable {α : Type} {p : α → Prop} [DecidablePred p]

instance decidableBex : ∀ (l : List α), Decidable (∃ x, x ∈ l → p x)
  | []    => isFalse sorry
  | x::xs =>
    match ‹DecidablePred p› x with
    | isTrue h₁ => isTrue sorry
    | isFalse h₁ => match decidableBex xs with
      | isTrue h₂  => isTrue sorry
      | isFalse h₂ => isFalse sorry

instance decidableBall (l : List α) : Decidable (∀ x, x ∈ l → p x) :=
  match (inferInstance : Decidable <| ∃ x, x ∈ l → ¬ p x) with
  | isFalse h => isTrue $ fun x hx => match ‹DecidablePred p› x with
    | isTrue h' => h'
    | isFalse h' => False.elim $ h sorry
  | isTrue h => isFalse sorry

end decidability_instances

@[inline] protected def List.insert {α : Type} [DecidableEq α] (a : α) (l : List α) : List α :=
  if a ∈ l then l else a :: l

def parts : List (List Nat) := List.insert ([1, 1, 0, 0]) <| List.insert ([0, 0, 1, 1]) <|
  List.insert ([1, 0, 0, 1]) <| List.insert ([1, 1, 1, 0]) <| List.insert ([1, 0, 0, 0]) <|
  List.insert [1, 2, 3, 4] <| List.insert [5, 6, 7, 8] []

#eval show Lean.Elab.Command.CommandElabM _ from
  for _ in [0:10] do
    Lean.Elab.Command.elabCommand (←
      `(example : ∀ (x) (_ : x ∈ parts) (y) (_ : y ∈ parts), x ++ y ∉ parts := by decide))
