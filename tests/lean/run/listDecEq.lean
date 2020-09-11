-- List decidable equality using `withPtrEqDecEq`
def listDecEqAux {α} [s : DecidableEq α] : ∀ (as bs : List α), Decidable (as = bs)
| [],    []    => isTrue rfl
| [],    b::bs => isFalse $ fun h => List.noConfusion h
| a::as, []    => isFalse $ fun h => List.noConfusion h
| a::as, b::bs =>
  match s a b with
  | isTrue h₁  =>
    match withPtrEqDecEq as bs (fun _ => listDecEqAux as bs) with
    | isTrue h₂  => isTrue $ h₁ ▸ h₂ ▸ rfl
    | isFalse h₂ => isFalse $ fun h => List.noConfusion h $ fun _ h₃ => absurd h₃ h₂
  | isFalse h₁ => isFalse $ fun h => List.noConfusion h $ fun h₂ _ => absurd h₂ h₁

instance List.optimizedDecEq {α} [DecidableEq α] : DecidableEq (List α) :=
fun a b => withPtrEqDecEq a b (fun _ => listDecEqAux a b)
