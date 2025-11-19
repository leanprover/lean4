def listL (a : List α) := if a = [] then 1 else 2
def listR (a : List α) := if [] = a then 1 else 2

/-- info: 1 -/
#guard_msgs in #eval @listL Nat []
/-- info: 2 -/
#guard_msgs in #eval listL [""]
/-- info: 1 -/
#guard_msgs in #eval @listL Nat []
/-- info: 2 -/
#guard_msgs in #eval listL [()]

section
variable {α : Type u} [DecidableEq α]

-- test for instance diamonds

example (x : List α) :
    instDecidableEqList x [] = instDecidableEqNil x := by
  with_reducible_and_instances rfl

example (x : List α) :
    instDecidableEqList [] x = instDecidableNilEq x := by
  with_reducible_and_instances rfl
end

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
