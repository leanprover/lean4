mutual

inductive ConE : Type where
| nilE : ConE
| extE : ConE → TyE → ConE

inductive TyE : Type where
| UE : ConE → TyE

end

def length (ΓE : ConE) : Nat :=
  match ΓE with
  | ConE.nilE => 0
  | ConE.extE ΓE AE => (length ΓE) + 1
