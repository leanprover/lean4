-- Create a new HAdd so that the unexpander for `+` doesn't take over for the `(+) 2 3` example.
class HAdd' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAdd : α → β → γ

instance [HAdd α β γ] : HAdd' α β γ where
  hAdd := HAdd.hAdd

notation "(+)" => HAdd'.hAdd
#check ((+) : Nat -> Nat -> Nat)
#check ((+) 2 : Nat -> Nat)
#check ((+) 2 3 : Nat)
