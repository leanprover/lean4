inductive T : Bool → Type
| mkTrue  : T true
| mkFalse : T false

def test2 : (b : Bool) → T b → (bif b then Nat else List Nat) → Nat
  | .(true), T.mkTrue, Nat.zero  => 1
  | _, _, _ => 0
