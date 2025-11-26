inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (x : α) (xs : Vec α n) : Vec α (n.succ)

-- set_option trace.Meta.Match.match true

def test : Vec Unit 100000000000 → Nat
  | Vec.cons () _ => 1
