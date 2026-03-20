

namespace scratch

inductive type
| bv (w:Nat) : type

open type

def value : type -> Type
  | bv w   => {n // n < w}

def tester_fails : ∀ {tp : type}, value tp -> Bool
  | bv _,   v1 => decide (v1.val = 0)

def tester_ok : ∀ {tp : type}, value tp -> Prop
  | bv _,   v1 => v1.val = 0

end scratch
