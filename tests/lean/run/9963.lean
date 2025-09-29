def Set (A : Type _) := A → Prop

inductive Thing (s : V → Prop) : Set V
| basic : ∀ x, s x → Thing s x

def foo := @Thing.casesOn
def bar := @Acc.casesOn
