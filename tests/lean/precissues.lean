new_frontend

#check id fun x => x -- should fail

def f (x : Nat) (g : Nat → Nat) := g x

#check f 1 fun x => x -- should fail

#check f 1 (fun x => x)

#check id have True from ⟨⟩; this -- should fail

#check 1

#check id (have True from ⟨⟩; this)

#check 0 = have Nat from 1; this
#check 0 = let x := 0; x

variables (p q r : Prop)
macro_rules `(¬ $p) => `(Not $p)

#check p ↔ ¬ q
#check True = ¬ False
#check p ∧ ¬q
#check ¬p ∧ q
#check ¬p ↔ q
#check ¬(p = q)
#check ¬ p = q
#check id ¬p
#check Nat → ∀ (a : Nat), a = a
