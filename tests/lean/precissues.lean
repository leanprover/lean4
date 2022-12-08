

#check id fun x => x -- should work

#check 0

def f (x : Nat) (g : Nat → Nat) := g x

#check f 1 fun x => x -- should fail

#check 0

#check f 1 (fun x => x)

#check id have : True := ⟨⟩; this -- should fail

#check id let x := 10; x

#check 1

#check id (have : True := ⟨⟩; this)

#check 0 = have : Nat := 1; this
#check 0 = let x := 0; x

variable (p q r : Prop)
macro_rules | `(¬ $p) => `(Not $p)

#check p ↔ ¬ q
#check True = ¬ False
#check p ∧ ¬q
#check ¬p ∧ q
#check ¬p ↔ q
#check ¬(p = q)
#check ¬ p = q
#check id ¬p
#check Nat → ∀ (a : Nat), a = a

macro "foo!" x:term : term => `($x + 1)

#check id foo! 10 -- error, `foo! x` precedence is leadPrec
