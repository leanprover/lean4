/-!
# Testing features of the app delaborator, including overapplication
-/

/-!
Check that the optional value equality check is specialized to the supplied arguments
(rather than, formerly, the locally-defined fvars from a telescope).
-/
def foo (α : Type) [Inhabited α] (x : α := default) : α := x

#check foo Nat
#check foo Nat 1

/-!
Check that optional value omission is aware of unfolding.
-/
def Ty := (x : Nat := 1) → Fin (x + 1)

def f (y : Nat := 2) : Ty := fun x => 0

#check f 3 4
#check f 3
#check (f)


/-!
Check that overapplied projections pretty print using projection notation.
-/

structure Foo where
  f : Nat → Nat

#check ∀ (x : Foo), x.f 1 = 0

/-!
Overapplied `letFun`
-/
#check (have f := id; f) 1

/-!
Overapplied `OfNat.ofNat`
-/
instance : OfNat (Nat → Nat) 1 where
  ofNat := id

#check (1 : Nat → Nat) 2

/-!
Overapplied `dite`
-/
#check (if h : True then id else id) 1
