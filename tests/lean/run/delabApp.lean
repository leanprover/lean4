/-!
# Testing features of the app delaborator, including overapplication
-/

/-!
Check that the optional value equality check is specialized to the supplied arguments
(rather than, formerly, the locally-defined fvars from a telescope).
-/
def foo (α : Type) [Inhabited α] (x : α := default) : α := x

/-- info: foo Nat : Nat -/
#guard_msgs in #check foo Nat
/-- info: foo Nat 1 : Nat -/
#guard_msgs in #check foo Nat 1

/-!
Check that optional value omission is aware of unfolding.
-/
def Ty := (x : Nat := 1) → Fin (x + 1)

def f (y : Nat := 2) : Ty := fun x => 0

/-- info: f 3 4 : Fin (4 + 1) -/
#guard_msgs in #check f 3 4
/-- info: f 3 : Fin (1 + 1) -/
#guard_msgs in #check f 3
/-- info: f : Fin (1 + 1) -/
#guard_msgs in #check (f)


/-!
Check that overapplied projections pretty print using projection notation.
-/

structure Foo where
  f : Nat → Nat

/-- info: ∀ (x : Foo), x.f 1 = 0 : Prop -/
#guard_msgs in #check ∀ (x : Foo), x.f 1 = 0

/-!
Overapplied `letFun`
-/
/--
info: (let_fun f := id;
  f)
  1 : Nat
-/
#guard_msgs in #check (have f := id; f) 1

/-!
Overapplied `OfNat.ofNat`
-/
instance : OfNat (Nat → Nat) 1 where
  ofNat := id

/-- info: 1 2 : Nat -/
#guard_msgs in #check (1 : Nat → Nat) 2

/-!
Overapplied `dite`
-/

/-- info: (if _h : True then id else id) 1 : Nat -/
#guard_msgs in #check (if _h : True then id else id) 1


/-!
Testing that multiple optional arguments are omitted rather than just the last (issue #4812)
-/

def g (a : Nat) (b := 1) (c := 2) (d := 3) := a + b + c + d

/-- info: g 0 : Nat -/
#guard_msgs in #check g 0
