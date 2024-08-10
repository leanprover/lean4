import Lean
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

-- Both the `start` and `stop` arguments are omitted.
/-- info: fun a => Array.foldl (fun x y => x + y) 0 a : Array Nat → Nat -/
#guard_msgs in #check fun (a : Array Nat) => a.foldl (fun x y => x + y) 0


/-!
Testing overriding the app delaborator with an `@[app_delab]`
-/

def myFun (x : Nat) : Nat := x

/-- info: myFun 2 : Nat -/
#guard_msgs in #check myFun 2

open Lean PrettyPrinter Delaborator in
@[app_delab myFun] def delabMyFun : Delab := withOverApp 0 `(id)

/-- info: id✝ 2 : Nat -/
#guard_msgs in #check myFun 2

/-!
Testing `@[app_delab]` error conditions.
-/

/-- error: unknown declaration 'noSuchFunction' -/
#guard_msgs in
open Lean PrettyPrinter Delaborator in
@[app_delab noSuchFunction] def delabErr1 : Delab := withOverApp 0 `(id)

def A.f := 0
def B.f := 0
open A B
/-- error: ambiguous declaration 'f' -/
#guard_msgs in
open Lean PrettyPrinter Delaborator in
@[app_delab f] def delabErr2 : Delab := withOverApp 0 `(id)
