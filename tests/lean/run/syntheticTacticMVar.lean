import Std.Data.TreeMap
/-!
# Testing autoparam metavariables having kind `.synthetic`

It used to be that all tactic metavariables were `.syntheticOpaque`, but this caused elaboration issues
for auto-params, since these prevent useful unifications from occurring.
Auto-params now use `.synthetic`, and, like in typeclass synthesis, when such a tactic metavariable
is assigned through unification, we check that the tactic-synthesized value and the inferred values are equal.
-/

/-!
This was failing because the auto-param in `Std.TreeMap.ofArray` was creating a synthetic opaque
metavariable that prevented the expected type from unifying with the resulting type.
(See Ex2 for example not depending on `Std.TreeMap.ofArray`.)
-/
namespace Ex1
inductive Typ where | Int : Typ | Str : Typ
def Schema := Std.TreeMap String Typ
def Example : Schema :=
  Std.TreeMap.ofArray #[
    ("Name", Typ.Str),
    ("Age", Typ.Int)
  ]
def Example' (a : Array (String × Typ)) : Schema :=
  Std.TreeMap.ofArray a
def Example'' : Array (String × Typ) → Schema :=
  fun a => Std.TreeMap.ofArray a
end Ex1

/-!
Self-contained version of Ex1, but with a twist. This time we need `String` to unify with `α`
for the tactic to succeed.
-/
namespace Ex2
class Klass (α : Type) where
  meth : α

open Klass

instance : Klass String where
  meth := "foo"

structure Foo (α : Type) (wit : α := by exact meth) where
def Foo.mk' {α : Type} (wit : α := by exact meth) : Foo α wit := Foo.mk

def bad := (Foo.mk' : Foo String)
def bad' : (α : Type) → [Klass α] → Foo String := fun _ _ => Foo.mk'
end Ex2

/-!
Checking that synth/inferred defeq checking is performed.
-/
namespace Ex3

def foo (n : Nat := by assumption) : Fin (n + 1) := 0

/-! Works -/
set_option linter.unusedVariables false in
example (x y : Nat) : Fin (y + 1) := foo

/-! Fails -/
/--
error: could not synthesize default value for parameter 'n' using tactics
---
error: term synthesized by tactic sequence is not definitionally equal to expression inferred by typing rules, synthesized
  y
inferred
  x
-/
#guard_msgs in
example (x y : Nat) : Fin (x + 1) := foo

end Ex3

/-!
Checking that synth/inferred defeq checking is done for syntheticOpaque as well.

https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Cannot.20prove.20index.20is.20valid/near/498465790
-/
namespace Ex4

axiom get {A : Type} (as : List A) (i : Nat) (_ : i < as.length) : A
axiom A : Type
axiom B : A → Type
axiom as : List A
axiom fn : (l : Nat) → (h : l < as.length) → Option (B (get as l h))

-- Used to say "no goals to be solved" on `assumption`
example {l : Nat} {llen : l < as.length} {b : B (get as l (by assumption))}
    (b_mem : b ∈ fn l llen) : True := sorry

end Ex4
