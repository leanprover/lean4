set_option cbv.warning false

/-! Tests for `cbv` handling of dependent projections.

When a struct is rewritten (e.g. via `@[cbv_eval]`) but the projection is
dependent and the original struct can't be reduced, `cbv` should gracefully
get stuck rather than crash.
-/

-- Sigma: .1 is non-dependent, .2 is dependent
def myPair : Σ n : Nat, Fin (n + 1) := ⟨5, ⟨3, by omega⟩⟩
axiom otherPair : Σ n : Nat, Fin (n + 1)
@[cbv_eval ←] axiom otherPair_eq : myPair = otherPair

example : otherPair.1 = 5 := by cbv

/--
error: unsolved goals
⊢ otherPair.2.1 = 3
-/
#guard_msgs in
example : otherPair.2.val = 3 := by cbv

-- Custom structure with a dependent field
structure DepPkg where
  n : Nat
  val : Fin (n + 1)

def concretePkg : DepPkg := ⟨5, ⟨3, by omega⟩⟩
axiom opaquePkg : DepPkg
@[cbv_eval ←] axiom opaquePkg_eq : concretePkg = opaquePkg

example : opaquePkg.n = 5 := by cbv

/--
error: unsolved goals
⊢ opaquePkg.2.1 = 3
-/
#guard_msgs in
example : opaquePkg.val.val = 3 := by cbv

-- Subtype: .val is non-dependent, so the rewrite goes through
def concreteSubtype : { n : Nat // n > 0 } := ⟨5, by omega⟩
axiom opaqueSubtype : { n : Nat // n > 0 }
@[cbv_eval ←] axiom opaqueSubtype_eq : concreteSubtype = opaqueSubtype

example : opaqueSubtype.val = 5 := by cbv

-- Non-dependent projections: function projected from a structure and applied
structure FnStruct where
  fn : Nat → Nat

def myFnStruct : FnStruct := ⟨fun n => n + 1⟩
example : myFnStruct.fn 5 = 6 := by cbv

-- Nested non-dependent projections
structure Layer1 where val : Nat
structure Layer2 where inner : Layer1
structure Layer3 where inner : Layer2

def nested : Layer3 := ⟨⟨⟨42⟩⟩⟩
example : nested.inner.inner.val = 42 := by cbv

-- Double projection through a product
structure FnPairS where
  fst : Nat → Nat
  snd : Nat → Nat

def fnPairPair : FnPairS × FnPairS :=
  (⟨fun n => n + 1, fun n => n + 2⟩, ⟨fun n => n + 3, fun n => n + 4⟩)

example : fnPairPair.1.fst 5 = 6 := by cbv
example : fnPairPair.2.snd 5 = 9 := by cbv
