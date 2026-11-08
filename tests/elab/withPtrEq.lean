import Std.Data.HashMap
import Lean.Expr

/-!
Tests the compiler's check of the types at which the safe `withPtrEq` is used: it must accept types
whose values cannot contain types or type formers (which are erased at runtime), and reject all
other types, including polymorphic uses. Also tests that accepted uses short-circuit on
pointer-equal arguments. The unsoundness that the check rules out was the reason for #15252.
-/

/-! ## Runtime behavior -/

structure Point where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

def p : Point := ⟨1, 2⟩
@[noinline] def mkPoint (x : Nat) : Point := ⟨x, x + 1⟩

def eqPoint (a b : Point) : Bool :=
  withPtrEq a b (fun _ => dbgTrace "called k" fun _ => decide (a = b)) decide_eq_true

/-- info: true -/
#guard_msgs in
#eval eqPoint p p

/--
info: called k
---
info: true
-/
#guard_msgs in
#eval eqPoint p (mkPoint 1)

/--
info: called k
---
info: false
-/
#guard_msgs in
#eval eqPoint p (mkPoint 2)

/-- `withPtrEq` can be passed to `withPtrEqDecEq` at a concrete type. -/
def decEqPoint (a b : Point) : Decidable (a = b) :=
  withPtrEqDecEq withPtrEq (fun _ _ _ _ => rfl) a b fun _ =>
    dbgTrace "called k" fun _ => inferInstance

/-- info: true -/
#guard_msgs in
#eval (decEqPoint p p).decide

/--
info: called k
---
info: false
-/
#guard_msgs in
#eval (decEqPoint p (mkPoint 2)).decide

/-- The logical value of `withPtrEq` is `k ()`. -/
example (a b : Point) (k : Unit → Bool) (h : a = b → k () = true) : withPtrEq a b k h = k () := rfl

/-! ## Accepted types -/

section Accepted

variable (k : Unit → Bool) (hk : k () = true)

def atNat (a b : Nat) : Bool := withPtrEq a b k fun _ => hk
def atString (a b : String) : Bool := withPtrEq a b k fun _ => hk
def atFloat (a b : Float) : Bool := withPtrEq a b k fun _ => hk
def atArray (a b : Array (List (Option (Nat × Int)))) : Bool := withPtrEq a b k fun _ => hk
def atThunk (a b : Thunk String) : Bool := withPtrEq a b k fun _ => hk
def atTask (a b : Task Char) : Bool := withPtrEq a b k fun _ => hk
def atFun (a b : Nat → String → Point) : Bool := withPtrEq a b k fun _ => hk
def atFunOfType (a b : Type → Nat) : Bool := withPtrEq a b k fun _ => hk
def atSubtype (a b : { n : Nat // n % 2 = 0 }) : Bool := withPtrEq a b k fun _ => hk
def atQuot (a b : Quot (fun (x y : Nat) => x % 2 = y % 2)) : Bool := withPtrEq a b k fun _ => hk
def atULift.{u} (a b : ULift.{u} Nat) : Bool := withPtrEq a b k fun _ => hk
def atDecidable (q : Prop) (a b : Decidable q) : Bool := withPtrEq a b k fun _ => hk

/-- Dependencies on variables that are not types are fine. -/
def atFin (n : Nat) (a b : Fin n) : Bool := withPtrEq a b k fun _ => hk
def atBitVec (w : Nat) (a b : BitVec w) : Bool := withPtrEq a b k fun _ => hk

/-- Type variables that do not occur in data positions are fine. -/
structure Tagged (β : Type) where
  val : Nat

def atTagged (β : Type) (a b : Tagged β) : Bool := withPtrEq a b k fun _ => hk

/-- Fields whose type is a type variable of `Prop` are proofs. -/
def atPSigma (q : Prop) (a b : PSigma fun (_ : q) => Nat) : Bool := withPtrEq a b k fun _ => hk

/-- Type definitions are unfolded. -/
def Tup : Nat → Type
  | 0 => Unit
  | n + 1 => Nat × Tup n

def atTup (a b : Tup 3) : Bool := withPtrEq a b k fun _ => hk

/-- Nested, mutual and indexed inductive types. -/
inductive Tree where
  | node (val : Nat) (children : List Tree)

mutual
inductive Even where
  | zero
  | succ (n : Odd)
inductive Odd where
  | succ (n : Even)
end

inductive Vec : Nat → Type where
  | nil : Vec 0
  | cons {n : Nat} (x : String) (xs : Vec n) : Vec (n + 1)

def atTree (a b : Tree) : Bool := withPtrEq a b k fun _ => hk
def atEven (a b : Even) : Bool := withPtrEq a b k fun _ => hk
def atVec (n : Nat) (a b : Vec n) : Bool := withPtrEq a b k fun _ => hk

/-- Partial applications are fine. -/
def partialApp : (a b : Point) → (k : Unit → Bool) → (a = b → k () = true) → Bool :=
  withPtrEq

end Accepted

/-! ## Rejected types -/

/-! The use from #15252, which would allow proving `False` using `native_decide`: -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Prop
because values of this type are erased at runtime.

Note: `withPtrEq` is implemented by a pointer equality check, which is only correct if pointer-equal values are equal. This is not the case for values that contain types or type formers, since these are erased at runtime. Therefore, `withPtrEq` can only be used at types for which the compiler can check that their values do not contain types or type formers; in particular, it cannot be used polymorphically.

Hint: In `unsafe` code, `withPtrEqUnsafe` can be used instead.
-/
#guard_msgs in
def atProp : Bool := withPtrEq True False (fun _ => false) (by simp)

theorem atProp_eq_false : atProp = false := rfl

/--
error: Tactic `native_decide` failed. Error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'atProp', which is 'noncomputable'
-/
#guard_msgs in
theorem bad : False := by
  suffices atProp = true by simp_all [atProp_eq_false]
  native_decide

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Prop
because values of this type are erased at runtime.
-/
#guard_msgs (substring := true) in
#eval withPtrEq True False (fun _ => false) (by simp)

/-!
`Erased.mk n` and `Erased.mk m` are represented by the same object at runtime, so a pointer
equality check would wrongly short-circuit the equality check on `n` and `m`.
-/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Erased Nat
because it contains values of type
  Nat → Prop
which are erased at runtime (in field `val` of constructor `Subtype.mk`).
-/
#guard_msgs (substring := true) in
def eqErased (n m : Nat) : Bool :=
  withPtrEq (Erased.mk n) (Erased.mk m) (fun _ => n == m)
    (fun h => beq_iff_eq.mpr (Erased.mk_inj.mp h))

example : eqErased 1 2 = false := rfl

/-- info: true -/
#guard_msgs in
#eval unsafe withPtrEqUnsafe (Erased.mk 1) (Erased.mk 2) (fun _ => 1 == 2)
  (fun h => beq_iff_eq.mpr (Erased.mk_inj.mp h))

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Type
because values of this type are erased at runtime.
-/
#guard_msgs (substring := true) in
def atType : Bool := withPtrEq Nat Int (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Nat → Prop
because values of this type are erased at runtime.
-/
#guard_msgs (substring := true) in
def atTypeFormer (a b : Nat → Prop) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

structure Packed where
  ty : Type
  val : Nat

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Packed
because it contains values of type
  Type
which are erased at runtime (in field `ty` of constructor `Packed.mk`).
-/
#guard_msgs (substring := true) in
def atPacked (a b : Packed) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  (α : Type) × α
because it contains values of type
  Type
which are erased at runtime (in field `fst` of constructor `Sigma.mk`).
-/
#guard_msgs (substring := true) in
def atSigma (a b : (α : Type) × α) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  List Prop
because it contains values of type
  Prop
which are erased at runtime (in field `head` of constructor `List.cons`).
-/
#guard_msgs (substring := true) in
def atListProp (a b : List Prop) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

structure Pred where
  p : Nat → Prop

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Option Pred
because it contains values of type
  Nat → Prop
which are erased at runtime (in field `p` of constructor `Pred.mk`).
-/
#guard_msgs (substring := true) in
def atPred (a b : Option Pred) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Nat → Packed
because it contains values of type
  Type
which are erased at runtime (in field `ty` of constructor `Packed.mk`).
-/
#guard_msgs (substring := true) in
def atFunToType (a b : Nat → Packed) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/-! Polymorphic uses are rejected. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  α
because values of this type cannot be checked since `α` is a type variable.
-/
#guard_msgs (substring := true) in
def atTypeVar {α : Type} (a b : α) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  List α
because it contains values of type
  α
which cannot be checked since `α` is a type variable (in field `head` of constructor `List.cons`).
-/
#guard_msgs (substring := true) in
def atListTypeVar {α : Type} (a b : List α) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  (β : Type) → β → β
because it contains values of type
  β
which cannot be checked since `β` is a type variable.
-/
#guard_msgs (substring := true) in
def atPolyFun (a b : (β : Type) → β → β) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  α
because values of this type cannot be checked since `α` is a type variable.
-/
#guard_msgs (substring := true) in
def polyDecEq {α : Type} [DecidableEq α] (a b : α) : Decidable (a = b) :=
  withPtrEqDecEq withPtrEq (fun _ _ _ _ => rfl) a b fun _ => inferInstance

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
-/
#guard_msgs (substring := true) in
def unapplied : {α : Type} → (a b : α) → (k : Unit → Bool) → (a = b → k () = true) → Bool :=
  withPtrEq

/-! Types that do not reduce to an inductive type, a function type or a quotient are rejected. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Tup n
because values of this type cannot be checked since the type does not reduce to an inductive type, a function type or a quotient.
-/
#guard_msgs (substring := true) in
def atTupVar (n : Nat) (a b : Tup n) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  IO.Ref Nat
because it contains values of type
  ST.RefPointed.type
which cannot be checked since the type does not reduce to an inductive type, a function type or a quotient (in field `ref` of constructor `ST.Ref.mk`).
-/
#guard_msgs (substring := true) in
def atRef (a b : IO.Ref Nat) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/-! ## Opaque types

Values of opaque types are not erased, but opaque types must still be rejected: the logic may know
that an opaque type is a type whose values are erased, from the type of an opaque constant or from
an axiom. Then two provably different values can be the same object at runtime. In each example
below, `withPtrEqUnsafe` shows what `withPtrEq` would return if the type were accepted.
-/

/-! The type of an opaque constant determines its projection, without any axioms. -/

opaque OpaqueProp : {α : Type // α = Prop} := ⟨Prop, rfl⟩

def projTrue : OpaqueProp.val := cast OpaqueProp.property.symm True
def projFalse : OpaqueProp.val := cast OpaqueProp.property.symm False

theorem projTrue_ne_projFalse : projTrue ≠ projFalse := by
  intro h
  have h' := congrArg (cast OpaqueProp.property) h
  simp [projTrue, projFalse] at h'

/-- info: true -/
#guard_msgs in
#eval unsafe withPtrEqUnsafe projTrue projFalse (fun _ => false)
  (fun h => absurd h projTrue_ne_projFalse)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  OpaqueProp.val
because values of this type cannot be checked since the type does not reduce to an inductive type, a function type or a quotient.
-/
#guard_msgs (substring := true) in
def atOpaqueProj : Bool :=
  withPtrEq projTrue projFalse (fun _ => false) (fun h => absurd h projTrue_ne_projFalse)

/-! A consistent axiom determines a plain opaque type. -/

opaque OpaqueType : Type
axiom opaqueType_eq : OpaqueType = Prop

def typeTrue : OpaqueType := cast opaqueType_eq.symm True
def typeFalse : OpaqueType := cast opaqueType_eq.symm False

theorem typeTrue_ne_typeFalse : typeTrue ≠ typeFalse := by
  intro h
  have h' := congrArg (cast opaqueType_eq) h
  simp [typeTrue, typeFalse] at h'

/-- info: true -/
#guard_msgs in
#eval unsafe withPtrEqUnsafe typeTrue typeFalse (fun _ => false)
  (fun h => absurd h typeTrue_ne_typeFalse)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  OpaqueType
because values of this type cannot be checked since the type does not reduce to an inductive type, a function type or a quotient.
-/
#guard_msgs (substring := true) in
def atOpaqueType : Bool :=
  withPtrEq typeTrue typeFalse (fun _ => false) (fun h => absurd h typeTrue_ne_typeFalse)

/-! The same applies to the `NonemptyType` pattern used for runtime objects such as `IO.Ref`. -/

opaque OpaqueNonempty : NonemptyType
axiom opaqueNonempty_eq : OpaqueNonempty.type = Prop

def nonemptyTrue : OpaqueNonempty.type := cast opaqueNonempty_eq.symm True
def nonemptyFalse : OpaqueNonempty.type := cast opaqueNonempty_eq.symm False

theorem nonemptyTrue_ne_nonemptyFalse : nonemptyTrue ≠ nonemptyFalse := by
  intro h
  have h' := congrArg (cast opaqueNonempty_eq) h
  simp [nonemptyTrue, nonemptyFalse] at h'

/-- info: true -/
#guard_msgs in
#eval unsafe withPtrEqUnsafe nonemptyTrue nonemptyFalse (fun _ => false)
  (fun h => absurd h nonemptyTrue_ne_nonemptyFalse)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  OpaqueNonempty.type
because values of this type cannot be checked since the type does not reduce to an inductive type, a function type or a quotient.
-/
#guard_msgs (substring := true) in
def atOpaqueNonempty : Bool :=
  withPtrEq nonemptyTrue nonemptyFalse (fun _ => false)
    (fun h => absurd h nonemptyTrue_ne_nonemptyFalse)

/-! ## Types that need several unfolding steps

The problematic type is only found after unfolding type definitions, applications of type-level
functions, and constructor fields of nested and mutual inductive types. Each rejected type is paired
with an accepted type of the same shape.
-/

namespace Deep

structure Bad where
  p : Prop

structure Good where
  s : String

structure Inner (α : Type) where
  f : Nat → Option α

inductive Middle (α : Type) where
  | leaf
  | node (xs : Array (Inner α × String)) (rest : Middle α)

structure Outer (α : Type) where
  id : Nat
  middle : Middle α

def OuterList (α : Type) := List (Outer α)
abbrev OuterThunk (α : Type) := Thunk (OuterList α)

/-! Through an abbreviation, a definition, a builtin type, a nested inductive and a function. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  OuterThunk Bad
because it contains values of type
  Prop
which are erased at runtime (in field `p` of constructor `Bad.mk`).
-/
#guard_msgs (substring := true) in
def atOuterThunk (a b : OuterThunk Bad) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def atOuterThunkOk (a b : OuterThunk Good) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def Twice (F : Type → Type) (α : Type) : Type := F (F α)
def Pairs (α : Type) : Type := List (α × α)

/-! Through applications of type-level functions taking a type function as argument. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Twice Pairs (Nat → Prop)
because it contains values of type
  Nat → Prop
which are erased at runtime (in field `fst` of constructor `Prod.mk`).
-/
#guard_msgs (substring := true) in
def atTwice (a b : Twice Pairs (Nat → Prop)) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def atTwiceOk (a b : Twice Pairs (Nat → Fin 3)) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def Nest (base : Type) : Nat → Type
  | 0 => base
  | n + 1 => Option (Nest base n) × Nat

/-! Through a recursive type-level function. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Nest Prop 3
because it contains values of type
  Nest Prop 0
which are erased at runtime (in field `val` of constructor `some`).
-/
#guard_msgs (substring := true) in
def atNest (a b : Nest Prop 3) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def atNestOk (a b : Nest String 3) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

mutual
inductive Forest (α : Type) where
  | nil
  | cons (t : PTree α) (f : Forest α)
inductive PTree (α : Type) where
  | node (label : Nat) (data : Nat → α) (children : Forest α)
end

/-! Through a mutual inductive type. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Forest Prop
because it contains values of type
  Nat → Prop
which are erased at runtime (in field `data` of constructor `PTree.node`).
-/
#guard_msgs (substring := true) in
def atForest (a b : Forest Prop) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def atForestOk (a b : Forest Good) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

inductive Rose (α : Type) where
  | node (label : α) (children : List (Rose α))

/-! Through the parameter of a nested inductive type. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Rose (List (Nat × Prop))
because it contains values of type
  Prop
which are erased at runtime (in field `snd` of constructor `Prod.mk`).
-/
#guard_msgs (substring := true) in
def atRose (a b : Rose (List (Nat × Prop))) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def atRoseOk (a b : Rose (List (Nat × String))) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def MyProp := Prop

structure UsesAlias where
  q : Option MyProp

/-! The message shows the field type before unfolding. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Array UsesAlias
because it contains values of type
  MyProp
which are erased at runtime (in field `val` of constructor `some`).
-/
#guard_msgs (substring := true) in
def atUsesAlias (a b : Array UsesAlias) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/-!
An irreducible alias of `Prop` must be seen through, even though the compiler's own erasure
predicate (`Meta.isTypeFormerType`, which uses default transparency) does not see through it:
`True` and `False` are erased where they are created, so both values below are the same object.
-/

def IrrProp := Prop
def irrTrue : IrrProp := True
def irrFalse : IrrProp := False
attribute [irreducible] IrrProp

structure UsesIrrAlias where
  q : IrrProp

theorem irrTrue_ne_irrFalse : UsesIrrAlias.mk irrTrue ≠ UsesIrrAlias.mk irrFalse := by
  intro h
  have h' := congrArg UsesIrrAlias.q h
  unfold irrTrue irrFalse at h'
  have : True = False := by with_unfolding_all exact h'
  exact this ▸ trivial

/-- info: true -/
#guard_msgs in
#eval unsafe withPtrEqUnsafe (UsesIrrAlias.mk irrTrue) (UsesIrrAlias.mk irrFalse) (fun _ => false)
  (fun h => absurd h irrTrue_ne_irrFalse)

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  UsesIrrAlias
because it contains values of type
  IrrProp
which are erased at runtime (in field `q` of constructor `UsesIrrAlias.mk`).
-/
#guard_msgs (substring := true) in
def atUsesIrrAlias : Bool :=
  withPtrEq (UsesIrrAlias.mk irrTrue) (UsesIrrAlias.mk irrFalse) (fun _ => false)
    (fun h => absurd h irrTrue_ne_irrFalse)

/-! Through the underlying type of a quotient. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Quot fun x x_1 => True
because it contains values of type
  Prop
which are erased at runtime (in field `p` of constructor `Bad.mk`).
-/
#guard_msgs (substring := true) in
def atQuot (a b : Quot (fun (_ _ : Option Bad) => True)) : Bool :=
  withPtrEq a b (fun _ => true) (fun _ => rfl)

def atQuotOk (a b : Quot (fun (_ _ : Option Good) => True)) : Bool :=
  withPtrEq a b (fun _ => true) (fun _ => rfl)

structure Dep where
  n : Nat
  xs : Tup n

structure DepOk where
  n : Nat
  xs : Fin n → String

/-! A field type that depends on an earlier field and therefore does not reduce. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Option Dep
because it contains values of type
  Tup n
which cannot be checked since the type does not reduce to an inductive type, a function type or a quotient (in field `xs` of constructor `Dep.mk`).
-/
#guard_msgs (substring := true) in
def atDep (a b : Option Dep) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def atDepOk (a b : Option DepOk) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/-! An opaque type deep inside. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  Array (Option (String × IO.Ref Nat))
because it contains values of type
  ST.RefPointed.type
which cannot be checked since the type does not reduce to an inductive type, a function type or a quotient (in field `ref` of constructor `ST.Ref.mk`).
-/
#guard_msgs (substring := true) in
def atRefDeep (a b : Array (Option (String × IO.Ref Nat))) : Bool :=
  withPtrEq a b (fun _ => true) (fun _ => rfl)

structure L3 (α : Type) where
  z : List α
structure L2 (α : Type) where
  y : Nat → Option (L3 α)
structure L1 (α : Type) where
  x : Array (L2 α)

structure P3 (α : Type) where
  z : List (Tagged α)
structure P2 (α : Type) where
  y : Nat → Option (P3 α)
structure P1 (α : Type) where
  x : Array (P2 α)

/-! A type variable deep inside; a type variable that only occurs as a phantom parameter is fine. -/

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  L1 α
because it contains values of type
  α
which cannot be checked since `α` is a type variable (in field `head` of constructor `List.cons`).
-/
#guard_msgs (substring := true) in
def atL1 {α : Type} (a b : L1 α) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

def atP1 {α : Type} (a b : P1 α) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

/-- Realistic library types with many layers. -/
def atHashMap (a b : Std.HashMap String (Array (Option Float))) : Bool :=
  withPtrEq a b (fun _ => true) (fun _ => rfl)

def atExpr (a b : Lean.Expr) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)

end Deep
