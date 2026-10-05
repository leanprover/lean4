import Lean
import Std.Data.TreeMap
import Std.Data.HashMap

/-!
Tests that the `Ord`, `BEq`, `DecidableEq` and `Hashable` deriving handlers mark their auxiliary
functions `@[inline]` for small structures (non-recursive single-constructor types with at most three
fields by default, configurable via `deriving.inline_threshold`), so that, e.g., comparisons are
inlined when such a structure serves as the key of a tree map.
-/

open Lean Compiler

structure Small where
  a : Nat
  b : String
  c : Bool
  deriving Ord, BEq, DecidableEq, Hashable

structure Large where
  a : Nat
  b : String
  c : Bool
  d : Nat
  deriving Ord, BEq, DecidableEq, Hashable

structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Ord, BEq, DecidableEq, Hashable

inductive SmallInductive where
  | mk (a : Nat) (b : Nat)
  deriving Ord, BEq, DecidableEq, Hashable

inductive TwoCtors where
  | a (n : Nat)
  | b (n : Nat)
  deriving Ord, BEq, DecidableEq, Hashable

inductive Chain where
  | mk (n : Nat) (next : Chain)
  deriving Ord, BEq, DecidableEq, Hashable

/-- Returns which of the derived `Ord`, `BEq`, `DecidableEq` and `Hashable` functions of `typeName` are `@[inline]`. -/
def inlineAttrs (typeName : Name) : CoreM (List Bool) := do
  let env ← getEnv
  let fns := [(`Ord, `ord), (`BEq, `beq), (`DecidableEq, `decEq), (`Hashable, `hash)]
  fns.mapM fun (cls, fn) => do
    let declName := (Name.mkSimple s!"inst{cls}{typeName}") ++ fn
    unless env.contains declName do
      throwError "unknown {declName}"
    return getInlineAttribute? env declName == some .inline

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval inlineAttrs `Small

/-- info: [false, false, false, false] -/
#guard_msgs in
#eval inlineAttrs `Large

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval inlineAttrs `Pair

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval inlineAttrs `SmallInductive

/-- info: [false, false, false, false] -/
#guard_msgs in
#eval inlineAttrs `TwoCtors

/-- info: [false, false, false, false] -/
#guard_msgs in
#eval inlineAttrs `Chain

/-! `deriving.inline_threshold` sets the maximal number of fields. -/

set_option deriving.inline_threshold 4 in
structure LargeRaised where
  a : Nat
  b : String
  c : Bool
  d : Nat
  deriving Ord, BEq, DecidableEq, Hashable

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval inlineAttrs `LargeRaised

set_option deriving.inline_threshold 1 in
structure SmallLowered where
  a : Nat
  b : Nat
  deriving Ord, BEq, DecidableEq, Hashable

/-- info: [false, false, false, false] -/
#guard_msgs in
#eval inlineAttrs `SmallLowered

structure Standalone where
  a : Nat
  b : Nat

set_option deriving.inline_threshold 0 in
deriving instance Ord, BEq, DecidableEq, Hashable for Standalone

/-- info: [false, false, false, false] -/
#guard_msgs in
#eval inlineAttrs `Standalone

/-!
Check that the derived functions are actually inlined into the compiled code, in particular into
the specializations of the tree map and hash map operations.
-/

/--
Returns the declarations called by the compiled code of `declName`, including those called
transitively through other declarations of the current module such as specializations.
-/
def compiledCallees (declName : Name) : CoreM NameSet := do
  let env ← getEnv
  let mut todo := #[declName]
  let mut seen : NameSet := {}
  repeat
    let some n := todo.back? | break
    todo := todo.pop
    unless seen.contains n do
      seen := seen.insert n
      if (env.getModuleIdxFor? n).isNone then
        if let some decl := IR.findEnvDecl env n then
          todo := todo ++ IR.collectUsedDecls env [decl]
  return seen

/-- Returns whether the compiled code of `declName` calls the instance `instName` or its auxiliary functions. -/
def callsInstance (declName instName : Name) : CoreM Bool :=
  return (← compiledCallees declName).any (instName.isPrefixOf ·)

def compareSmall (x y : Small) : Ordering := compare x y
def beqSmall (x y : Small) : Bool := x == y
def decEqSmall (x y : Small) : Bool := decide (x = y)
def hashSmall (x : Small) : UInt64 := hash x
def treeMapSmall (m : Std.TreeMap Small Nat) (k : Small) : Option Nat := m[k]?
def hashMapSmall (m : Std.HashMap Small Nat) (k : Small) : Option Nat := m[k]?

def compareLarge (x y : Large) : Ordering := compare x y
def beqLarge (x y : Large) : Bool := x == y
def decEqLarge (x y : Large) : Bool := decide (x = y)
def hashLarge (x : Large) : UInt64 := hash x
def treeMapLarge (m : Std.TreeMap Large Nat) (k : Large) : Option Nat := m[k]?
def hashMapLarge (m : Std.HashMap Large Nat) (k : Large) : Option Nat := m[k]?

/-- info: [false, false, false, false, false, false, false] -/
#guard_msgs in
#eval [
  callsInstance ``compareSmall ``instOrdSmall,
  callsInstance ``beqSmall ``instBEqSmall,
  callsInstance ``decEqSmall ``instDecidableEqSmall,
  callsInstance ``hashSmall ``instHashableSmall,
  callsInstance ``treeMapSmall ``instOrdSmall,
  callsInstance ``hashMapSmall ``instBEqSmall,
  callsInstance ``hashMapSmall ``instHashableSmall
].mapM id

/-- info: [true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [
  callsInstance ``compareLarge ``instOrdLarge,
  callsInstance ``beqLarge ``instBEqLarge,
  callsInstance ``decEqLarge ``instDecidableEqLarge,
  callsInstance ``hashLarge ``instHashableLarge,
  callsInstance ``treeMapLarge ``instOrdLarge,
  callsInstance ``hashMapLarge ``instBEqLarge,
  callsInstance ``hashMapLarge ``instHashableLarge
].mapM id
