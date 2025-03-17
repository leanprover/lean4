import Lean
open Lean

inductive Entry
| name (n : Name)
| level (n : Level)
| expr (n : Expr)
| defn (n : Name)
deriving Inhabited

structure Alloc (α) [BEq α] [Hashable α] where
  map : HashMap α Nat
  next : Nat
deriving Inhabited

namespace Export

structure State where
  names : Alloc Name := ⟨HashMap.empty.insert Name.anonymous 0, 1⟩
  levels : Alloc Level := ⟨HashMap.empty.insert levelZero 0, 1⟩
  exprs : Alloc Expr
  defs : HashSet Name
  stk : Array (Bool × Entry)
deriving Inhabited

class OfState (α : Type) [BEq α] [Hashable α] where
  get : State → Alloc α
  modify : (Alloc α → Alloc α) → State → State

instance : OfState Name where
  get s := s.names
  modify f s := { s with names := f s.names }

instance : OfState Level where
  get s := s.levels
  modify f s := { s with levels := f s.levels }

instance : OfState Expr where
  get s := s.exprs
  modify f s := { s with exprs := f s.exprs }

end Export

abbrev ExportM := StateT Export.State CoreM

namespace Export

def alloc {α} [BEq α] [Hashable α] [OfState α] (a : α) : ExportM Nat := do
  let n := (OfState.get (α := α) (← get)).next
  modify $ OfState.modify (α := α) fun s => {map := s.map.insert a n, next := n+1}
  pure n

def exportName (n : Name) : ExportM Nat := do
  match (← get).names.map.find? n with
  | some i => pure i
  | none => match n with
    | .anonymous => pure 0
    | .num p a => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | .str p s => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i

attribute [simp] exportName

def exportLevel (L : Level) : ExportM Nat := do
  match (← get).levels.map.find? L with
  | some i => pure i
  | none => match L with
    | Level.zero => pure 0
    | Level.succ l =>
      let i ← alloc L; IO.println s!"{i} #US {← exportLevel l}"; pure i
    | Level.max l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | Level.imax l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UIM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | Level.param n =>
      let i ← alloc L; IO.println s!"{i} #UP {← exportName n}"; pure i
    | Level.mvar n => unreachable!

-- TODO: this test has been broken for a while with a panic that was ignored by the test suite
--attribute [simp] exportLevel
