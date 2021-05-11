universe u v w

structure A (α : Type u) :=
(f : (β : Type u) → α → β → α)

set_option pp.all true

structure B (α : Type u) extends A α :=
(x : Nat)
(f := fun β a b => a)

#check B.f._default

#check { x := 10 : B Nat}

namespace New

structure A (α : Type u) where
  f : (β : Type u) → α → β → α

structure B (α : Type u) extends A α where
  x : Nat
  f := fun β a b => a

#check B.f._default

#check { x := 10 : B Nat }

structure Data where
  index?   : Option Nat := none
  lowlink? : Option Nat := none
  onStack  : Bool       := false

structure State (α : Type) where
  stack     : List α := []
  nextIndex : Nat := 0
  data      : Array Data := #[]
  sccs      : List (List α) := []

inductive Format where
  | nil                 : Format
  | line                : Format
  | text                : String → Format
  | nest (indent : Int) : Format → Format
  | append              : Format → Format → Format
  | group               : Format → Format

class MonadControl (m : Type u → Type v) (n : Type u → Type w) where
  stM          : Type u → Type u
  liftWith {α} : (({β : Type u} → n β → m (stM β)) → m α) → n α
  restoreM {α} : m (stM α) → n α

instance : MonadControl m (ReaderT ρ m) where
  stM        := id
  liftWith f := fun ctx => f fun x => x ctx
  restoreM x := fun ctx => x

instance [Monad m] : MonadControl m (StateT σ m) where
  stM α := α × σ
  liftWith f := do let s ← get; liftM (f (fun x => x.run s))
  restoreM x := do let (a, s) ← liftM x; set s; pure a

end New
