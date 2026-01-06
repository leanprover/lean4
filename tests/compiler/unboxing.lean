@[noinline]
def discardIO (a : α) : BaseIO Unit :=
  go (a, pure ())
where
  go (x : α × BaseIO Unit) : BaseIO Unit := x.2

def myStructConst : UInt8 × UInt16 × UInt32 × UInt64 × USize × Float × Float32 × Nat :=
  (1, 2, 3, 4, 5, 6, 7, 8)

@[unbox]
inductive SpecialValue (α : Type) where
  | thing (a b : Nat) (c : UInt8) (d : UInt32) (e : USize)
  | nothing
  | something (x : α)
deriving Repr

@[noinline] def special1 (_ : Unit) : SpecialValue Nat := .thing 1 2 3 4 5
@[noinline] def special2 (_ : Unit) : SpecialValue (Nat × Nat) := .nothing
@[noinline] def special3 (_ : Unit) : SpecialValue (Nat × Nat) := .something (2, 3)
@[noinline] def special4 (_ : Unit) : SpecialValue Prop := .something True

instance : Repr Prop where
  reprPrec _ _ := "_"


@[noinline]
def myFunc (x : α × (Nat × Nat)) : Nat := x.2.1 + x.2.2

@[noinline]
def myOtherFunc (x : α) : (Nat × Nat) × α := ((1, 2), x)

@[noinline]
def reshapeTest (x : Nat × Nat) : Nat :=
  myFunc (myOtherFunc x)

set_option compiler.extract_closed false in
def main : IO Unit := do
  -- Access a persistent builtin `struct` declaration
  let a := stdRange
  discardIO a.1
  -- Ensure that struct constructors with scalar values work
  IO.println (repr myStructConst)
  -- Construct different values of the `SpecialValue` type
  IO.println (repr (special1 ()))
  IO.println (repr (special2 ()))
  IO.println (repr (special3 ()))
  IO.println (repr (special4 ()))
  -- box them
  IO.println (repr [special1 ()])
  IO.println (repr [special2 ()])
  IO.println (repr [special3 ()])
  IO.println (repr [special4 ()])
  -- try a reshape
  IO.println (reshapeTest (1, 2))
