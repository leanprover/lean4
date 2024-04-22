/-
# Testing monad lift coercion elaborator

The functions inserted for the coercions are supposed to be inlined immediately during elaboration.
-/

variable (p : Nat → Prop) (m : IO (Subtype p))

/-!
`Lean.Internal.liftCoeM`
-/
#check (m : (ReaderT Int IO) Nat)

/-!
`Lean.Internal.coeM`
-/
#check (m : IO Nat)
