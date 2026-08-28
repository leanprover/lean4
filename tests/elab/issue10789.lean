/-!
# Kernel should accept nested inductives involving private constructors

https://github.com/leanprover/lean4/issues/10789
-/

/-!
Example from issue. The `Rec` structure used to report
`error: (kernel) constant has already been declared '_private.«external:...».0.Box.mk'`
-/
structure Box (α : Type u) where
  private mk ::
  val : α

structure Rec where
  box? : Option (Box Rec)
