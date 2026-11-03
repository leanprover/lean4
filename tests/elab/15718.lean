/-!
Casting between `IO.Ref`s of different types is not possible without `unsafe`
-/

/--
error: Application type mismatch: The argument
  ref.ref
has type
  (ST.RefPointed IO.RealWorld α).type
but is expected to have type
  (ST.RefPointed IO.RealWorld β).type
in the application
  ST.Ref.mk ref.ref
-/
#guard_msgs in
def «"safe"Cast» {α β : Type} [Nonempty β] (x : α) : BaseIO β := do
  let ref : IO.Ref α ← IO.mkRef x
  let ref : IO.Ref β := ⟨ref.ref, inferInstance⟩ -- error here
  ref.get
