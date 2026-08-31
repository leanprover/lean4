module

/-!
`builtin_initialize` and `initialize` in a `module` without `private`/`public` should work, even
when the type references a non-public declaration.
-/

structure MyState where
  value : Nat := 0
  deriving Inhabited

builtin_initialize myState : IO.Ref MyState ← IO.mkRef {}
initialize myState' : IO.Ref MyState ← IO.mkRef {}

builtin_initialize
  myState.modify fun s => { s with value := s.value + 1 }

-- Exercise match auxiliary generation inside `initialize` (reproducer for Batteries issue)
initialize myRef : IO.Ref Nat ← do
  let x : Nat ⊕ Nat := .inl 42
  let v := match x with
    | .inl n => n
    | .inr n => n + 1
  IO.mkRef v

initialize
  myRef.modify (· + 1)
