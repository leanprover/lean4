example : Except String Nat := do
  try
    -- The try block has result type Unit:
    pure ()
  catch _ =>
    -- The doLetElse here should not "eat" the `return 42` as its body seq.
    -- If it does, we'd get a type error because the result type is not Unit.
    let .some true := none | throw "error"
  return 42

example : Except String Nat := do
  try
    -- The try block has result type Unit:
    pure ()
  catch _ =>
    -- The doLetArrow here should not "eat" the `return 42` as its body seq.
    -- If it does, we'd get a type error because the result type is not Unit.
    let .some true ← pure none | throw "error"
  return 42
