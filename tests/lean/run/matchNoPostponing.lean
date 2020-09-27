new_frontend

/- In the following example, type of `x` and `y` could be any type `α` s.t. `[HasOfNat α]`.
   It relies on `SyntheticMVarKind.withDefault` to set `α := Nat`.
   Moreover, we must commit to `α := Nat` before we try to build de `matcher` since
   `mkMatcher` assumes `matchType` does not contain metavariables.
   We accomplish that by invoking `synthesizeSyntheticMVarsNoPostponing` at `elabMatch`. -/
def foo : IO Unit := do
let (x, y) ← pure (0, 0);
IO.println x
