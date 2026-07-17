module

/-!
`recOn` references are rejected during `toDecl` (no structural translation, never compiled as a
function). Inside `noncomputable section` that failure must be swallowed by marking the definition
`noncomputable` — also under postponed compilation, where the eager `toDecl` run is what observes
the failure before `leanir` would hit it as a hard error.
-/

public inductive TwoCtor
  | a
  | b

noncomputable section

/-- Compiles by being marked `noncomputable`, not by generating code. -/
public def twoCtorElim (t : TwoCtor) : Nat :=
  TwoCtor.recOn t 0 1

end
