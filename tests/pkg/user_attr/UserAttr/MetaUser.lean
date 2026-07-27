module

public meta import UserAttr.MetaMid
meta import Lean.Elab.GuardMsgs

/-! Regression test for https://github.com/leanprover/lean4/issues/13599: using `@[my_simp]` (an
attribute registered in `UserAttr.BlaAttr`) while reaching `BlaAttr` only via a `meta import`
chain (`UserAttr.MetaMid → import UserAttr.BlaAttr`) used to make `shake --fix` flip-flop. The
elaborator now rejects such uses with a clear error pointing at the missing import. -/

@[expose] public section

/--
error: Cannot use attribute `[my_simp]`: module `UserAttr.BlaAttr` is loaded for IR only (reached as a private `meta` dependency). Add an import of `UserAttr.BlaAttr`.
-/
#guard_msgs in
@[my_simp]
theorem midVal_eq : midVal = 17 := rfl

end
