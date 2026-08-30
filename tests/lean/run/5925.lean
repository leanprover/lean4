/-!
# Regression test for issue 5925
https://github.com/leanprover/lean4/issues/5925

This test was provided by @mik-jozef as an example that failed in v4.15.0-rc1 but is OK as of a nightly for 4.16.
It is possible that this is the same issue as the one originally reported, but we have not checked.

A difficulty is that the original reported example does not typecheck due to other fixes (#6024).
We ought to verify that https://github.com/leanprover/lean4/pull/6414 indeed is the reason that the test in this file passes.
-/

def Set (D: Type) := D → Prop

structure ValVar where
  d: Empty
  x: Nat

structure Salgebra where
  D: Type
  I: Empty → Empty

def pairSalgebra: Salgebra := ⟨Empty, nofun⟩

structure Cause (D: Type) where
  contextIns: Set Nat

mutual
inductive Ins (salg: Salgebra): Prop

inductive IsCauseInapplicable (salg: Salgebra):
  Cause salg.D → Prop

| blockedContextIns
  (cause: Cause salg.D)
  (inContextIns: cause.contextIns 0)
:
  IsCauseInapplicable salg cause
end

def IsVarFree (x: Nat): Prop := ∀ d, ValVar.mk d x ∉ []

def extOfIntCause
  (internalCause: Cause Empty)
:
  Cause Empty
:= {
  contextIns :=
    fun _ => ∃ vvI, internalCause.contextIns vvI ∧ IsVarFree vvI
}

def insInternalToInsExternal
  (isInapp: IsCauseInapplicable pairSalgebra internalCause)
:
  IsCauseInapplicable pairSalgebra (extOfIntCause internalCause)
:=
  isInapp.rec
    (motive_1 := fun _ => True)
    (motive_2 :=
      fun cause _ =>
        IsCauseInapplicable pairSalgebra (extOfIntCause cause))
    (fun cause inCins =>
      IsCauseInapplicable.blockedContextIns
        (salg := pairSalgebra)
        (extOfIntCause cause)
        (⟨_, inCins, nofun⟩))
