/-!
# Tests of `kabstract`
-/

/-!
Issue: kabstract was not doing isDefEq of types before testing isDefEq of the terms themselves.
This could lead to reasonable terms not unifying.

In this example, the issue is that `rw [SPred.and_cons]` tries unifying the `SPred.and ...` expressions directly,
and since `σs` is implicit, all the explicit arguments fail.
Instead, by first unifying the types the `σs`s are solved for immediately.
-/

namespace Test1

abbrev SPred : List Type → Type
  | []    => Prop
  | σ::σs => σ → SPred σs

def SPred.and (P Q : SPred σs) : SPred σs := match σs with
  | []    => P ∧ Q
  | σ::σs => fun s => and (P s) (Q s)

theorem SPred.and_cons {P Q : SPred (σ::σs)} {s : σ} : SPred.and P Q s = SPred.and (P s) (Q s) := rfl

example {s : Nat} : (SPred.and (fun s => True) (fun s => True) : SPred [Nat]) s = True ∧ True := by
  rw [SPred.and_cons]; simp
  exact And.intro trivial trivial

end Test1
