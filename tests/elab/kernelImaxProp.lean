import Lean.CoreM
import Lean.AddDecl

/-!
The kernel must recognize a sort as `Prop` up to level normalization.

`KMWeird : Sort (imax 1 0)` is a proposition: `imax 1 0` normalizes to `0`. The
inductive is therefore legitimate, and the kernel is right to allow its `Bool`
field, exactly as it would for any other inductive predicate. What must not be
allowed is projecting that field back out, since proof irrelevance equates
`KMWeird.mk false` and `KMWeird.mk true`.
-/

open Lean

#eval show CoreM Unit from
  addDecl <| .inductDecl [] 0 [
    { name := `KMDummy
      type := .sort .zero
      ctors := [{ name := `KMDummy.intro, type := .const `KMDummy [] }] },
    { name := `KMWeird
      type := .sort (.imax (.succ .zero) .zero)
      ctors := [{ name := `KMWeird.mk
                  type := .forallE `value (.const ``Bool []) (.const `KMWeird []) .default }] }
  ] false

def KMAsProp : Prop := KMWeird

theorem kmLeft : KMAsProp := KMWeird.mk false
theorem kmRight : KMAsProp := KMWeird.mk true

/-- The inductive really is a proposition, so proof irrelevance applies. -/
theorem kmProofIrrel : kmLeft = kmRight := rfl

/--
error: (kernel) invalid projection
  proof.1
-/
#guard_msgs in
#eval addDecl <| .defnDecl {
  name := `kmLeak
  levelParams := []
  type := .forallE `proof (.const ``KMAsProp []) (.const ``Bool []) .default
  value := .lam `proof (.const ``KMAsProp []) (.proj `KMWeird 0 (.bvar 0)) .default
  hints := .abbrev
  safety := .safe }
