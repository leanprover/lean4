/-!
The first pass of `isDefEqArgs` must bump to transparency for implicit arguments, just like the
second pass.

Reduced from `CategoryTheory.Abelian.subobjectIsoSubobjectOp` in Mathlib's
`CategoryTheory/Abelian/Subobject.lean`, which otherwise fails to synthesize
`Mono (kernel.ι (cokernel.π f))`.

`isDefEqArgsFirstPass` immediately unifies an argument pair when one side is an unassigned
metavariable instead of postponing it to the second pass. Such a pair is still an argument
unification at an implicit position, but originally, the assignment did not involve a unification
problem, so transparency did not matter. Since `respectTransparency.isDefEq.respectTransparency.instanceSearchTypes`, however,
the assignment can fall back to synthesizing an instance and unifying with it, and the transparency
of the unification should be exactly the same as if it happened in the second pass.

Below, synthesizing `Mono (limitPi f)` applies `limitPiMono`, whose conclusion is
`Mono (limitPi ?f ?inst)`. The instance-implicit `?inst` is unassigned, so the first pass assigns it
`h`. Checking that assignment compares `HasLimit f` against `HasLimit (ofOpp (toOpp f))`, which
fails at instance transparency because `ofOpp` and `toOpp` are `implicit_reducible`. Lean falls
back to synthesizing `HasLimit f` via `hasLimitAll` and compares `h` against the result.
That comparison runs at the ambient transparency. Bumped to implicit transparency, it reduces
`ofOpp (toOpp f)` to `f` and the two proofs match. At `.instances`, it does not, and synthesis fails
with `failed to synthesize Mono (limitPi f)`.

In the original situation from mathlib, the assignment read
`(?m : HasEqualizer (cokernel.π f) 0) := (h : HasKernel (cokernel.π f).op.unop)`, and the
`implicit_reducible` definitions were `Quiver.Hom.op` and `Quiver.Hom.unop`.
-/

@[implicit_reducible] def toOpp (a : Nat) : Nat := a
@[implicit_reducible] def ofOpp (a : Nat) : Nat := a

class HasLimit (f : Nat) : Prop where
instance hasLimitAll (f : Nat) : HasLimit f := ⟨⟩

opaque limitObj : Nat → Nat
def limitPi (f : Nat) [HasLimit f] : Nat := limitObj f

class Mono (g : Nat) : Prop where
instance limitPiMono (f : Nat) [HasLimit f] : Mono (limitPi f) := ⟨⟩

example (f : Nat) (h : HasLimit (ofOpp (toOpp f))) : Mono (@limitPi f h) := inferInstance
