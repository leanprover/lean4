/-!
The first pass of `isDefEqArgs` must apply the `.implicit` transparency bump too.

Reduced from `CategoryTheory.Abelian.subobjectIsoSubobjectOp` in Mathlib's
`CategoryTheory/Abelian/Subobject.lean` — the order isomorphism
`Subobject X ≃o (Subobject (op X))ᵒᵈ` — whose proof stops elaborating without the bump,
failing to synthesize `Mono (kernel.ι (cokernel.π f))`.

`isDefEqArgsFirstPass` unifies an argument pair eagerly when one side is an unassigned
metavariable, instead of postponing it to the second pass. Such a pair is still an argument
unification at an implicit position, so it gets the same transparency bump as the second pass:
whether an argument is checked at `.implicit` must not depend on which side happens to be an
unassigned metavariable.

Below, synthesizing `Mono (limitPi f)` applies `limitPiMono`, whose conclusion is
`Mono (limitPi ?f ?inst)`. The instance-implicit `?inst` is unassigned, so the first pass takes
the eager branch and assigns it `h`. Checking that assignment compares `HasLimit f` against
`HasLimit (ofOpp (toOpp f))`, which fails at `.instances` because `ofOpp` and `toOpp` are
`implicit_reducible`. The `backward.isDefEq.instanceTypes` fallback then synthesizes `HasLimit f`
via `hasLimitAll` and compares `h` against the result — and *that* comparison runs at the ambient
transparency. Bumped to `.implicit` it reduces `ofOpp (toOpp f)` to `f` and the two proofs match;
at `.instances` it does not, and synthesis fails with `failed to synthesize Mono (limitPi f)`.

There the assignment reads
`(?m : HasEqualizer (cokernel.π f) 0) := (h : HasKernel (cokernel.π f).op.unop)`, and the
`implicit_reducible` definitions are `Quiver.Hom.op` and `Quiver.Hom.unop`.
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
