/-!
Reduced from `CategoryTheory.Abelian.subobjectIsoSubobjectOp` in Mathlib's
`CategoryTheory/Abelian/Subobject.lean`, which needs `Mono (kernel.ι (cokernel.π f))`.

Below, synthesizing `Mono (limitPi f)` applies `limitPiMono`, whose conclusion is
`Mono (limitPi ?f ?inst)`. The instance-implicit `?inst` is unassigned, so the first pass of
`isDefEqArgs` assigns it `h`. Checking that assignment compares `HasLimit f` against
`HasLimit (ofOpp (toOpp f))`, which fails at instance transparency because `ofOpp` and `toOpp` are
`implicit_reducible`. So the assignment is rejected (see
`backward.isDefEq.respectTransparency.instanceTypes`) and synthesis fails.

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

/--
error: failed to synthesize instance of type class
  Mono (limitPi f)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (f : Nat) (h : HasLimit (ofOpp (toOpp f))) : Mono (@limitPi f h) := inferInstance

#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceTypes false in
example (f : Nat) (h : HasLimit (ofOpp (toOpp f))) : Mono (@limitPi f h) := inferInstance
