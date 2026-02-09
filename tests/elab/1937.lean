structure BundledFunction (α β : Sort _) :=
(toFun : α → β)

namespace BundledFunction

-- `simp` doesn't seem to unify partial applications of structure projections:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60simp.60.20failing.20on.20partial.20application.20of.20projections
def id (α) : BundledFunction α α := ⟨λ a => a⟩

@[simp] theorem coe_id : (id α).toFun = _root_.id := rfl

example (x : α) : (id α).toFun x = x :=
by simp only [coe_id, id_eq] -- should succeed
example (x : α) : (id α).toFun x = x :=
by rw [coe_id, id_eq] -- succeeds

-- seems to be another instance of the same behaviour:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60simp.60.20calls.20broken.20in.20mathlib4.23922/near/314790371

def otherProjection (f : BundledFunction α β) : α → β := f.toFun

-- Projections functions are expanded when populating the discrimination tree, and are indexed as `Expr.proj` objects.
-- `@toFun α β` cannot be expanded into `Expr.proj` since there is a missing argument. The workaround is to add the missing argument.
-- Then, we get `a.1 = otherProjection a`
@[simp] theorem toFun_eq_otherProjection : @toFun α β a = otherProjection a := rfl
@[simp] theorem id_apply : (id α).otherProjection x = x := rfl

example : (id α).toFun x = x := by simp only [toFun_eq_otherProjection, id_apply]; done -- should work
example : (id α).toFun x = x := by rw [toFun_eq_otherProjection, id_apply] -- succeeds

end BundledFunction

-- `simp` is happy with partial applications in other functions:
def id2 (x : α) := x

@[simp] theorem id2_eq_id : @id2 α = id := rfl

example : id2 x = x := by simp only [id2_eq_id, id_eq] -- works fine
example : id2 x = x := by rw [id2_eq_id, id_eq] -- succeeds
