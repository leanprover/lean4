def iscoh_wmap {A:Type _}{B:Type _} : (A -> B) -> Type _ :=
  fun f => @Subtype (B -> A) fun r => ∀ a , a = r (f a)
def wmap : Type _ -> Type _ -> Type _ :=
  fun A B => @Sigma (A -> B) fun f => iscoh_wmap f

def hgroup : Nat -> Type _ -> Type _
| .zero , T => wmap T T
| .succ a, T => wmap (hgroup a T) (hgroup a T)

example : hgroup 0 Unit := by
  unfold hgroup
  admit

-- TODO: we should improve univere inference. It should be
-- hgroup.{u} : Nat → Type u → Type u
/--
info: hgroup.{u_1, u_2} : Nat → Type (max u_1 u_2) → Type (max u_1 u_2)
-/
#guard_msgs in
#check hgroup
