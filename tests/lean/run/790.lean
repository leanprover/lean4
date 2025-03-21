class Vec (X : Type) extends Add X, Inhabited X

class Vec' (X : Type) extends Vec X

def differential {X Y : Type} [Vec X] [Vec Y] (f : X → Y) (x dx : X) : Y := f dx

@[simp]
theorem differential_of_linear {X Y : Type} [Vec X] [Vec Y] (f : X → Y) (x dx : X)
        : differential f x dx = f dx := by simp[differential]

example {X Y : Type} [Vec X] [Vec Y] (f : X → Y) (x dx : X)
        : differential f x dx = f dx := by simp

instance : Vec Nat := ⟨⟩
instance : Vec' Nat := ⟨⟩

set_option trace.Meta.Tactic.simp true
/--
info: [Meta.Tactic.simp.rewrite] differential_of_linear:1000:
      differential f x dx
    ==>
      f dx
[Meta.Tactic.simp.rewrite] eq_self:1000: f dx = f dx ==> True
-/
#guard_msgs in
example {Y : Type} [Vec Y] (f : Nat → Y) (x dx : Nat)
        : @differential _ _ Vec'.toVec _ f x dx = f dx :=
  by simp
