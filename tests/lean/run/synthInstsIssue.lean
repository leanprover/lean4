/-!
This is a minimization of an issue widely seen in Mathlib after
https://github.com/leanprover/lean4/pull/2793.
We find that we need to either specify a named argument or use `..` in certain rewrites.
-/

section Mathlib.Algebra.Group.Defs

universe u v w

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

class SMul (M : Type u) (α : Type v) where
  smul : M → α → α

infixr:73 " • " => HSMul.hSMul

instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

end Mathlib.Algebra.Group.Defs

section Mathlib.Data.FunLike.Basic

class DFunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  coe : F → ∀ a : α, β a

abbrev FunLike F α β := DFunLike F α fun _ => β

instance (priority := 100) hasCoeToFun {F α β} [_i : DFunLike F α β] :
    CoeFun F (fun _ ↦ ∀ a : α, β a) where
  coe := @DFunLike.coe _ _ β _

end Mathlib.Data.FunLike.Basic

section Mathlib.Algebra.Group.Hom.Defs

variable {M N : Type _}
variable {F : Type _}

class ZeroHomClass (F : Type _) (M N : outParam (Type _)) [Zero M] [Zero N] [FunLike F M N] :
    Prop where
  map_zero : ∀ f : F, f 0 = 0

variable [Zero M] [Zero N] [FunLike F M N]

theorem map_zero [ZeroHomClass F M N] (f : F) : f 0 = 0 :=
  ZeroHomClass.map_zero f

end Mathlib.Algebra.Group.Hom.Defs

section Mathlib.GroupTheory.GroupAction.Defs

variable {M A : Type _}

class SMulZeroClass (M A : Type _) [Zero A] extends SMul M A where
  smul_zero : ∀ a : M, a • (0 : A) = 0

@[simp]
theorem smul_zero [Zero A] [SMulZeroClass M A] (a : M) : a • (0 : A) = 0 :=
  SMulZeroClass.smul_zero _

end Mathlib.GroupTheory.GroupAction.Defs

section Mathlib.Algebra.SMulWithZero

variable (R M)

class SMulWithZero [Zero R] [Zero M] extends SMulZeroClass R M where

@[simp]
theorem zero_smul {M} [Zero R] [Zero M] [SMulWithZero R M] (m : M) : (0 : R) • m = 0 := sorry

end Mathlib.Algebra.SMulWithZero

section Mathlib.GroupTheory.GroupAction.Hom

class MulActionSemiHomClass (F : Type _)
    {M N : outParam (Type _)} (φ : outParam (M → N))
    (X Y : outParam (Type _)) [SMul M X] [SMul N Y] [FunLike F X Y] : Prop where
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)

export MulActionSemiHomClass (map_smulₛₗ)

end Mathlib.GroupTheory.GroupAction.Hom

section Mathlib.Algebra.Module.LinearMap.Defs

variable {R S S₃ T M M₃ : Type _}

class LinearMapClass (F : Type _) (R : outParam (Type _))
  (M M₂ : outParam (Type _)) [Add M] [Add M₂]
    [SMul R M] [SMul R M₂] [FunLike F M M₂] : Prop
    extends MulActionSemiHomClass F (id : R → R) M M₂

variable (F : Type _)
variable [Zero R]
variable [Zero M] [Add M] [Zero M₃] [Add M₃]
variable [SMulWithZero R M] [SMulWithZero R M₃]

def inst1 [FunLike F M M₃] [LinearMapClass F R M M₃] : ZeroHomClass F M M₃ :=
  { map_zero := fun f ↦
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), @map_smulₛₗ]
        simp only [id_eq, zero_smul]
  }

def inst2 [FunLike F M M₃] [LinearMapClass F R M M₃] : ZeroHomClass F M M₃ :=
  { map_zero := fun f ↦
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), map_smulₛₗ (N := R)]
        simp only [id_eq, zero_smul]
  }

def inst3 [FunLike F M M₃] [LinearMapClass F R M M₃] : ZeroHomClass F M M₃ :=
  { map_zero := fun f ↦
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), map_smulₛₗ ]
        simp only [id_eq, zero_smul]
  }

def inst4 [FunLike F M M₃] [LinearMapClass F R M M₃] : ZeroHomClass F M M₃ :=
  { map_zero := fun f ↦
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), map_smulₛₗ ..]
        simp only [id_eq, zero_smul]
  }

end Mathlib.Algebra.Module.LinearMap.Defs
