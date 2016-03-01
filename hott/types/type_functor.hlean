/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

Pointed and unpointed type functor, and adjoint pairs.
More or less ported from Evan Cavallo's HoTT-Agda homotopy library.
-/

import types.pointed

open equiv function pointed

structure type_functor : Type :=
  (fun_ty : Type → Type)
  (fun_arr : Π {A B}, (A → B) → (fun_ty A → fun_ty B))
  (respect_id : Π {A}, fun_arr (@id A) = id)
  (respect_comp : Π {A B C} (g : B → C) (f : A → B),
    fun_arr (g ∘ f) = (fun_arr g) ∘ (fun_arr f))

attribute [coercion] type_functor.fun_ty

section type_adjoint
open type_functor

structure type_adjoint (F G : type_functor) : Type :=
  (η : Π X, X → G (F X))
  (ε : Π U, F (G U) → U)
  (ηnat : Π X Y (h : X → Y), η Y ∘ h = fun_arr G (fun_arr F h) ∘ η X)
  (εnat : Π U V (k : U → V), ε V ∘ fun_arr F (fun_arr G k) = k ∘ ε U)
  (εF_Fη : Π X, ε (F X) ∘ fun_arr F (η X) = id)
  (Gε_ηG : Π U, fun_arr G (ε U) ∘ η (G U) = id)

end type_adjoint

structure Type_functor : Type :=
  (fun_ty : Type* → Type*)
  (fun_arr : Π {A B}, (A →* B) → (fun_ty A →* fun_ty B))
  (respect_id : Π {A}, fun_arr (pid A) = pid (fun_ty A))
  (respect_comp : Π {A B C} (g : B →* C) (f : A →* B),
    fun_arr (g ∘* f) = fun_arr g ∘* fun_arr f)

attribute [coercion] Type_functor.fun_ty

section Type_adjoint
open Type_functor

structure Type_adjoint (F G : Type_functor) : Type :=
  (η : Π (X : Type*), X →* G (F X))
  (ε : Π (U : Type*), F (G U) →* U)
  (ηnat : Π {X Y} (h : X →* Y), η Y ∘* h = (fun_arr G (fun_arr F h)) ∘* η X)
  (εnat : Π {U V} (k : U →* V), ε V ∘* (fun_arr F (fun_arr G k)) = k ∘* ε U)
  (εF_Fη : Π {X}, ε (F X) ∘* (fun_arr F (η X)) = !pid)
  (Gε_ηG : Π {U}, (fun_arr G (ε U)) ∘* η (G U) = !pid)

end Type_adjoint
