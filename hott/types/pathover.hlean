/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Pathovers.
Note that the basic definitions are in init.pathover
-/

import types.squareover

open eq equiv is_equiv equiv.ops

namespace eq

  variables {A A' : Type} {B B' : A → Type} {C : Πa, B a → Type}
            {a a₂ a₃ a₄ : A} {p : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
            {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
            {c : C a b} {c₂ : C a₂ b₂}
            {q q' : a =[p] a₂}


--check λa, pathover (C a) (fc a) (h a) (gc a)

-- λa, pathover P (b a) (p a) (b' a)



-- pathover P b p b'
--set_option pp.notation false

  --in this version A' does not depend on A
  definition pathover_pathover_fl {a' a₂' : A'} {p : a' = a₂'} {a₂ : A} {f : A' → A}
    {b : Πa, B (f a)} {b₂ : B a₂} {q : Π(a' : A'), f a' = a₂} (r : pathover B (b a') (q a') b₂)
    (r₂ : pathover B (b a₂') (q a₂') b₂)
    (s : squareover B (naturality q p) r r₂ (pathover_ap B f (apdo b p)) (!ap_constant⁻¹ ▸ idpo))
    : r =[p] r₂ :=
  by cases p; esimp at s; apply pathover_idp_of_eq; apply eq_of_vdeg_squareover; exact s

--   definition pathover_pathover {ba ba' : Πa, B a} {pa : Πa, ba a = ba a}
--             {ca : Πa, C a (ba a)} {ca' : Πa, C a (ba' a)}
--             {qa : ba a =[pa a] ba' a} {qa₂ : ba a₂ =[pa a₂] ba' a₂}
--  (r : squareover _ _ _ _ _ _) : qa =[p] qa₂ :=
-- sorry

--   definition pathover_pathover_constant_FlFr {C : A → A' → Type} {ba ba' : A → A'} {pa : Πa, ba a = ba a}
--             {ca : Πa, C a (ba a)} {ca' : Πa, C a (ba' a)}
--             {qa : ba a =[pa a] ba' a} {qa₂ : ba a₂ =[pa a₂] ba' a₂}
--  (r : squareover (λa, C a _) _ _ _ _ _) : pathover _ qa p qa₂ := sorry

--   definition pathover_pathover_constant_l {C : A → A' → Type} {ba ba' : A → A'} {pa : Πa, ba a = ba a}
--             {ca : Πa, C a (ba a)} {ca' : Πa, C a (ba' a)}
--             {qa : ba a =[pa a] ba' a} {qa₂ : ba a₂ =[pa a₂] ba' a₂}
--  (r : squareover (λa, C a _) _ _ _ _ _) : qa =[p] qa₂ :=
-- begin
--   check_expr qa =[p] qa₂
-- end


end eq
