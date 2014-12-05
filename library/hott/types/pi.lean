/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about pi-types (dependent function spaces)
-/

import ..trunc ..axioms.funext
open path equiv is_equiv funext

namespace pi
  universe variables l k
  variables [H : funext.{l k}] {A : Type.{l}} {B : A → Type.{k}} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {f g h : Πa, B a}
  include H
  /- Paths -/

  /- Paths [p : f ≈ g] in a function type [Πx:X, P x] are equivalent to functions taking values in path types, [H : Πx:X, f x ≈ g x], or concisely, [H : f == g].

  This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in axioms.funext and path:  -/

  /- Now we show how these things compute. -/

  definition equiv_apD10 : (f ≈ g) ≃ (f ∼ g) :=
  equiv.mk _ !funext.ap

  open truncation
  definition trunc_pi [instance] (B : A → Type.{k}) (n : trunc_index)
      [H : Πa, is_trunc n (B a)] : is_trunc n (Πa, B a) :=
  begin
    reverts (B, H),
    apply (truncation.trunc_index.rec_on n),
      intros (B, H),
        fapply is_contr.mk,
          intro a, apply center, apply H, --remove "apply H" when term synthesis works correctly
          intro f, apply path_forall,
            intro x, apply (contr (f x)),
      intros (n, IH, B, H),
        fapply is_trunc_succ, intros (f, g),
          fapply trunc_equiv',
            apply equiv.symm, apply equiv_apD10,
            apply IH,
              intro a,
              show is_trunc n (f a ≈ g a), from
              succ_is_trunc n (f a) (g a)
  end

  definition trunc_path_pi [instance] (n : trunc_index) (f g : Πa, B a)
      [H : ∀a, is_trunc n (f a ≈ g a)] : is_trunc n (f ≈ g) :=
  begin
    apply trunc_equiv', apply equiv.symm,
    apply equiv_apD10,
    apply trunc_pi, exact H,
  end

end pi
