/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about W-types (well-founded trees)
-/

import .sigma .pi
open eq equiv is_equiv sigma sigma.ops

inductive Wtype.{l k} {A : Type.{l}} (B : A → Type.{k}) : Type.{max l k} :=
sup : Π (a : A), (B a → Wtype.{l k} B) → Wtype.{l k} B

namespace Wtype
  notation `W` binders `,` r:(scoped B, Wtype B) := r

  universe variables u v
  variables {A A' : Type.{u}} {B B' : A → Type.{v}} {C : Π(a : A), B a → Type}
            {a a' : A} {f : B a → W a, B a} {f' : B a' → W a, B a} {w w' : W(a : A), B a}

  protected definition pr1 [unfold 3] (w : W(a : A), B a) : A :=
  by cases w with a f; exact a

  protected definition pr2 [unfold 3] (w : W(a : A), B a) : B (Wtype.pr1 w) → W(a : A), B a :=
  by cases w with a f; exact f

  namespace ops
  postfix `.1`:(max+1) := Wtype.pr1
  postfix `.2`:(max+1) := Wtype.pr2
  notation `⟨` a `,` f `⟩`:0 := Wtype.sup a f --input ⟨ ⟩ as \< \>
  end ops
  open ops

  protected definition eta (w : W a, B a) : ⟨w.1 , w.2⟩ = w :=
  by cases w; exact idp

  definition sup_eq_sup (p : a = a') (q : f =[p] f') : ⟨a, f⟩ = ⟨a', f'⟩ :=
  by cases q; exact idp

  definition Wtype_eq (p : w.1 = w'.1) (q : w.2 =[p] w'.2) : w = w' :=
  by cases w; cases w';exact (sup_eq_sup p q)

  definition Wtype_eq_pr1 (p : w = w') : w.1 = w'.1 :=
  by cases p;exact idp

  definition Wtype_eq_pr2 (p : w = w') : w.2 =[Wtype_eq_pr1 p] w'.2 :=
  by cases p;exact idpo

  namespace ops
  postfix `..1`:(max+1) := Wtype_eq_pr1
  postfix `..2`:(max+1) := Wtype_eq_pr2
  end ops open ops open sigma

  definition sup_path_W (p : w.1 = w'.1) (q : w.2 =[p] w'.2)
    : ⟨(Wtype_eq p q)..1, (Wtype_eq p q)..2⟩ = ⟨p, q⟩ :=
  by cases w; cases w'; cases q; exact idp

  definition pr1_path_W (p : w.1 = w'.1) (q : w.2 =[p] w'.2) : (Wtype_eq p q)..1 = p :=
  !sup_path_W..1

  definition pr2_path_W (p : w.1 = w'.1) (q : w.2 =[p] w'.2)
      : (Wtype_eq p q)..2 =[pr1_path_W p q] q :=
  !sup_path_W..2

  definition eta_path_W (p : w = w') : Wtype_eq (p..1) (p..2) = p :=
  by cases p; cases w; exact idp

  definition transport_pr1_path_W {B' : A → Type} (p : w.1 = w'.1) (q : w.2 =[p] w'.2)
      : transport (λx, B' x.1) (Wtype_eq p q) = transport B' p :=
  by cases w; cases w'; cases q; exact idp

  definition path_W_uncurried (pq : Σ(p : w.1 = w'.1), w.2 =[p] w'.2) : w = w' :=
  by cases pq with p q; exact (Wtype_eq p q)

  definition sup_path_W_uncurried (pq : Σ(p : w.1 = w'.1), w.2 =[p] w'.2)
      :  ⟨(path_W_uncurried pq)..1, (path_W_uncurried pq)..2⟩ = pq :=
  by cases pq with p q; exact (sup_path_W p q)

  definition pr1_path_W_uncurried (pq : Σ(p : w.1 = w'.1), w.2 =[p] w'.2)
      : (path_W_uncurried pq)..1 = pq.1 :=
  !sup_path_W_uncurried..1

  definition pr2_path_W_uncurried (pq : Σ(p : w.1 = w'.1), w.2 =[p] w'.2)
      : (path_W_uncurried pq)..2 =[pr1_path_W_uncurried pq] pq.2 :=
  !sup_path_W_uncurried..2

  definition eta_path_W_uncurried (p : w = w') : path_W_uncurried ⟨p..1, p..2⟩ = p :=
  !eta_path_W

  definition transport_pr1_path_W_uncurried {B' : A → Type} (pq : Σ(p : w.1 = w'.1), w.2 =[p] w'.2)
      : transport (λx, B' x.1) (@path_W_uncurried A B w w' pq) = transport B' pq.1 :=
  by cases pq with p q; exact (transport_pr1_path_W p q)

  definition isequiv_path_W /-[instance]-/ (w w' : W a, B a)
      : is_equiv (path_W_uncurried : (Σ(p : w.1 = w'.1), w.2 =[p] w'.2) → w = w') :=
  adjointify path_W_uncurried
             (λp, ⟨p..1, p..2⟩)
             eta_path_W_uncurried
             sup_path_W_uncurried

  definition equiv_path_W (w w' : W a, B a) : (Σ(p : w.1 = w'.1), w.2 =[p] w'.2) ≃ (w = w') :=
  equiv.mk path_W_uncurried !isequiv_path_W

  definition double_induction_on {P : (W a, B a) → (W a, B a) → Type} (w w' : W a, B a)
    (H : ∀ (a a' : A) (f : B a → W a, B a) (f' : B a' → W a, B a),
      (∀ (b : B a) (b' : B a'), P (f b) (f' b')) → P (sup a f) (sup a' f')) : P w w' :=
  begin
    revert w',
    induction w with a f IH,
    intro w',
    cases w' with a' f',
    apply H, intro b b',
    apply IH
  end

  /- truncatedness -/
  open is_trunc pi
  definition trunc_W [instance] (n : trunc_index)
    [HA : is_trunc (n.+1) A] : is_trunc (n.+1) (W a, B a) :=
  begin
  fapply is_trunc_succ_intro, intro w w',
  eapply (double_induction_on w w'), intro a a' f f' IH,
  fapply is_trunc_equiv_closed,
  { apply equiv_path_W},
  { apply is_trunc_sigma,
    intro p, cases p, esimp, apply is_trunc_equiv_closed_rev,
      apply pathover_idp}
  end

end Wtype
