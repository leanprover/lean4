/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

import arity .eq .bool .unit .sigma .nat.basic prop_trunc
open is_trunc eq prod sigma nat equiv option is_equiv bool unit algebra sigma.ops

structure pointed [class] (A : Type) :=
  (point : A)

structure pType :=
  (carrier : Type)
  (Point   : carrier)

notation `Type*` := pType

section
  universe variable u
  structure ptrunctype (n : trunc_index) extends trunctype.{u} n, pType.{u}
end

notation n `-Type*` := ptrunctype n
abbreviation pSet  [parsing_only] := 0-Type*
notation `Set*` := pSet

namespace pointed
  attribute pType.carrier [coercion]
  variables {A B : Type}

  definition pt [unfold 2] [H : pointed A] := point A
  definition Point [unfold 1] (A : Type*) := pType.Point A
  abbreviation carrier [unfold 1] (A : Type*) := pType.carrier A
  protected definition Mk [constructor] {A : Type} (a : A) := pType.mk A a
  protected definition MK [constructor] (A : Type) (a : A) := pType.mk A a
  protected definition mk' [constructor] (A : Type) [H : pointed A] : Type* :=
  pType.mk A (point A)
  definition pointed_carrier [instance] [constructor] (A : Type*) : pointed A :=
  pointed.mk (Point A)

  -- Any contractible type is pointed
  definition pointed_of_is_contr [instance] [priority 800] [constructor]
    (A : Type) [H : is_contr A] : pointed A :=
  pointed.mk !center

  -- A pi type with a pointed target is pointed
  definition pointed_pi [instance] [constructor] (P : A → Type) [H : Πx, pointed (P x)]
      : pointed (Πx, P x) :=
  pointed.mk (λx, pt)

  -- A sigma type of pointed components is pointed
  definition pointed_sigma [instance] [constructor] (P : A → Type) [G : pointed A]
      [H : pointed (P pt)] : pointed (Σx, P x) :=
  pointed.mk ⟨pt,pt⟩

  definition pointed_prod [instance] [constructor] (A B : Type) [H1 : pointed A] [H2 : pointed B]
      : pointed (A × B) :=
  pointed.mk (pt,pt)

  definition pointed_loop [instance] [constructor] (a : A) : pointed (a = a) :=
  pointed.mk idp

  definition pointed_bool [instance] [constructor] : pointed bool :=
  pointed.mk ff

  definition pprod [constructor] (A B : Type*) : Type* :=
  pointed.mk' (A × B)

  infixr ` ×* `:35 := pprod

  definition pointed_fun_closed [constructor] (f : A → B) [H : pointed A] : pointed B :=
  pointed.mk (f pt)

  definition ploop_space [reducible] [constructor] (A : Type*) : Type* :=
  pointed.mk' (point A = point A)

  definition iterated_ploop_space [reducible] : ℕ → Type* → Type*
  | iterated_ploop_space  0    X := X
  | iterated_ploop_space (n+1) X := ploop_space (iterated_ploop_space n X)

  prefix `Ω`:(max+5) := ploop_space
  notation `Ω[`:95 n:0 `] `:0 A:95 := iterated_ploop_space n A

  definition iterated_ploop_space_zero [unfold_full] (A : Type*)
    : Ω[0] A = A := rfl

  definition iterated_ploop_space_succ [unfold_full] (k : ℕ) (A : Type*)
    : Ω[succ k] A = Ω Ω[k] A := rfl

  definition rfln  [constructor] [reducible] {A : Type*} {n : ℕ} : Ω[n] A := pt
  definition refln [constructor] [reducible] (A : Type*) (n : ℕ) : Ω[n] A := pt
  definition refln_eq_refl (A : Type*) (n : ℕ) : rfln = rfl :> Ω[succ n] A := rfl

  definition iterated_loop_space [unfold 3] (A : Type) [H : pointed A] (n : ℕ) : Type :=
  Ω[n] (pointed.mk' A)

  definition pType_eq {A B : Type*} (f : A ≃ B) (p : f pt = pt) : A = B :=
  begin
    cases A with A a, cases B with B b, esimp at *,
    fapply apd011 @pType.mk,
    { apply ua f},
    { rewrite [cast_ua,p]},
  end

  definition pType_eq_elim {A B : Type*} (p : A = B :> Type*)
    : Σ(p : carrier A = carrier B :> Type), cast p pt = pt :=
  by induction p; exact ⟨idp, idp⟩

  protected definition pType.sigma_char.{u} : pType.{u} ≃ Σ(X : Type.{u}), X :=
  begin
    fapply equiv.MK,
    { intro x, induction x with X x, exact ⟨X, x⟩},
    { intro x, induction x with X x, exact pointed.MK X x},
    { intro x, induction x with X x, reflexivity},
    { intro x, induction x with X x, reflexivity},
  end

  definition add_point [constructor] (A : Type) : Type* :=
  pointed.Mk (none : option A)
  postfix `₊`:(max+1) := add_point
  -- the inclusion A → A₊ is called "some", the extra point "pt" or "none" ("@none A")

end pointed open pointed

protected definition ptrunctype.mk' [constructor] (n : trunc_index)
  (A : Type) [pointed A] [is_trunc n A] : n-Type* :=
ptrunctype.mk A _ pt

protected definition pSet.mk [constructor] := @ptrunctype.mk (-1.+1)
protected definition pSet.mk' [constructor] := ptrunctype.mk' (-1.+1)

definition ptrunctype_of_trunctype [constructor] {n : trunc_index} (A : n-Type) (a : A) : n-Type* :=
ptrunctype.mk A _ a

definition ptrunctype_of_pType [constructor] {n : trunc_index} (A : Type*) (H : is_trunc n A)
  : n-Type* :=
ptrunctype.mk A _ pt

definition pSet_of_Set [constructor] (A : Set) (a : A) : Set* :=
ptrunctype.mk A _ a

definition pSet_of_pType [constructor] (A : Type*) (H : is_set A) : Set* :=
ptrunctype.mk A _ pt

attribute pType._trans_to_carrier ptrunctype.to_pType ptrunctype.to_trunctype [unfold 2]

definition ptrunctype_eq {n : trunc_index} {A B : n-Type*} (p : A = B :> Type) (q : cast p pt = pt)
  : A = B :=
begin
  induction A with A HA a, induction B with B HB b, esimp at *,
  induction p, induction q,
  esimp,
  refine ap010 (ptrunctype.mk A) _ a,
  exact !is_prop.elim
end

definition ptrunctype_eq_of_pType_eq {n : trunc_index} {A B : n-Type*} (p : A = B :> Type*)
  : A = B :=
begin
  cases pType_eq_elim p with q r,
  exact ptrunctype_eq q r
end


namespace pointed

  definition pbool [constructor] : Set* :=
  pSet.mk' bool

  definition punit [constructor] : Set* :=
  pSet.mk' unit

  /- properties of iterated loop space -/
  variable (A : Type*)
  definition loop_space_succ_eq_in (n : ℕ) : Ω[succ n] A = Ω[n] (Ω A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap ploop_space IH}
  end

  definition loop_space_add (n m : ℕ) : Ω[n] (Ω[m] A) = Ω[m+n] (A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap ploop_space IH}
  end

  definition loop_space_succ_eq_out (n : ℕ) : Ω[succ n] A = Ω(Ω[n] A)  :=
  idp

  variable {A}

  /- the equality [loop_space_succ_eq_in] preserves concatenation -/
  theorem loop_space_succ_eq_in_concat {n : ℕ} (p q : Ω[succ (succ n)] A) :
           transport carrier (ap ploop_space (loop_space_succ_eq_in A n)) (p ⬝ q)
         = transport carrier (ap ploop_space (loop_space_succ_eq_in A n)) p
         ⬝ transport carrier (ap ploop_space (loop_space_succ_eq_in A n)) q :=
  begin
    rewrite [-+tr_compose, ↑function.compose],
    rewrite [+@transport_eq_FlFr_D _ _ _ _ Point Point, +con.assoc], apply whisker_left,
    rewrite [-+con.assoc], apply whisker_right, rewrite [con_inv_cancel_right, ▸*, -ap_con]
  end

  definition loop_space_loop_irrel (p : point A = point A) : Ω(pointed.Mk p) = Ω[2] A :=
  begin
    intros, fapply pType_eq,
    { esimp, transitivity _,
      apply eq_equiv_fn_eq_of_equiv (equiv_eq_closed_right _ p⁻¹),
      esimp, apply eq_equiv_eq_closed, apply con.right_inv, apply con.right_inv},
    { esimp, apply con.left_inv}
  end

  definition iterated_loop_space_loop_irrel (n : ℕ) (p : point A = point A)
    : Ω[succ n](pointed.Mk p) = Ω[succ (succ n)] A :> pType :=
  calc
    Ω[succ n](pointed.Mk p) = Ω[n](Ω (pointed.Mk p)) : loop_space_succ_eq_in
      ... = Ω[n] (Ω[2] A)                            : loop_space_loop_irrel
      ... = Ω[2+n] A                                 : loop_space_add
      ... = Ω[n+2] A                                 : by rewrite [algebra.add.comm]

end pointed open pointed

/- pointed maps -/
structure pmap (A B : Type*) :=
  (to_fun : A → B)
  (resp_pt : to_fun (Point A) = Point B)

namespace pointed
  abbreviation respect_pt [unfold 3] := @pmap.resp_pt
  notation `map₊` := pmap
  infix ` →* `:30 := pmap
  attribute pmap.to_fun [coercion]
end pointed open pointed

/- pointed homotopies -/
structure phomotopy {A B : Type*} (f g : A →* B) :=
  (homotopy : f ~ g)
  (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

namespace pointed
  variables {A B C D : Type*} {f g h : A →* B}

  infix ` ~* `:50 := phomotopy
  abbreviation to_homotopy_pt [unfold 5] := @phomotopy.homotopy_pt
  abbreviation to_homotopy [coercion] [unfold 5] (p : f ~* g) : Πa, f a = g a :=
  phomotopy.homotopy p

  /- categorical properties of pointed maps -/

  definition pid [constructor] [refl] (A : Type*) : A →* A :=
  pmap.mk id idp

  definition pcompose [constructor] [trans] (g : B →* C) (f : A →* B) : A →* C :=
  pmap.mk (λa, g (f a)) (ap g (respect_pt f) ⬝ respect_pt g)

  infixr ` ∘* `:60 := pcompose

  definition passoc (h : C →* D) (g : B →* C) (f : A →* B) : (h ∘* g) ∘* f ~* h ∘* (g ∘* f) :=
  begin
    fconstructor, intro a, reflexivity,
    cases A, cases B, cases C, cases D, cases f with f pf, cases g with g pg, cases h with h ph,
    esimp at *,
    induction pf, induction pg, induction ph, reflexivity
  end

  definition pid_comp (f : A →* B) : pid B ∘* f ~* f :=
  begin
    fconstructor,
    { intro a, reflexivity},
    { reflexivity}
  end

  definition comp_pid (f : A →* B) : f ∘* pid A ~* f :=
  begin
    fconstructor,
    { intro a, reflexivity},
    { reflexivity}
  end

  /- equivalences and equalities -/

  definition pmap_eq (r : Πa, f a = g a) (s : respect_pt f = (r pt) ⬝ respect_pt g) : f = g :=
  begin
    cases f with f p, cases g with g q,
    esimp at *,
    fapply apo011 pmap.mk,
    { exact eq_of_homotopy r},
    { apply concato_eq, apply pathover_eq_Fl, apply inv_con_eq_of_eq_con,
      rewrite [ap_eq_ap10,↑ap10,apd10_eq_of_homotopy,s]}
  end

  definition pmap_equiv_left (A : Type) (B : Type*) : A₊ →* B ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro f a, cases f with f p, exact f (some a)},
    { intro f, fconstructor,
        intro a, cases a, exact pt, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro f, cases f with f p, esimp, fapply pmap_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end

  definition pmap_equiv_right (A : Type*) (B : Type)
    : (Σ(b : B), A →* (pointed.Mk b)) ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro u a, exact pmap.to_fun u.2 a},
    { intro f, refine ⟨f pt, _⟩, fapply pmap.mk,
        intro a, esimp, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro u, cases u with b f, cases f with f p, esimp at *, induction p,
      reflexivity}
  end

  definition pmap_bool_equiv (B : Type*) : (pbool →* B) ≃ B :=
  begin
    fapply equiv.MK,
    { intro f, cases f with f p, exact f tt},
    { intro b, fconstructor,
        intro u, cases u, exact pt, exact b,
        reflexivity},
    { intro b, reflexivity},
    { intro f, cases f with f p, esimp, fapply pmap_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end

  -- The constant pointed map between any two types
  definition pconst [constructor] (A B : Type*) : A →* B :=
  pmap.mk (λ a, Point B) idp

  -- the pointed type of pointed maps
  definition ppmap [constructor] (A B : Type*) : Type* :=
  pType.mk (A →* B) (pconst A B)

  /- instances of pointed maps -/

  definition ap1 [constructor] (f : A →* B) : Ω A →* Ω B :=
  begin
    fconstructor,
    { intro p, exact !respect_pt⁻¹ ⬝ ap f p ⬝ !respect_pt},
    { esimp, apply con.left_inv}
  end

  definition apn (n : ℕ) (f : map₊ A B) : Ω[n] A →* Ω[n] B :=
  begin
  induction n with n IH,
  { exact f},
  { esimp [iterated_ploop_space], exact ap1 IH}
  end

  prefix `Ω→`:(max+5) := ap1
  notation `Ω→[`:95 n:0 `] `:0 f:95 := apn n f

  definition apn_zero (f : map₊ A B) : Ω→[0] f = f := idp
  definition apn_succ (n : ℕ) (f : map₊ A B) : Ω→[n + 1] f = ap1 (Ω→[n] f) := idp

  definition pcast [constructor] {A B : Type*} (p : A = B) : A →* B :=
  proof pmap.mk (cast (ap pType.carrier p)) (by induction p; reflexivity) qed

  definition pinverse [constructor] {X : Type*} : Ω X →* Ω X :=
  pmap.mk eq.inverse idp

  /- categorical properties of pointed homotopies -/

  protected definition phomotopy.refl [constructor] [refl] (f : A →* B) : f ~* f :=
  begin
    fconstructor,
    { intro a, exact idp},
    { apply idp_con}
  end

  protected definition phomotopy.rfl [constructor] {A B : Type*} {f : A →* B} : f ~* f :=
  phomotopy.refl f

  protected definition phomotopy.trans [constructor] [trans] (p : f ~* g) (q : g ~* h)
    : f ~* h :=
  phomotopy.mk (λa, p a ⬝ q a)
    abstract begin
      induction f, induction g, induction p with p p', induction q with q q', esimp at *,
      induction p', induction q', esimp, apply con.assoc
    end end

  protected definition phomotopy.symm [constructor] [symm] (p : f ~* g) : g ~* f :=
  phomotopy.mk (λa, (p a)⁻¹)
    abstract begin
      induction f, induction p with p p', esimp at *,
      induction p', esimp, apply inv_con_cancel_left
    end end

  infix ` ⬝* `:75 := phomotopy.trans
  postfix `⁻¹*`:(max+1) := phomotopy.symm

  /- properties about the given pointed maps -/

  definition is_equiv_ap1 {A B : Type*} (f : A →* B) [is_equiv f] : is_equiv (ap1 f) :=
  begin
    induction B with B b, induction f with f pf, esimp at *, cases pf, esimp,
    apply is_equiv.homotopy_closed (ap f),
    intro p, exact !idp_con⁻¹
  end

  definition is_equiv_apn {A B : Type*} (n : ℕ) (f : A →* B) [H : is_equiv f]
    : is_equiv (apn n f) :=
  begin
    induction n with n IH,
    { exact H},
    { exact is_equiv_ap1 (apn n f)}
  end

  definition ap1_id [constructor] {A : Type*} : ap1 (pid A) ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, esimp, refine !idp_con ⬝ !ap_id},
    { reflexivity}
  end

  definition ap1_pinverse {A : Type*} : ap1 (@pinverse A) ~* @pinverse (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, esimp, refine !idp_con ⬝ _, exact !inverse_eq_inverse2⁻¹ },
    { reflexivity}
  end

  definition ap1_compose (g : B →* C) (f : A →* B) : ap1 (g ∘* f) ~* ap1 g ∘* ap1 f :=
  begin
    induction B, induction C, induction g with g pg, induction f with f pf, esimp at *,
    induction pg, induction pf,
    fconstructor,
    { intro p, esimp, apply whisker_left, exact ap_compose g f p ⬝ ap (ap g) !idp_con⁻¹},
    { reflexivity}
  end

  definition ap1_compose_pinverse (f : A →* B) : ap1 f ∘* pinverse ~* pinverse ∘* ap1 f :=
  begin
    fconstructor,
    { intro p, esimp, refine !con.assoc ⬝ _ ⬝ !con_inv⁻¹, apply whisker_left,
      refine whisker_right !ap_inv _ ⬝ _ ⬝ !con_inv⁻¹, apply whisker_left,
      exact !inv_inv⁻¹},
    { induction B with B b, induction f with f pf, esimp at *, induction pf, reflexivity},
  end

  theorem ap1_con (f : A →* B) (p q : Ω A) : ap1 f (p ⬝ q) = ap1 f p ⬝ ap1 f q :=
  begin
    rewrite [▸*,ap_con, +con.assoc, con_inv_cancel_left], repeat apply whisker_left
  end

  theorem ap1_inv (f : A →* B) (p : Ω A) : ap1 f p⁻¹ = (ap1 f p)⁻¹ :=
  begin
    rewrite [▸*,ap_inv, +con_inv, inv_inv, +con.assoc], repeat apply whisker_left
  end

  definition pcast_ap_loop_space {A B : Type*} (p : A = B)
    : pcast (ap ploop_space p) ~* Ω→ (pcast p) :=
  begin
    induction p, exact !ap1_id⁻¹*
  end

  definition pinverse_con [constructor] {X : Type*} (p q : Ω X)
    : pinverse (p ⬝ q) = pinverse q ⬝ pinverse p :=
  !con_inv

  definition pinverse_inv [constructor] {X : Type*} (p : Ω X)
    : pinverse p⁻¹ = (pinverse p)⁻¹ :=
  idp

  /- more on pointed homotopies -/

  definition phomotopy_of_eq [constructor] {A B : Type*} {f g : A →* B} (p : f = g) : f ~* g :=
  phomotopy.mk (ap010 pmap.to_fun p) begin induction p, apply idp_con end

  definition pconcat_eq [constructor] {A B : Type*} {f g h : A →* B} (p : f ~* g) (q : g = h)
    : f ~* h :=
  p ⬝* phomotopy_of_eq q

  definition eq_pconcat [constructor] {A B : Type*} {f g h : A →* B} (p : f = g) (q : g ~* h)
    : f ~* h :=
  phomotopy_of_eq p ⬝* q

  definition pwhisker_left [constructor] (h : B →* C) (p : f ~* g) : h ∘* f ~* h ∘* g :=
  phomotopy.mk (λa, ap h (p a))
    abstract begin
      induction A, induction B, induction C,
      induction f with f pf, induction g with g pg, induction h with h ph,
      induction p with p p', esimp at *, induction ph, induction pg, induction p', reflexivity
    end end

  definition pwhisker_right [constructor] (h : C →* A) (p : f ~* g) : f ∘* h ~* g ∘* h :=
  phomotopy.mk (λa, p (h a))
    abstract begin
      induction A, induction B, induction C,
      induction f with f pf, induction g with g pg, induction h with h ph,
      induction p with p p', esimp at *, induction ph, induction pg, induction p', esimp,
      exact !idp_con⁻¹
    end end

  definition pconcat2 [constructor] {A B C : Type*} {h i : B →* C} {f g : A →* B}
    (q : h ~* i) (p : f ~* g) : h ∘* f ~* i ∘* g :=
  pwhisker_left _ p ⬝* pwhisker_right _ q

  definition eq_of_phomotopy (p : f ~* g) : f = g :=
  begin
    fapply pmap_eq,
    { intro a, exact p a},
    { exact !to_homotopy_pt⁻¹}
  end

  definition pap {A B C D : Type*} (F : (A →* B) → (C →* D))
    {f g : A →* B} (p : f ~* g) : F f ~* F g :=
  phomotopy.mk (ap010 F (eq_of_phomotopy p)) begin cases eq_of_phomotopy p, apply idp_con end

  -- TODO: give proof without using function extensionality (commented out part is a start)
  definition ap1_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g)
    : ap1 f ~* ap1 g :=
  pap ap1 p
  /- begin
    induction p with p q, induction f with f pf, induction g with g pg, induction B with B b,
    esimp at *, induction q, induction pg,
    fapply phomotopy.mk,
    { intro l, esimp, refine _ ⬝ !idp_con⁻¹, refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
      apply ap_con_eq_con_ap},
    { esimp, }
  end -/

  definition apn_compose (n : ℕ) (g : B →* C) (f : A →* B) : apn n (g ∘* f) ~* apn n g ∘* apn n f :=
  begin
    induction n with n IH,
    { reflexivity},
    { refine ap1_phomotopy IH ⬝* _, apply ap1_compose}
  end

  theorem apn_con (n : ℕ) (f : A →* B) (p q : Ω[n+1] A)
    : apn (n+1) f (p ⬝ q) = apn (n+1) f p ⬝ apn (n+1) f q :=
  by rewrite [+apn_succ, ap1_con]

  theorem apn_inv (n : ℕ)  (f : A →* B) (p : Ω[n+1] A) : apn (n+1) f p⁻¹ = (apn (n+1) f p)⁻¹ :=
  by rewrite [+apn_succ, ap1_inv]

  infix ` ⬝*p `:75 := pconcat_eq
  infix ` ⬝p* `:75 := eq_pconcat

end pointed
