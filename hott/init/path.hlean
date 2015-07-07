/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

prelude
import .function .datatypes .relation .tactic

open function eq

/- Path equality -/

namespace eq
  variables {A B C : Type} {P : A → Type} {x y z t : A}

  --notation a = b := eq a b
  notation x = y `:>`:50 A:49 := @eq A x y
  definition idp [reducible] [constructor] {a : A} := refl a
  definition idpath [reducible] [constructor] (a : A) := refl a

  -- unbased path induction
  definition rec' [reducible] [unfold 6] {P : Π (a b : A), (a = b) → Type}
    (H : Π (a : A), P a a idp) {a b : A} (p : a = b) : P a b p :=
  eq.rec (H a) p

  definition rec_on' [reducible] [unfold 5] {P : Π (a b : A), (a = b) → Type}
    {a b : A} (p : a = b) (H : Π (a : A), P a a idp) : P a b p :=
  eq.rec (H a) p

  /- Concatenation and inverse -/

  definition concat [trans] [unfold 6] (p : x = y) (q : y = z) : x = z :=
  eq.rec (λp', p') q p

  definition inverse [symm] [unfold 4] (p : x = y) : y = x :=
  eq.rec (refl x) p

  infix   ⬝  := concat
  postfix ⁻¹ := inverse
  --a second notation for the inverse, which is not overloaded
  postfix [parsing-only] `⁻¹ᵖ`:std.prec.max_plus := inverse

  /- The 1-dimensional groupoid structure -/

  -- The identity path is a right unit.
  definition con_idp [unfold-full] (p : x = y) : p ⬝ idp = p :=
  idp

  -- The identity path is a right unit.
  definition idp_con [unfold 4] (p : x = y) : idp ⬝ p = p :=
  eq.rec_on p idp

  -- Concatenation is associative.
  definition con.assoc' (p : x = y) (q : y = z) (r : z = t) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  eq.rec_on r (eq.rec_on q idp)

  definition con.assoc (p : x = y) (q : y = z) (r : z = t) :
    (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
  eq.rec_on r (eq.rec_on q idp)

  -- The left inverse law.
  definition con.right_inv [unfold 4] (p : x = y) : p ⬝ p⁻¹ = idp :=
  eq.rec_on p idp

  -- The right inverse law.
  definition con.left_inv [unfold 4] (p : x = y) : p⁻¹ ⬝ p = idp :=
  eq.rec_on p idp

  /- Several auxiliary theorems about canceling inverses across associativity. These are somewhat
     redundant, following from earlier theorems. -/

  definition inv_con_cancel_left (p : x = y) (q : y = z) : p⁻¹ ⬝ (p ⬝ q) = q :=
  eq.rec_on q (eq.rec_on p idp)

  definition con_inv_cancel_left (p : x = y) (q : x = z) : p ⬝ (p⁻¹ ⬝ q) = q :=
  eq.rec_on q (eq.rec_on p idp)

  definition con_inv_cancel_right (p : x = y) (q : y = z) : (p ⬝ q) ⬝ q⁻¹ = p :=
  eq.rec_on q (eq.rec_on p idp)

  definition inv_con_cancel_right (p : x = z) (q : y = z) : (p ⬝ q⁻¹) ⬝ q = p :=
  eq.rec_on q (take p, eq.rec_on p idp) p

  -- Inverse distributes over concatenation
  definition con_inv (p : x = y) (q : y = z) : (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
  eq.rec_on q (eq.rec_on p idp)

  definition inv_con_inv_left (p : y = x) (q : y = z) : (p⁻¹ ⬝ q)⁻¹ = q⁻¹ ⬝ p :=
  eq.rec_on q (eq.rec_on p idp)

  -- universe metavariables
  definition inv_con_inv_right (p : x = y) (q : z = y) : (p ⬝ q⁻¹)⁻¹ = q ⬝ p⁻¹ :=
  eq.rec_on p (take q, eq.rec_on q idp) q

  definition inv_con_inv_inv (p : y = x) (q : z = y) : (p⁻¹ ⬝ q⁻¹)⁻¹ = q ⬝ p :=
  eq.rec_on p (eq.rec_on q idp)

  -- Inverse is an involution.
  definition inv_inv (p : x = y) : p⁻¹⁻¹ = p :=
  eq.rec_on p idp

  -- auxiliary definition used by 'cases' tactic
  definition elim_inv_inv {A : Type} {a b : A} {C : a = b → Type} (H₁ : a = b) (H₂ : C (H₁⁻¹⁻¹)) : C H₁ :=
  eq.rec_on (inv_inv H₁) H₂

  /- Theorems for moving things around in equations -/

  definition con_eq_of_eq_inv_con {p : x = z} {q : y = z} {r : y = x} :
    p = r⁻¹ ⬝ q → r ⬝ p = q :=
  eq.rec_on r (take p h, !idp_con ⬝ h ⬝ !idp_con) p

  definition con_eq_of_eq_con_inv [unfold 5] {p : x = z} {q : y = z} {r : y = x} :
    r = q ⬝ p⁻¹ → r ⬝ p = q :=
  eq.rec_on p (take q h, h) q

  definition inv_con_eq_of_eq_con {p : x = z} {q : y = z} {r : x = y} :
    p = r ⬝ q → r⁻¹ ⬝ p = q :=
  eq.rec_on r (take q h, !idp_con ⬝ h ⬝ !idp_con) q

  definition con_inv_eq_of_eq_con [unfold 5] {p : z = x} {q : y = z} {r : y = x} :
    r = q ⬝ p → r ⬝ p⁻¹ = q :=
  eq.rec_on p (take r h, h) r

  definition eq_con_of_inv_con_eq {p : x = z} {q : y = z} {r : y = x} :
    r⁻¹ ⬝ q = p → q = r ⬝ p :=
  eq.rec_on r (take p h, !idp_con⁻¹ ⬝ h ⬝ !idp_con⁻¹) p

  definition eq_con_of_con_inv_eq [unfold 5] {p : x = z} {q : y = z} {r : y = x} :
    q ⬝ p⁻¹ = r → q = r ⬝ p :=
  eq.rec_on p (take q h, h) q

  definition eq_inv_con_of_con_eq {p : x = z} {q : y = z} {r : x = y} :
    r ⬝ q = p → q = r⁻¹ ⬝ p :=
  eq.rec_on r (take q h, !idp_con⁻¹ ⬝ h ⬝ !idp_con⁻¹) q

  definition eq_con_inv_of_con_eq [unfold 5] {p : z = x} {q : y = z} {r : y = x} :
    q ⬝ p = r → q = r ⬝ p⁻¹ :=
  eq.rec_on p (take r h, h) r

  definition eq_of_con_inv_eq_idp [unfold 5] {p q : x = y} : p ⬝ q⁻¹ = idp → p = q :=
  eq.rec_on q (take p h, h) p

  definition eq_of_inv_con_eq_idp {p q : x = y} : q⁻¹ ⬝ p = idp → p = q :=
  eq.rec_on q (take p h, !idp_con⁻¹ ⬝ h) p

  definition eq_inv_of_con_eq_idp' [unfold 5] {p : x = y} {q : y = x} : p ⬝ q = idp → p = q⁻¹ :=
  eq.rec_on q (take p h, h) p

  definition eq_inv_of_con_eq_idp {p : x = y} {q : y = x} : q ⬝ p = idp → p = q⁻¹ :=
  eq.rec_on q (take p h, !idp_con⁻¹ ⬝ h) p

  definition eq_of_idp_eq_inv_con {p q : x = y} : idp = p⁻¹ ⬝ q → p = q :=
  eq.rec_on p (take q h, h ⬝ !idp_con) q

  definition eq_of_idp_eq_con_inv [unfold 4] {p q : x = y} : idp = q ⬝ p⁻¹ → p = q :=
  eq.rec_on p (take q h, h) q

  definition inv_eq_of_idp_eq_con [unfold 4] {p : x = y} {q : y = x} : idp = q ⬝ p → p⁻¹ = q :=
  eq.rec_on p (take q h, h) q

  definition inv_eq_of_idp_eq_con' {p : x = y} {q : y = x} : idp = p ⬝ q → p⁻¹ = q :=
  eq.rec_on p (take q h, h ⬝ !idp_con) q

  definition con_inv_eq_idp {p q : x = y} (r : p = q) : p ⬝ q⁻¹ = idp :=
  by cases r;apply con.right_inv

  definition inv_con_eq_idp {p q : x = y} (r : p = q) : q⁻¹ ⬝ p = idp :=
  by cases r;apply con.left_inv

  definition con_eq_idp {p : x = y} {q : y = x} (r : p = q⁻¹) : p ⬝ q = idp :=
  by cases q;exact r

  definition idp_eq_inv_con {p q : x = y} (r : p = q) : idp = p⁻¹ ⬝ q :=
  by cases r;exact !con.left_inv⁻¹

  definition idp_eq_con_inv {p q : x = y} (r : p = q) : idp = q ⬝ p⁻¹ :=
  by cases r;exact !con.right_inv⁻¹

  definition idp_eq_con {p : x = y} {q : y = x} (r : p⁻¹ = q) : idp = q ⬝ p :=
  by cases p;exact r

  /- Transport -/

  definition transport [subst] [reducible] [unfold 5] (P : A → Type) {x y : A} (p : x = y)
    (u : P x) : P y :=
  eq.rec_on p u

  -- This idiom makes the operation right associative.
  notation p `▸` x := transport _ p x

  definition cast [reducible] [unfold 3] {A B : Type} (p : A = B) (a : A) : B :=
  p ▸ a

  definition tr_rev [reducible] [unfold 6] (P : A → Type) {x y : A} (p : x = y) (u : P y) : P x :=
  p⁻¹ ▸ u

  definition ap [unfold 6] ⦃A B : Type⦄ (f : A → B) {x y:A} (p : x = y) : f x = f y :=
  eq.rec_on p idp

  abbreviation ap01 [parsing-only] := ap

  definition homotopy [reducible] (f g : Πx, P x) : Type :=
  Πx : A, f x = g x

  infix ~ := homotopy

  protected definition homotopy.refl [refl] [reducible] (f : Πx, P x) : f ~ f :=
  λ x, idp

  protected definition homotopy.symm [symm] [reducible] {f g : Πx, P x} (H : f ~ g) : g ~ f :=
  λ x, (H x)⁻¹

  protected definition homotopy.trans [trans] [reducible] {f g h : Πx, P x}
    (H1 : f ~ g) (H2 : g ~ h) : f ~ h :=
  λ x, H1 x ⬝ H2 x

  definition apd10 [unfold 5] {f g : Πx, P x} (H : f = g) : f ~ g :=
  λx, eq.rec_on H idp

  --the next theorem is useful if you want to write "apply (apd10' a)"
  definition apd10' [unfold 6] {f g : Πx, P x} (a : A) (H : f = g) : f a = g a :=
  eq.rec_on H idp

  definition ap10 [reducible] [unfold 5] {f g : A → B} (H : f = g) : f ~ g := apd10 H

  definition ap11 {f g : A → B} (H : f = g) {x y : A} (p : x = y) : f x = g y :=
  eq.rec_on H (eq.rec_on p idp)

  definition apd [unfold 6] (f : Πa, P a) {x y : A} (p : x = y) : p ▸ f x = f y :=
  eq.rec_on p idp

  /- More theorems for moving things around in equations -/

  definition tr_eq_of_eq_inv_tr {P : A → Type} {x y : A} {p : x = y} {u : P x} {v : P y} :
    u = p⁻¹ ▸ v → p ▸ u = v :=
  eq.rec_on p (take v, id) v

  definition inv_tr_eq_of_eq_tr {P : A → Type} {x y : A} {p : y = x} {u : P x} {v : P y} :
    u = p ▸ v → p⁻¹ ▸ u = v :=
  eq.rec_on p (take u, id) u

  definition eq_inv_tr_of_tr_eq {P : A → Type} {x y : A} {p : x = y} {u : P x} {v : P y} :
    p ▸ u = v → u = p⁻¹ ▸ v :=
  eq.rec_on p (take v, id) v

  definition eq_tr_of_inv_tr_eq {P : A → Type} {x y : A} {p : y = x} {u : P x} {v : P y} :
    p⁻¹ ▸ u = v → u = p ▸ v :=
  eq.rec_on p (take u, id) u

  /- Functoriality of functions -/

  -- Here we prove that functions behave like functors between groupoids, and that [ap] itself is
  -- functorial.

  -- Functions take identity paths to identity paths
  definition ap_idp (x : A) (f : A → B) : ap f idp = idp :> (f x = f x) := idp

  -- Functions commute with concatenation.
  definition ap_con (f : A → B) {x y z : A} (p : x = y) (q : y = z) :
    ap f (p ⬝ q) = ap f p ⬝ ap f q :=
  eq.rec_on q (eq.rec_on p idp)

  definition con_ap_con_eq_con_ap_con_ap (f : A → B) {w x y z : A} (r : f w = f x)
    (p : x = y) (q : y = z) : r ⬝ ap f (p ⬝ q) = (r ⬝ ap f p) ⬝ ap f q :=
  eq.rec_on q (take p, eq.rec_on p idp) p

  definition ap_con_con_eq_ap_con_ap_con (f : A → B) {w x y z : A} (p : x = y) (q : y = z)
    (r : f z = f w) : ap f (p ⬝ q) ⬝ r = ap f p ⬝ (ap f q ⬝ r) :=
  eq.rec_on q (eq.rec_on p (take r, con.assoc _ _ _)) r

  -- Functions commute with path inverses.
  definition ap_inv' (f : A → B) {x y : A} (p : x = y) : (ap f p)⁻¹ = ap f p⁻¹ :=
  eq.rec_on p idp

  definition ap_inv {A B : Type} (f : A → B) {x y : A} (p : x = y) : ap f p⁻¹ = (ap f p)⁻¹ :=
  eq.rec_on p idp

  -- [ap] itself is functorial in the first argument.

  definition ap_id (p : x = y) : ap id p = p :=
  eq.rec_on p idp

  definition ap_compose (g : B → C) (f : A → B) {x y : A} (p : x = y) :
    ap (g ∘ f) p = ap g (ap f p) :=
  eq.rec_on p idp

  -- Sometimes we don't have the actual function [compose].
  definition ap_compose' (g : B → C) (f : A → B) {x y : A} (p : x = y) :
    ap (λa, g (f a)) p = ap g (ap f p) :=
  eq.rec_on p idp

  -- The action of constant maps.
  definition ap_constant [unfold 5] (p : x = y) (z : B) : ap (λu, z) p = idp :=
  eq.rec_on p idp

  -- Naturality of [ap].
  definition ap_con_eq_con_ap {f g : A → B} (p : f ~ g) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x ⬝ ap g q :=
  eq.rec_on q !idp_con

  -- Naturality of [ap] at identity.
  definition ap_con_eq_con {f : A → A} (p : Πx, f x = x) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x ⬝ q :=
  eq.rec_on q !idp_con

  definition con_ap_eq_con {f : A → A} (p : Πx, x = f x) {x y : A} (q : x = y) :
    p x ⬝ ap f q =  q ⬝ p y :=
  eq.rec_on q !idp_con⁻¹

  -- Naturality of [ap] with constant function
  definition ap_con_eq {f : A → B} {b : B} (p : Πx, f x = b) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x :=
  eq.rec_on q !idp_con

  -- Naturality with other paths hanging around.

  definition con_ap_con_con_eq_con_con_ap_con {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {w z : B} (r : w = f x) (s : g y = z) :
    (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (ap g q ⬝ s) :=
  eq.rec_on s (eq.rec_on q idp)

  definition con_ap_con_eq_con_con_ap {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {w : B} (r : w = f x) :
    (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ ap g q :=
  eq.rec_on q idp

  -- TODO: try this using the simplifier, and compare proofs
  definition ap_con_con_eq_con_ap_con {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {z : B} (s : g y = z) :
    ap f q ⬝ (p y ⬝ s) = p x ⬝ (ap g q ⬝ s) :=
  eq.rec_on s (eq.rec_on q
    (calc
      (ap f idp) ⬝ (p x ⬝ idp) = idp ⬝ p x : idp
        ... = p x : !idp_con
        ... = (p x) ⬝ (ap g idp ⬝ idp) : idp))
  -- This also works:
  -- eq.rec_on s (eq.rec_on q (!idp_con ▸ idp))

  definition con_ap_con_con_eq_con_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {w z : A} (r : w = f x) (s : y = z) :
    (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (q ⬝ s) :=
  eq.rec_on s (eq.rec_on q idp)

  definition con_con_ap_con_eq_con_con_con {g : A → A} (p : id ~ g) {x y : A} (q : x = y)
      {w z : A} (r : w = x) (s : g y = z) :
    (r ⬝ p x) ⬝ (ap g q ⬝ s) = (r ⬝ q) ⬝ (p y ⬝ s) :=
  eq.rec_on s (eq.rec_on q idp)

  definition con_ap_con_eq_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {w : A} (r : w = f x) :
    (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ q :=
  eq.rec_on q idp

  definition ap_con_con_eq_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {z : A} (s : y = z) :
    ap f q ⬝ (p y ⬝ s) = p x ⬝ (q ⬝ s) :=
  eq.rec_on s (eq.rec_on q (!idp_con ▸ idp))

  definition con_con_ap_eq_con_con {g : A → A} (p : id ~ g) {x y : A} (q : x = y)
      {w : A} (r : w = x) :
    (r ⬝ p x) ⬝ ap g q = (r ⬝ q) ⬝ p y :=
  begin cases q, exact idp end

  definition con_ap_con_eq_con_con' {g : A → A} (p : id ~ g) {x y : A} (q : x = y)
      {z : A} (s : g y = z) :
    p x ⬝ (ap g q ⬝ s) = q ⬝ (p y ⬝ s) :=
  begin
    apply (eq.rec_on s),
    apply (eq.rec_on q),
    apply (idp_con (p x) ▸ idp)
  end

  /- Action of [apd10] and [ap10] on paths -/

  -- Application of paths between functions preserves the groupoid structure

  definition apd10_idp (f : Πx, P x) (x : A) : apd10 (refl f) x = idp := idp

  definition apd10_con {f f' f'' : Πx, P x} (h : f = f') (h' : f' = f'') (x : A) :
    apd10 (h ⬝ h') x = apd10 h x ⬝ apd10 h' x :=
  eq.rec_on h (take h', eq.rec_on h' idp) h'

  definition apd10_inv {f g : Πx : A, P x} (h : f = g) (x : A) :
    apd10 h⁻¹ x = (apd10 h x)⁻¹ :=
  eq.rec_on h idp

  definition ap10_idp {f : A → B} (x : A) : ap10 (refl f) x = idp := idp

  definition ap10_con {f f' f'' : A → B} (h : f = f') (h' : f' = f'') (x : A) :
  ap10 (h ⬝ h') x = ap10 h x ⬝ ap10 h' x := apd10_con h h' x

  definition ap10_inv {f g : A → B} (h : f = g) (x : A) : ap10 h⁻¹ x = (ap10 h x)⁻¹ :=
  apd10_inv h x

  -- [ap10] also behaves nicely on paths produced by [ap]
  definition ap_ap10 (f g : A → B) (h : B → C) (p : f = g) (a : A) :
    ap h (ap10 p a) = ap10 (ap (λ f', h ∘ f') p) a:=
  eq.rec_on p idp


  /- Transport and the groupoid structure of paths -/

  definition idp_tr {P : A → Type} {x : A} (u : P x) : idp ▸ u = u := idp

  definition con_tr {P : A → Type} {x y z : A} (p : x = y) (q : y = z) (u : P x) :
    p ⬝ q ▸ u = q ▸ p ▸ u :=
  eq.rec_on q (eq.rec_on p idp)

  definition tr_inv_tr {P : A → Type} {x y : A} (p : x = y) (z : P y) :
    p ▸ p⁻¹ ▸ z = z :=
  (con_tr p⁻¹ p z)⁻¹ ⬝ ap (λr, transport P r z) (con.left_inv p)

  definition inv_tr_tr {P : A → Type} {x y : A} (p : x = y) (z : P x) :
    p⁻¹ ▸ p ▸ z = z :=
  (con_tr p p⁻¹ z)⁻¹ ⬝ ap (λr, transport P r z) (con.right_inv p)

  definition con_tr_lemma {P : A → Type}
      {x y z w : A} (p : x = y) (q : y = z) (r : z = w) (u : P x) :
    ap (λe, e ▸ u) (con.assoc' p q r) ⬝ (con_tr (p ⬝ q) r u) ⬝
        ap (transport P r) (con_tr p q u)
      = (con_tr p (q ⬝ r) u) ⬝ (con_tr q r (p ▸ u))
      :> ((p ⬝ (q ⬝ r)) ▸ u = r ▸ q ▸ p ▸ u) :=
  eq.rec_on r (eq.rec_on q (eq.rec_on p idp))

  --  Here is another coherence lemma for transport.
  definition tr_inv_tr_lemma {P : A → Type} {x y : A} (p : x = y) (z : P x) :
    tr_inv_tr p (transport P p z) = ap (transport P p) (inv_tr_tr p z) :=
  eq.rec_on p idp

  /- some properties for apd -/

  definition apd_idp (x : A) (f : Πx, P x) : apd f idp = idp :> (f x = f x) := idp
  definition apd_con (f : Πx, P x) {x y z : A} (p : x = y) (q : y = z)
    : apd f (p ⬝ q) = con_tr p q (f x) ⬝ ap (transport P q) (apd f p) ⬝ apd f q :=
  by cases p;cases q;apply idp
  definition apd_inv (f : Πx, P x) {x y : A} (p : x = y)
    : apd f p⁻¹ = (eq_inv_tr_of_tr_eq (apd f p))⁻¹ :=
  by cases p;apply idp


  -- Dependent transport in a doubly dependent type.
  definition transportD [unfold 6] {P : A → Type} (Q : Πa, P a → Type)
      {a a' : A} (p : a = a') (b : P a) (z : Q a b) : Q a' (p ▸ b) :=
  eq.rec_on p z

  -- In Coq the variables P, Q and b are explicit, but in Lean we can probably have them implicit
  -- using the following notation
  notation p `▸D`:65 x:64 := transportD _ p _ x

  -- Transporting along higher-dimensional paths
  definition transport2 [unfold 7] (P : A → Type) {x y : A} {p q : x = y} (r : p = q) (z : P x) :
    p ▸ z = q ▸ z :=
  ap (λp', p' ▸ z) r

  notation p `▸2`:65 x:64 := transport2 _ p _ x

  -- An alternative definition.
  definition tr2_eq_ap10 (Q : A → Type) {x y : A} {p q : x = y} (r : p = q)
      (z : Q x) :
    transport2 Q r z = ap10 (ap (transport Q) r) z :=
  eq.rec_on r idp

  definition tr2_con {P : A → Type} {x y : A} {p1 p2 p3 : x = y}
      (r1 : p1 = p2) (r2 : p2 = p3) (z : P x) :
    transport2 P (r1 ⬝ r2) z = transport2 P r1 z ⬝ transport2 P r2 z :=
  eq.rec_on r1 (eq.rec_on r2 idp)

  definition tr2_inv (Q : A → Type) {x y : A} {p q : x = y} (r : p = q) (z : Q x) :
    transport2 Q r⁻¹ z = (transport2 Q r z)⁻¹ :=
  eq.rec_on r idp

  definition transportD2 [unfold 7] (B C : A → Type) (D : Π(a:A), B a → C a → Type)
    {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z) : D x2 (p ▸ y) (p ▸ z) :=
  eq.rec_on p w

  notation p `▸D2`:65 x:64 := transportD2 _ _ _ p _ _ x

  definition ap_tr_con_tr2 (P : A → Type) {x y : A} {p q : x = y} {z w : P x} (r : p = q)
      (s : z = w) :
    ap (transport P p) s  ⬝  transport2 P r w = transport2 P r z  ⬝  ap (transport P q) s :=
  eq.rec_on r !idp_con⁻¹


  definition fn_tr_eq_tr_fn {P Q : A → Type} {x y : A} (p : x = y) (f : Πx, P x → Q x) (z : P x) :
    f y (p ▸ z) = (p ▸ (f x z)) :=
  eq.rec_on p idp

  /- Transporting in particular fibrations -/

  /-
  From the Coq HoTT library:

  One frequently needs lemmas showing that transport in a certain dependent type is equal to some
  more explicitly defined operation, defined according to the structure of that dependent type.
  For most dependent types, we prove these lemmas in the appropriate file in the types/
  subdirectory.  Here we consider only the most basic cases.
  -/

  -- Transporting in a constant fibration.
  definition tr_constant (p : x = y) (z : B) : transport (λx, B) p z = z :=
  eq.rec_on p idp

  definition tr2_constant {p q : x = y} (r : p = q) (z : B) :
    tr_constant p z = transport2 (λu, B) r z ⬝ tr_constant q z :=
  eq.rec_on r !idp_con⁻¹

  -- Transporting in a pulled back fibration.
  -- rename: tr_compose
  definition transport_compose (P : B → Type) (f : A → B) (p : x = y) (z : P (f x)) :
    transport (P ∘ f) p z  =  transport P (ap f p) z :=
  eq.rec_on p idp

  definition ap_precompose (f : A → B) (g g' : B → C) (p : g = g') :
    ap (λh, h ∘ f) p = transport (λh : B → C, g ∘ f = h ∘ f) p idp :=
  eq.rec_on p idp

  definition apd10_ap_precompose (f : A → B) (g g' : B → C) (p : g = g') (a : A) :
    apd10 (ap (λh : B → C, h ∘ f) p) a = apd10 p (f a) :=
  eq.rec_on p idp

  definition apd10_ap_postcompose (f : B → C) (g g' : A → B) (p : g = g') (a : A) :
    apd10 (ap (λh : A → B, f ∘ h) p) a = ap f (apd10 p a) :=
  eq.rec_on p idp

  -- A special case of [transport_compose] which seems to come up a lot.
  definition tr_eq_cast_ap {P : A → Type} {x y} (p : x = y) (u : P x) : p ▸ u = cast (ap P p) u :=
  eq.rec_on p idp

  definition tr_eq_cast_ap_fn {P : A → Type} {x y} (p : x = y) : transport P p = cast (ap P p) :=
  eq.rec_on p idp

  /- The behavior of [ap] and [apd] -/

  -- In a constant fibration, [apd] reduces to [ap], modulo [transport_const].
  definition apd_eq_tr_constant_con_ap (f : A → B) (p : x = y) :
    apd f p = tr_constant p (f x) ⬝ ap f p :=
  eq.rec_on p idp


  /- The 2-dimensional groupoid structure -/

  -- Horizontal composition of 2-dimensional paths.
  definition concat2 {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
    : p ⬝ q = p' ⬝ q' :=
  eq.rec_on h (eq.rec_on h' idp)

  -- 2-dimensional path inversion
  definition inverse2 [unfold 6] {p q : x = y} (h : p = q) : p⁻¹ = q⁻¹ :=
  eq.rec_on h idp

  infixl `◾`:75 := concat2
  postfix [parsing-only] `⁻²`:(max+10) := inverse2 --this notation is abusive, should we use it?

  /- Whiskering -/

  definition whisker_left (p : x = y) {q r : y = z} (h : q = r) : p ⬝ q = p ⬝ r :=
  idp ◾ h

  definition whisker_right {p q : x = y} (h : p = q) (r : y = z) : p ⬝ r = q ⬝ r :=
  h ◾ idp

  -- Unwhiskering, a.k.a. cancelling

  definition cancel_left {x y z : A} {p : x = y} {q r : y = z} : (p ⬝ q = p ⬝ r) → (q = r) :=
  λs, !inv_con_cancel_left⁻¹ ⬝ whisker_left p⁻¹ s ⬝ !inv_con_cancel_left

  definition cancel_right {x y z : A} {p q : x = y} {r : y = z} : (p ⬝ r = q ⬝ r) → (p = q) :=
  λs, !con_inv_cancel_right⁻¹ ⬝ whisker_right s r⁻¹ ⬝ !con_inv_cancel_right

  -- Whiskering and identity paths.

  definition whisker_right_idp_right {p q : x = y} (h : p = q) :
    whisker_right h idp = h :=
  eq.rec_on h (eq.rec_on p idp)

  definition whisker_right_idp_left (p : x = y) (q : y = z) :
    whisker_right idp q = idp :> (p ⬝ q = p ⬝ q) :=
  eq.rec_on q idp

  definition whisker_left_idp_right (p : x = y) (q : y = z) :
    whisker_left p idp = idp :> (p ⬝ q = p ⬝ q) :=
  eq.rec_on q idp

  definition whisker_left_idp_left {p q : x = y} (h : p = q) :
    (idp_con p) ⁻¹ ⬝ whisker_left idp h ⬝ idp_con q = h :=
  eq.rec_on h (eq.rec_on p idp)

  definition con2_idp {p q : x = y} (h : p = q) :
    h ◾ idp = whisker_right h idp :> (p ⬝ idp = q ⬝ idp) :=
  idp

  definition idp_con2 {p q : x = y} (h : p = q) :
    idp ◾ h = whisker_left idp h :> (idp ⬝ p = idp ⬝ q) :=
  idp

  -- The interchange law for concatenation.
  definition con2_con_con2 {p p' p'' : x = y} {q q' q'' : y = z}
      (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
    (a ◾ c) ⬝ (b ◾ d) = (a ⬝ b) ◾ (c ⬝ d) :=
  eq.rec_on d (eq.rec_on c (eq.rec_on b (eq.rec_on a idp)))

  definition whisker_right_con_whisker_left {x y z : A} {p p' : x = y} {q q' : y = z}
    (a : p = p') (b : q = q') :
    (whisker_right a q) ⬝ (whisker_left p' b) = (whisker_left p b) ⬝ (whisker_right a q') :=
  eq.rec_on b (eq.rec_on a !idp_con⁻¹)

  -- Structure corresponding to the coherence equations of a bicategory.

  -- The "pentagonator": the 3-cell witnessing the associativity pentagon.
  definition pentagon {v w x y z : A} (p : v = w) (q : w = x) (r : x = y) (s : y = z) :
    whisker_left p (con.assoc' q r s)
      ⬝ con.assoc' p (q ⬝ r) s
      ⬝ whisker_right (con.assoc' p q r) s
    = con.assoc' p q (r ⬝ s) ⬝ con.assoc' (p ⬝ q) r s :=
  by induction s;induction r;induction q;induction p;reflexivity

  -- The 3-cell witnessing the left unit triangle.
  definition triangulator (p : x = y) (q : y = z) :
    con.assoc' p idp q ⬝ whisker_right (con_idp p) q = whisker_left p (idp_con q) :=
  eq.rec_on q (eq.rec_on p idp)

  definition eckmann_hilton {x:A} (p q : idp = idp :> x = x) : p ⬝ q = q ⬝ p :=
    (!whisker_right_idp_right ◾ !whisker_left_idp_left)⁻¹
    ⬝ whisker_left _ !idp_con
    ⬝ !whisker_right_con_whisker_left
    ⬝ whisker_right !idp_con⁻¹ _
    ⬝ (!whisker_left_idp_left ◾ !whisker_right_idp_right)

  -- The action of functions on 2-dimensional paths
  definition ap02 [unfold 8] [reducible] (f : A → B) {x y : A} {p q : x = y} (r : p = q)
    : ap f p = ap f q :=
  ap (ap f) r

  definition ap02_con (f : A → B) {x y : A} {p p' p'' : x = y} (r : p = p') (r' : p' = p'') :
    ap02 f (r ⬝ r') = ap02 f r ⬝ ap02 f r' :=
  eq.rec_on r (eq.rec_on r' idp)

  definition ap02_con2 (f : A → B) {x y z : A} {p p' : x = y} {q q' :y = z} (r : p = p')
    (s : q = q') :
      ap02 f (r ◾ s) = ap_con f p q
                        ⬝ (ap02 f r  ◾  ap02 f s)
                        ⬝ (ap_con f p' q')⁻¹ :=
  eq.rec_on r (eq.rec_on s (eq.rec_on q (eq.rec_on p idp)))

  definition apd02 [unfold 8] {p q : x = y} (f : Π x, P x) (r : p = q) :
    apd f p = transport2 P r (f x) ⬝ apd f q :=
  eq.rec_on r !idp_con⁻¹

  -- And now for a lemma whose statement is much longer than its proof.
  definition apd02_con {P : A → Type} (f : Π x:A, P x) {x y : A}
      {p1 p2 p3 : x = y} (r1 : p1 = p2) (r2 : p2 = p3) :
    apd02 f (r1 ⬝ r2) = apd02 f r1
      ⬝ whisker_left (transport2 P r1 (f x)) (apd02 f r2)
      ⬝ con.assoc' _ _ _
      ⬝ (whisker_right (tr2_con r1 r2 (f x))⁻¹ (apd f p3)) :=
  eq.rec_on r2 (eq.rec_on r1 (eq.rec_on p1 idp))

end eq
