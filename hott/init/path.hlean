/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

prelude
import .function .tactic

open function eq

/- Path equality -/

namespace eq
  variables {A B C : Type} {P : A → Type} {a a' x y z t : A} {b b' : B}

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
  by induction q; exact p

  definition inverse [symm] [unfold 4] (p : x = y) : y = x :=
  by induction p; reflexivity

  infix   ⬝  := concat
  postfix ⁻¹ := inverse
  --a second notation for the inverse, which is not overloaded
  postfix [parsing_only] `⁻¹ᵖ`:std.prec.max_plus := inverse

  /- The 1-dimensional groupoid structure -/

  -- The identity path is a right unit.
  definition con_idp [unfold_full] (p : x = y) : p ⬝ idp = p :=
  idp

  -- The identity path is a right unit.
  definition idp_con [unfold 4] (p : x = y) : idp ⬝ p = p :=
  by induction p; reflexivity

  -- Concatenation is associative.
  definition con.assoc' (p : x = y) (q : y = z) (r : z = t) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  by induction r; induction q; reflexivity

  definition con.assoc (p : x = y) (q : y = z) (r : z = t) :
    (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
  by induction r; induction q; reflexivity

  -- The left inverse law.
  definition con.right_inv [unfold 4] (p : x = y) : p ⬝ p⁻¹ = idp :=
  by induction p; reflexivity

  -- The right inverse law.
  definition con.left_inv [unfold 4] (p : x = y) : p⁻¹ ⬝ p = idp :=
  by induction p; reflexivity

  /- Several auxiliary theorems about canceling inverses across associativity. These are somewhat
     redundant, following from earlier theorems. -/

  definition inv_con_cancel_left (p : x = y) (q : y = z) : p⁻¹ ⬝ (p ⬝ q) = q :=
  by induction q; induction p; reflexivity

  definition con_inv_cancel_left (p : x = y) (q : x = z) : p ⬝ (p⁻¹ ⬝ q) = q :=
  by induction q; induction p; reflexivity

  definition con_inv_cancel_right (p : x = y) (q : y = z) : (p ⬝ q) ⬝ q⁻¹ = p :=
  by induction q; induction p; reflexivity

  definition inv_con_cancel_right (p : x = z) (q : y = z) : (p ⬝ q⁻¹) ⬝ q = p :=
  by induction q; induction p; reflexivity

  -- Inverse distributes over concatenation
  definition con_inv (p : x = y) (q : y = z) : (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
  by induction q; induction p; reflexivity

  definition inv_con_inv_left (p : y = x) (q : y = z) : (p⁻¹ ⬝ q)⁻¹ = q⁻¹ ⬝ p :=
  by induction q; induction p; reflexivity

  -- universe metavariables
  definition inv_con_inv_right (p : x = y) (q : z = y) : (p ⬝ q⁻¹)⁻¹ = q ⬝ p⁻¹ :=
  by induction q; induction p; reflexivity

  definition inv_con_inv_inv (p : y = x) (q : z = y) : (p⁻¹ ⬝ q⁻¹)⁻¹ = q ⬝ p :=
  by induction q; induction p; reflexivity

  -- Inverse is an involution.
  definition inv_inv (p : x = y) : p⁻¹⁻¹ = p :=
  by induction p; reflexivity

  -- auxiliary definition used by 'cases' tactic
  definition elim_inv_inv {A : Type} {a b : A} {C : a = b → Type} (H₁ : a = b) (H₂ : C (H₁⁻¹⁻¹)) : C H₁ :=
  eq.rec_on (inv_inv H₁) H₂

  /- Theorems for moving things around in equations -/

  definition con_eq_of_eq_inv_con {p : x = z} {q : y = z} {r : y = x} :
    p = r⁻¹ ⬝ q → r ⬝ p = q :=
  begin
    induction r, intro h, exact !idp_con ⬝ h ⬝ !idp_con
  end

  definition con_eq_of_eq_con_inv [unfold 5] {p : x = z} {q : y = z} {r : y = x} :
    r = q ⬝ p⁻¹ → r ⬝ p = q :=
  by induction p; exact id

  definition inv_con_eq_of_eq_con {p : x = z} {q : y = z} {r : x = y} :
    p = r ⬝ q → r⁻¹ ⬝ p = q :=
  by induction r; intro h; exact !idp_con ⬝ h ⬝ !idp_con

  definition con_inv_eq_of_eq_con [unfold 5] {p : z = x} {q : y = z} {r : y = x} :
    r = q ⬝ p → r ⬝ p⁻¹ = q :=
  by induction p; exact id

  definition eq_con_of_inv_con_eq {p : x = z} {q : y = z} {r : y = x} :
    r⁻¹ ⬝ q = p → q = r ⬝ p :=
  by induction r; intro h; exact !idp_con⁻¹ ⬝ h ⬝ !idp_con⁻¹

  definition eq_con_of_con_inv_eq [unfold 5] {p : x = z} {q : y = z} {r : y = x} :
    q ⬝ p⁻¹ = r → q = r ⬝ p :=
  by induction p; exact id

  definition eq_inv_con_of_con_eq {p : x = z} {q : y = z} {r : x = y} :
    r ⬝ q = p → q = r⁻¹ ⬝ p :=
  by induction r; intro h; exact !idp_con⁻¹ ⬝ h ⬝ !idp_con⁻¹

  definition eq_con_inv_of_con_eq [unfold 5] {p : z = x} {q : y = z} {r : y = x} :
    q ⬝ p = r → q = r ⬝ p⁻¹ :=
  by induction p; exact id

  definition eq_of_con_inv_eq_idp [unfold 5] {p q : x = y} : p ⬝ q⁻¹ = idp → p = q :=
  by induction q; exact id

  definition eq_of_inv_con_eq_idp {p q : x = y} : q⁻¹ ⬝ p = idp → p = q :=
  by induction q; intro h; exact !idp_con⁻¹ ⬝ h

  definition eq_inv_of_con_eq_idp' [unfold 5] {p : x = y} {q : y = x} : p ⬝ q = idp → p = q⁻¹ :=
  by induction q; exact id

  definition eq_inv_of_con_eq_idp {p : x = y} {q : y = x} : q ⬝ p = idp → p = q⁻¹ :=
  by induction q; intro h; exact !idp_con⁻¹ ⬝ h

  definition eq_of_idp_eq_inv_con {p q : x = y} : idp = p⁻¹ ⬝ q → p = q :=
  by induction p; intro h; exact h ⬝ !idp_con

  definition eq_of_idp_eq_con_inv [unfold 4] {p q : x = y} : idp = q ⬝ p⁻¹ → p = q :=
  by induction p; exact id

  definition inv_eq_of_idp_eq_con [unfold 4] {p : x = y} {q : y = x} : idp = q ⬝ p → p⁻¹ = q :=
  by induction p; exact id

  definition inv_eq_of_idp_eq_con' {p : x = y} {q : y = x} : idp = p ⬝ q → p⁻¹ = q :=
  by induction p; intro h; exact h ⬝ !idp_con

  definition con_inv_eq_idp [unfold 6] {p q : x = y} (r : p = q) : p ⬝ q⁻¹ = idp :=
  by cases r;apply con.right_inv

  definition inv_con_eq_idp [unfold 6] {p q : x = y} (r : p = q) : q⁻¹ ⬝ p = idp :=
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
  by induction p; exact u

  -- This idiom makes the operation right associative.
  infixr ` ▸ ` := transport _

  definition cast [reducible] [unfold 3] {A B : Type} (p : A = B) (a : A) : B :=
  p ▸ a

  definition cast_def [reducible] [unfold_full] {A B : Type} (p : A = B) (a : A)
    : cast p a = p ▸ a :=
  idp

  definition tr_rev [reducible] [unfold 6] (P : A → Type) {x y : A} (p : x = y) (u : P y) : P x :=
  p⁻¹ ▸ u

  definition ap [unfold 6] ⦃A B : Type⦄ (f : A → B) {x y:A} (p : x = y) : f x = f y :=
  by induction p; reflexivity

  abbreviation ap01 [parsing_only] := ap

  definition homotopy [reducible] (f g : Πx, P x) : Type :=
  Πx : A, f x = g x

  infix ~ := homotopy

  protected definition homotopy.refl [refl] [reducible] [unfold_full] (f : Πx, P x) : f ~ f :=
  λ x, idp

  protected definition homotopy.symm [symm] [reducible] [unfold_full] {f g : Πx, P x} (H : f ~ g)
    : g ~ f :=
  λ x, (H x)⁻¹

  protected definition homotopy.trans [trans] [reducible] [unfold_full] {f g h : Πx, P x}
    (H1 : f ~ g) (H2 : g ~ h) : f ~ h :=
  λ x, H1 x ⬝ H2 x

  definition homotopy_of_eq {f g : Πx, P x} (H1 : f = g) : f ~ g :=
  H1 ▸ homotopy.refl f

  definition apd10 [unfold 5] {f g : Πx, P x} (H : f = g) : f ~ g :=
  λx, by induction H; reflexivity

  --the next theorem is useful if you want to write "apply (apd10' a)"
  definition apd10' [unfold 6] {f g : Πx, P x} (a : A) (H : f = g) : f a = g a :=
  by induction H; reflexivity

  --apd10 is also ap evaluation
  definition apd10_eq_ap_eval {f g : Πx, P x} (H : f = g) (a : A)
    : apd10 H a = ap (λs : Πx, P x, s a) H :=
  by induction H; reflexivity

  definition ap10 [reducible] [unfold 5] {f g : A → B} (H : f = g) : f ~ g := apd10 H

  definition ap11 {f g : A → B} (H : f = g) {x y : A} (p : x = y) : f x = g y :=
  by induction H; exact ap f p

  definition apd [unfold 6] (f : Πa, P a) {x y : A} (p : x = y) : p ▸ f x = f y :=
  by induction p; reflexivity

  definition ap011 (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
  by cases Ha; exact ap (f a) Hb

  /- More theorems for moving things around in equations -/

  definition tr_eq_of_eq_inv_tr {P : A → Type} {x y : A} {p : x = y} {u : P x} {v : P y} :
    u = p⁻¹ ▸ v → p ▸ u = v :=
  by induction p; exact id

  definition inv_tr_eq_of_eq_tr {P : A → Type} {x y : A} {p : y = x} {u : P x} {v : P y} :
    u = p ▸ v → p⁻¹ ▸ u = v :=
  by induction p; exact id

  definition eq_inv_tr_of_tr_eq {P : A → Type} {x y : A} {p : x = y} {u : P x} {v : P y} :
    p ▸ u = v → u = p⁻¹ ▸ v :=
  by induction p; exact id

  definition eq_tr_of_inv_tr_eq {P : A → Type} {x y : A} {p : y = x} {u : P x} {v : P y} :
    p⁻¹ ▸ u = v → u = p ▸ v :=
  by induction p; exact id

  /- Functoriality of functions -/

  -- Here we prove that functions behave like functors between groupoids, and that [ap] itself is
  -- functorial.

  -- Functions take identity paths to identity paths
  definition ap_idp [unfold_full] (x : A) (f : A → B) : ap f idp = idp :> (f x = f x) := idp

  -- Functions commute with concatenation.
  definition ap_con [unfold 8] (f : A → B) {x y z : A} (p : x = y) (q : y = z) :
    ap f (p ⬝ q) = ap f p ⬝ ap f q :=
  by induction q; reflexivity

  definition con_ap_con_eq_con_ap_con_ap (f : A → B) {w x y z : A} (r : f w = f x)
    (p : x = y) (q : y = z) : r ⬝ ap f (p ⬝ q) = (r ⬝ ap f p) ⬝ ap f q :=
  by induction q; induction p; reflexivity

  definition ap_con_con_eq_ap_con_ap_con (f : A → B) {w x y z : A} (p : x = y) (q : y = z)
    (r : f z = f w) : ap f (p ⬝ q) ⬝ r = ap f p ⬝ (ap f q ⬝ r) :=
  by induction q; induction p; apply con.assoc

  -- Functions commute with path inverses.
  definition ap_inv' [unfold 6] (f : A → B) {x y : A} (p : x = y) : (ap f p)⁻¹ = ap f p⁻¹ :=
  by induction p; reflexivity

  definition ap_inv [unfold 6] (f : A → B) {x y : A} (p : x = y) : ap f p⁻¹ = (ap f p)⁻¹ :=
  by induction p; reflexivity

  -- [ap] itself is functorial in the first argument.

  definition ap_id [unfold 4] (p : x = y) : ap id p = p :=
  by induction p; reflexivity

  definition ap_compose [unfold 8] (g : B → C) (f : A → B) {x y : A} (p : x = y) :
    ap (g ∘ f) p = ap g (ap f p) :=
  by induction p; reflexivity

  -- Sometimes we don't have the actual function [compose].
  definition ap_compose' [unfold 8] (g : B → C) (f : A → B) {x y : A} (p : x = y) :
    ap (λa, g (f a)) p = ap g (ap f p) :=
  by induction p; reflexivity

  -- The action of constant maps.
  definition ap_constant [unfold 5] (p : x = y) (z : B) : ap (λu, z) p = idp :=
  by induction p; reflexivity

  -- Naturality of [ap].
  -- see also natural_square in cubical.square
  definition ap_con_eq_con_ap {f g : A → B} (p : f ~ g) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x ⬝ ap g q :=
  by induction q; apply idp_con

  -- Naturality of [ap] at identity.
  definition ap_con_eq_con {f : A → A} (p : Πx, f x = x) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x ⬝ q :=
  by induction q; apply idp_con

  definition con_ap_eq_con {f : A → A} (p : Πx, x = f x) {x y : A} (q : x = y) :
    p x ⬝ ap f q =  q ⬝ p y :=
  by induction q; exact !idp_con⁻¹

  -- Naturality of [ap] with constant function
  definition ap_con_eq {f : A → B} {b : B} (p : Πx, f x = b) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x :=
  by induction q; apply idp_con

  -- Naturality with other paths hanging around.

  definition con_ap_con_con_eq_con_con_ap_con {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {w z : B} (r : w = f x) (s : g y = z) :
    (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (ap g q ⬝ s) :=
  by induction s; induction q; reflexivity

  definition con_ap_con_eq_con_con_ap {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {w : B} (r : w = f x) :
    (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ ap g q :=
  by induction q; reflexivity

  -- TODO: try this using the simplifier, and compare proofs
  definition ap_con_con_eq_con_ap_con {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {z : B} (s : g y = z) :
    ap f q ⬝ (p y ⬝ s) = p x ⬝ (ap g q ⬝ s) :=
  begin
    induction s,
    induction q,
    apply idp_con
  end

  definition con_ap_con_con_eq_con_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {w z : A} (r : w = f x) (s : y = z) :
    (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (q ⬝ s) :=
  by induction s; induction q; reflexivity

  definition con_con_ap_con_eq_con_con_con {g : A → A} (p : id ~ g) {x y : A} (q : x = y)
      {w z : A} (r : w = x) (s : g y = z) :
    (r ⬝ p x) ⬝ (ap g q ⬝ s) = (r ⬝ q) ⬝ (p y ⬝ s) :=
  by induction s; induction q; reflexivity

  definition con_ap_con_eq_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {w : A} (r : w = f x) :
    (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ q :=
  by induction q; reflexivity

  definition ap_con_con_eq_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {z : A} (s : y = z) :
    ap f q ⬝ (p y ⬝ s) = p x ⬝ (q ⬝ s) :=
  by induction s; induction q; apply idp_con

  definition con_con_ap_eq_con_con {g : A → A} (p : id ~ g) {x y : A} (q : x = y)
      {w : A} (r : w = x) :
    (r ⬝ p x) ⬝ ap g q = (r ⬝ q) ⬝ p y :=
  begin cases q, exact idp end

  definition con_ap_con_eq_con_con' {g : A → A} (p : id ~ g) {x y : A} (q : x = y)
      {z : A} (s : g y = z) :
    p x ⬝ (ap g q ⬝ s) = q ⬝ (p y ⬝ s) :=
  by induction s; induction q; exact !idp_con⁻¹

  /- Action of [apd10] and [ap10] on paths -/

  -- Application of paths between functions preserves the groupoid structure

  definition apd10_idp (f : Πx, P x) (x : A) : apd10 (refl f) x = idp := idp

  definition apd10_con {f f' f'' : Πx, P x} (h : f = f') (h' : f' = f'') (x : A) :
    apd10 (h ⬝ h') x = apd10 h x ⬝ apd10 h' x :=
  by induction h; induction h'; reflexivity

  definition apd10_inv {f g : Πx : A, P x} (h : f = g) (x : A) :
    apd10 h⁻¹ x = (apd10 h x)⁻¹ :=
  by induction h; reflexivity

  definition ap10_idp {f : A → B} (x : A) : ap10 (refl f) x = idp := idp

  definition ap10_con {f f' f'' : A → B} (h : f = f') (h' : f' = f'') (x : A) :
  ap10 (h ⬝ h') x = ap10 h x ⬝ ap10 h' x := apd10_con h h' x

  definition ap10_inv {f g : A → B} (h : f = g) (x : A) : ap10 h⁻¹ x = (ap10 h x)⁻¹ :=
  apd10_inv h x

  -- [ap10] also behaves nicely on paths produced by [ap]
  definition ap_ap10 (f g : A → B) (h : B → C) (p : f = g) (a : A) :
    ap h (ap10 p a) = ap10 (ap (λ f', h ∘ f') p) a:=
  by induction p; reflexivity


  /- Transport and the groupoid structure of paths -/

  definition idp_tr {P : A → Type} {x : A} (u : P x) : idp ▸ u = u := idp

  definition con_tr [unfold 7] {P : A → Type} {x y z : A} (p : x = y) (q : y = z) (u : P x) :
    p ⬝ q ▸ u = q ▸ p ▸ u :=
  by induction q; reflexivity

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
  by induction r; induction q; induction p; reflexivity

  --  Here is another coherence lemma for transport.
  definition tr_inv_tr_lemma {P : A → Type} {x y : A} (p : x = y) (z : P x) :
    tr_inv_tr p (transport P p z) = ap (transport P p) (inv_tr_tr p z) :=
  by induction p; reflexivity

  /- some properties for apd -/

  definition apd_idp (x : A) (f : Πx, P x) : apd f idp = idp :> (f x = f x) := idp

  definition apd_con (f : Πx, P x) {x y z : A} (p : x = y) (q : y = z)
    : apd f (p ⬝ q) = con_tr p q (f x) ⬝ ap (transport P q) (apd f p) ⬝ apd f q :=
  by cases p; cases q; apply idp

  definition apd_inv (f : Πx, P x) {x y : A} (p : x = y)
    : apd f p⁻¹ = (eq_inv_tr_of_tr_eq (apd f p))⁻¹ :=
  by cases p; apply idp


  -- Dependent transport in a doubly dependent type.
  definition transportD [unfold 6] {P : A → Type} (Q : Πa, P a → Type)
      {a a' : A} (p : a = a') (b : P a) (z : Q a b) : Q a' (p ▸ b) :=
  by induction p; exact z

  -- In Coq the variables P, Q and b are explicit, but in Lean we can probably have them implicit
  -- using the following notation
  notation p ` ▸D `:65 x:64 := transportD _ p _ x

  -- Transporting along higher-dimensional paths
  definition transport2 [unfold 7] (P : A → Type) {x y : A} {p q : x = y} (r : p = q) (z : P x) :
    p ▸ z = q ▸ z :=
  ap (λp', p' ▸ z) r

  notation p ` ▸2 `:65 x:64 := transport2 _ p _ x

  -- An alternative definition.
  definition tr2_eq_ap10 (Q : A → Type) {x y : A} {p q : x = y} (r : p = q) (z : Q x) :
    transport2 Q r z = ap10 (ap (transport Q) r) z :=
  by induction r; reflexivity

  definition tr2_con {P : A → Type} {x y : A} {p1 p2 p3 : x = y}
      (r1 : p1 = p2) (r2 : p2 = p3) (z : P x) :
    transport2 P (r1 ⬝ r2) z = transport2 P r1 z ⬝ transport2 P r2 z :=
  by induction r1; induction r2; reflexivity

  definition tr2_inv (Q : A → Type) {x y : A} {p q : x = y} (r : p = q) (z : Q x) :
    transport2 Q r⁻¹ z = (transport2 Q r z)⁻¹ :=
  by induction r; reflexivity

  definition transportD2 [unfold 7] {B C : A → Type} (D : Π(a:A), B a → C a → Type)
    {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z) : D x2 (p ▸ y) (p ▸ z) :=
  by induction p; exact w

  notation p ` ▸D2 `:65 x:64 := transportD2 _ p _ _ x

  definition ap_tr_con_tr2 (P : A → Type) {x y : A} {p q : x = y} {z w : P x} (r : p = q)
      (s : z = w) :
    ap (transport P p) s  ⬝  transport2 P r w = transport2 P r z  ⬝  ap (transport P q) s :=
  by induction r; exact !idp_con⁻¹

  definition fn_tr_eq_tr_fn {P Q : A → Type} {x y : A} (p : x = y) (f : Πx, P x → Q x) (z : P x) :
    f y (p ▸ z) = (p ▸ (f x z)) :=
  by induction p; reflexivity

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
  by induction p; reflexivity

  definition tr2_constant {p q : x = y} (r : p = q) (z : B) :
    tr_constant p z = transport2 (λu, B) r z ⬝ tr_constant q z :=
  by induction r; exact !idp_con⁻¹

  -- Transporting in a pulled back fibration.
  definition tr_compose (P : B → Type) (f : A → B) (p : x = y) (z : P (f x)) :
    transport (P ∘ f) p z  =  transport P (ap f p) z :=
  by induction p; reflexivity

  definition ap_precompose (f : A → B) (g g' : B → C) (p : g = g') :
    ap (λh, h ∘ f) p = transport (λh : B → C, g ∘ f = h ∘ f) p idp :=
  by induction p; reflexivity

  definition apd10_ap_precompose (f : A → B) (g g' : B → C) (p : g = g') :
    apd10 (ap (λh : B → C, h ∘ f) p) = λa, apd10 p (f a) :=
  by induction p; reflexivity

  definition apd10_ap_precompose_dependent {C : B → Type}
    (f : A → B) {g g' : Πb : B, C b} (p : g = g')
    : apd10 (ap (λ(h : (Πb : B, C b))(a : A), h (f a)) p) = λa, apd10 p (f a) :=
  by induction p; reflexivity

  definition apd10_ap_postcompose (f : B → C) (g g' : A → B) (p : g = g') :
    apd10 (ap (λh : A → B, f ∘ h) p) = λa, ap f (apd10 p a) :=
  by induction p; reflexivity

  -- A special case of [tr_compose] which seems to come up a lot.
  definition tr_eq_cast_ap {P : A → Type} {x y} (p : x = y) (u : P x) : p ▸ u = cast (ap P p) u :=
  by induction p; reflexivity

  definition tr_eq_cast_ap_fn {P : A → Type} {x y} (p : x = y) : transport P p = cast (ap P p) :=
  by induction p; reflexivity

  /- The behavior of [ap] and [apd] -/

  -- In a constant fibration, [apd] reduces to [ap], modulo [transport_const].
  definition apd_eq_tr_constant_con_ap (f : A → B) (p : x = y) :
    apd f p = tr_constant p (f x) ⬝ ap f p :=
  by induction p; reflexivity


  /- The 2-dimensional groupoid structure -/

  -- Horizontal composition of 2-dimensional paths.
  definition concat2 [unfold 9 10] {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
    : p ⬝ q = p' ⬝ q' :=
  ap011 concat h h'

  -- 2-dimensional path inversion
  definition inverse2 [unfold 6] {p q : x = y} (h : p = q) : p⁻¹ = q⁻¹ :=
  ap inverse h

  infixl ` ◾ `:75 := concat2
  postfix [parsing_only] `⁻²`:(max+10) := inverse2 --this notation is abusive, should we use it?

  /- Whiskering -/

  definition whisker_left [unfold 8] (p : x = y) {q r : y = z} (h : q = r) : p ⬝ q = p ⬝ r :=
  idp ◾ h

  definition whisker_right [unfold 7] {p q : x = y} (h : p = q) (r : y = z) : p ⬝ r = q ⬝ r :=
  h ◾ idp

  -- Unwhiskering, a.k.a. cancelling

  definition cancel_left {x y z : A} (p : x = y) {q r : y = z} : (p ⬝ q = p ⬝ r) → (q = r) :=
  λs, !inv_con_cancel_left⁻¹ ⬝ whisker_left p⁻¹ s ⬝ !inv_con_cancel_left

  definition cancel_right {x y z : A} {p q : x = y} (r : y = z) : (p ⬝ r = q ⬝ r) → (p = q) :=
  λs, !con_inv_cancel_right⁻¹ ⬝ whisker_right s r⁻¹ ⬝ !con_inv_cancel_right

  -- Whiskering and identity paths.

  definition whisker_right_idp {p q : x = y} (h : p = q) :
    whisker_right h idp = h :=
  by induction h; induction p; reflexivity

  definition whisker_right_idp_left [unfold_full] (p : x = y) (q : y = z) :
    whisker_right idp q = idp :> (p ⬝ q = p ⬝ q) :=
  idp

  definition whisker_left_idp_right [unfold_full] (p : x = y) (q : y = z) :
    whisker_left p idp = idp :> (p ⬝ q = p ⬝ q) :=
  idp

  definition whisker_left_idp {p q : x = y} (h : p = q) :
    (idp_con p)⁻¹ ⬝ whisker_left idp h ⬝ idp_con q = h :=
  by induction h; induction p; reflexivity

  definition whisker_left_idp2 {A : Type} {a : A} (p : idp = idp :> a = a) :
    whisker_left idp p = p :=
  begin
    refine _ ⬝ whisker_left_idp p,
    exact !idp_con⁻¹
  end

  definition con2_idp [unfold_full] {p q : x = y} (h : p = q) :
    h ◾ idp = whisker_right h idp :> (p ⬝ idp = q ⬝ idp) :=
  idp

  definition idp_con2 [unfold_full] {p q : x = y} (h : p = q) :
    idp ◾ h = whisker_left idp h :> (idp ⬝ p = idp ⬝ q) :=
  idp

  definition inverse2_concat2 {p p' : x = y} (h : p = p')
    : h⁻² ◾ h = con.left_inv p ⬝ (con.left_inv p')⁻¹ :=
  by induction h; induction p; reflexivity

  -- The interchange law for concatenation.
  definition con2_con_con2 {p p' p'' : x = y} {q q' q'' : y = z}
      (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
    (a ◾ c) ⬝ (b ◾ d) = (a ⬝ b) ◾ (c ⬝ d) :=
  by induction d; induction c; induction b;induction a; reflexivity

  definition concat2_eq_rl {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
    (a : p = p') (b : q = q') : a ◾ b = whisker_right a q ⬝ whisker_left p' b :=
  by induction b; induction a; reflexivity

  definition concat2_eq_lf {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
    (a : p = p') (b : q = q') : a ◾ b = whisker_left p b ⬝ whisker_right a q' :=
  by induction b; induction a; reflexivity

  definition whisker_right_con_whisker_left {x y z : A} {p p' : x = y} {q q' : y = z}
    (a : p = p') (b : q = q') :
    (whisker_right a q) ⬝ (whisker_left p' b) = (whisker_left p b) ⬝ (whisker_right a q') :=
  by induction b; induction a; reflexivity

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
  by induction q; induction p; reflexivity

  definition eckmann_hilton {x:A} (p q : idp = idp :> x = x) : p ⬝ q = q ⬝ p :=
  begin
    refine (whisker_right_idp p ◾ whisker_left_idp2 q)⁻¹ ⬝ _,
    refine !whisker_right_con_whisker_left ⬝ _,
    refine !whisker_left_idp2 ◾ !whisker_right_idp
  end

  definition concat_eq_concat2 {A : Type} {a : A} (p q : idp = idp :> a = a) : p ⬝ q = p ◾ q :=
  begin
    refine (whisker_right_idp p ◾ whisker_left_idp2 q)⁻¹ ⬝ _,
    exact !concat2_eq_rl⁻¹
  end

  definition inverse_eq_inverse2 {A : Type} {a : A} (p : idp = idp :> a = a) : p⁻¹ = p⁻² :=
  begin
    apply eq.cancel_right p,
    refine !con.left_inv ⬝ _,
    refine _ ⬝ !concat_eq_concat2⁻¹,
    exact !inverse2_concat2⁻¹,
  end

  -- The action of functions on 2-dimensional paths
  definition ap02 [unfold 8] [reducible] (f : A → B) {x y : A} {p q : x = y} (r : p = q)
    : ap f p = ap f q :=
  ap (ap f) r

  definition ap02_con (f : A → B) {x y : A} {p p' p'' : x = y} (r : p = p') (r' : p' = p'') :
    ap02 f (r ⬝ r') = ap02 f r ⬝ ap02 f r' :=
  by induction r; induction r'; reflexivity

  definition ap02_con2 (f : A → B) {x y z : A} {p p' : x = y} {q q' :y = z} (r : p = p')
    (s : q = q') :
      ap02 f (r ◾ s) = ap_con f p q
                        ⬝ (ap02 f r  ◾  ap02 f s)
                        ⬝ (ap_con f p' q')⁻¹ :=
  by induction r; induction s; induction q; induction p; reflexivity

  definition apd02 [unfold 8] {p q : x = y} (f : Π x, P x) (r : p = q) :
    apd f p = transport2 P r (f x) ⬝ apd f q :=
  by induction r; exact !idp_con⁻¹

  -- And now for a lemma whose statement is much longer than its proof.
  definition apd02_con {P : A → Type} (f : Π x:A, P x) {x y : A}
      {p1 p2 p3 : x = y} (r1 : p1 = p2) (r2 : p2 = p3) :
    apd02 f (r1 ⬝ r2) = apd02 f r1
      ⬝ whisker_left (transport2 P r1 (f x)) (apd02 f r2)
      ⬝ con.assoc' _ _ _
      ⬝ (whisker_right (tr2_con r1 r2 (f x))⁻¹ (apd f p3)) :=
  by induction r2; induction r1; induction p1; reflexivity

end eq
