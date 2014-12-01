-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad
-- Ported from Coq HoTT
--
-- TODO: things to test:
-- o To what extent can we use opaque definitions outside the file?
-- o Try doing these proofs with tactics.
-- o Try using the simplifier on some of these proofs.

import algebra.function

open function

-- Path
-- ----

inductive path.{l} {A : Type.{l}} (a : A) : A → Type.{l} :=
idpath : path a a

namespace path
notation a ≈ b := path a b
notation x ≈ y `:>`:50 A:49 := @path A x y
definition idp {A : Type} {a : A} := idpath a

-- unbased path induction
definition rec' [reducible] {A : Type} {P : Π (a b : A), (a ≈ b) -> Type}
    (H : Π (a : A), P a a idp) {a b : A} (p : a ≈ b) : P a b p :=
path.rec (H a) p

definition rec_on' [reducible] {A : Type} {P : Π (a b : A), (a ≈ b) -> Type} {a b : A} (p : a ≈ b)
    (H : Π (a : A), P a a idp) : P a b p :=
path.rec (H a) p

-- Concatenation and inverse
-- -------------------------

definition concat {A : Type} {x y z : A} (p : x ≈ y) (q : y ≈ z) : x ≈ z :=
path.rec (λu, u) q p

definition inverse {A : Type} {x y : A} (p : x ≈ y) : y ≈ x :=
path.rec (idpath x) p

notation p₁ ⬝ p₂ := concat p₁ p₂
notation p ⁻¹ := inverse p

-- In Coq, these are not needed, because concat and inv are kept transparent
-- definition inv_1 {A : Type} (x : A) : (idpath x)⁻¹ ≈ idpath x := idp

-- definition concat_11 {A : Type} (x : A) : idpath x ⬝ idpath x ≈ idpath x := idp


-- The 1-dimensional groupoid structure
-- ------------------------------------

-- The identity path is a right unit.
definition concat_p1 {A : Type} {x y : A} (p : x ≈ y) : p ⬝ idp ≈ p :=
rec_on p idp

-- The identity path is a right unit.
definition concat_1p {A : Type} {x y : A} (p : x ≈ y) : idp ⬝ p ≈ p :=
rec_on p idp

-- Concatenation is associative.
definition concat_p_pp {A : Type} {x y z t : A} (p : x ≈ y) (q : y ≈ z) (r : z ≈ t) :
  p ⬝ (q ⬝ r) ≈ (p ⬝ q) ⬝ r :=
rec_on r (rec_on q idp)

definition concat_pp_p {A : Type} {x y z t : A} (p : x ≈ y) (q : y ≈ z) (r : z ≈ t) :
  (p ⬝ q) ⬝ r ≈ p ⬝ (q ⬝ r) :=
rec_on r (rec_on q idp)

-- The left inverse law.
definition concat_pV {A : Type} {x y : A} (p : x ≈ y) : p ⬝ p⁻¹ ≈ idp :=
rec_on p idp

-- The right inverse law.
definition concat_Vp {A : Type} {x y : A} (p : x ≈ y) : p⁻¹ ⬝ p ≈ idp :=
rec_on p idp

-- Several auxiliary theorems about canceling inverses across associativity. These are somewhat
-- redundant, following from earlier theorems.

definition concat_V_pp {A : Type} {x y z : A} (p : x ≈ y) (q : y ≈ z) : p⁻¹ ⬝ (p ⬝ q) ≈ q :=
rec_on q (rec_on p idp)

definition concat_p_Vp {A : Type} {x y z : A} (p : x ≈ y) (q : x ≈ z) : p ⬝ (p⁻¹ ⬝ q) ≈ q :=
rec_on q (rec_on p idp)

definition concat_pp_V {A : Type} {x y z : A} (p : x ≈ y) (q : y ≈ z) : (p ⬝ q) ⬝ q⁻¹ ≈ p :=
rec_on q (rec_on p idp)

definition concat_pV_p {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) : (p ⬝ q⁻¹) ⬝ q ≈ p :=
rec_on q (take p, rec_on p idp) p

-- Inverse distributes over concatenation
definition inv_pp {A : Type} {x y z : A} (p : x ≈ y) (q : y ≈ z) : (p ⬝ q)⁻¹ ≈ q⁻¹ ⬝ p⁻¹ :=
rec_on q (rec_on p idp)

definition inv_Vp {A : Type} {x y z : A} (p : y ≈ x) (q : y ≈ z) : (p⁻¹ ⬝ q)⁻¹ ≈ q⁻¹ ⬝ p :=
rec_on q (rec_on p idp)

-- universe metavariables
definition inv_pV {A : Type} {x y z : A} (p : x ≈ y) (q : z ≈ y) : (p ⬝ q⁻¹)⁻¹ ≈ q ⬝ p⁻¹ :=
rec_on p (take q, rec_on q idp) q

definition inv_VV {A : Type} {x y z : A} (p : y ≈ x) (q : z ≈ y) : (p⁻¹ ⬝ q⁻¹)⁻¹ ≈ q ⬝ p :=
rec_on p (rec_on q idp)

-- Inverse is an involution.
definition inv_V {A : Type} {x y : A} (p : x ≈ y) : p⁻¹⁻¹ ≈ p :=
rec_on p idp

-- Theorems for moving things around in equations
-- ----------------------------------------------

definition moveR_Mp {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) (r : y ≈ x) :
  p ≈ (r⁻¹ ⬝ q) → (r ⬝ p) ≈ q :=
rec_on r (take p h, concat_1p _ ⬝ h ⬝ concat_1p _) p

definition moveR_pM {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) (r : y ≈ x) :
  r ≈ q ⬝ p⁻¹ → r ⬝ p ≈ q :=
rec_on p (take q h, (concat_p1 _ ⬝ h ⬝ concat_p1 _)) q

definition moveR_Vp {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) (r : x ≈ y) :
  p ≈ r ⬝ q → r⁻¹ ⬝ p ≈ q :=
rec_on r (take q h, concat_1p _ ⬝ h ⬝ concat_1p _) q

definition moveR_pV {A : Type} {x y z : A} (p : z ≈ x) (q : y ≈ z) (r : y ≈ x) :
  r ≈ q ⬝ p → r ⬝ p⁻¹ ≈ q :=
rec_on p (take r h, concat_p1 _ ⬝ h ⬝ concat_p1 _) r

definition moveL_Mp {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) (r : y ≈ x) :
  r⁻¹ ⬝ q ≈ p → q ≈ r ⬝ p :=
rec_on r (take p h, (concat_1p _)⁻¹ ⬝ h ⬝ (concat_1p _)⁻¹) p

definition moveL_pM {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) (r : y ≈ x) :
  q ⬝ p⁻¹ ≈ r → q ≈ r ⬝ p :=
rec_on p (take q h, (concat_p1 _)⁻¹ ⬝ h ⬝ (concat_p1 _)⁻¹) q

definition moveL_Vp {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) (r : x ≈ y) :
  r ⬝ q ≈ p → q ≈ r⁻¹ ⬝ p :=
rec_on r (take q h, (concat_1p _)⁻¹ ⬝ h ⬝ (concat_1p _)⁻¹) q

definition moveL_pV {A : Type} {x y z : A} (p : z ≈ x) (q : y ≈ z) (r : y ≈ x) :
  q ⬝ p ≈ r → q ≈ r ⬝ p⁻¹ :=
rec_on p (take r h, (concat_p1 _)⁻¹ ⬝ h ⬝ (concat_p1 _)⁻¹) r

definition moveL_1M {A : Type} {x y : A} (p q : x ≈ y) :
  p ⬝ q⁻¹ ≈ idp → p ≈ q :=
rec_on q (take p h, (concat_p1 _)⁻¹ ⬝ h) p

definition moveL_M1 {A : Type} {x y : A} (p q : x ≈ y) :
  q⁻¹ ⬝ p ≈ idp → p ≈ q :=
rec_on q (take p h, (concat_1p _)⁻¹ ⬝ h) p

definition moveL_1V {A : Type} {x y : A} (p : x ≈ y) (q : y ≈ x) :
  p ⬝ q ≈ idp → p ≈ q⁻¹ :=
rec_on q (take p h, (concat_p1 _)⁻¹ ⬝ h) p

definition moveL_V1 {A : Type} {x y : A} (p : x ≈ y) (q : y ≈ x) :
  q ⬝ p ≈ idp → p ≈ q⁻¹ :=
rec_on q (take p h, (concat_1p _)⁻¹ ⬝ h) p

definition moveR_M1 {A : Type} {x y : A} (p q : x ≈ y) :
  idp ≈ p⁻¹ ⬝ q → p ≈ q :=
rec_on p (take q h, h ⬝ (concat_1p _)) q

definition moveR_1M {A : Type} {x y : A} (p q : x ≈ y) :
  idp ≈ q ⬝ p⁻¹ → p ≈ q :=
rec_on p (take q h, h ⬝ (concat_p1 _)) q

definition moveR_1V {A : Type} {x y : A} (p : x ≈ y) (q : y ≈ x) :
  idp ≈ q ⬝ p → p⁻¹ ≈ q :=
rec_on p (take q h, h ⬝ (concat_p1 _)) q

definition moveR_V1 {A : Type} {x y : A} (p : x ≈ y) (q : y ≈ x) :
  idp ≈ p ⬝ q → p⁻¹ ≈ q :=
rec_on p (take q h, h ⬝ (concat_1p _)) q


-- Transport
-- ---------

definition transport [reducible] {A : Type} (P : A → Type) {x y : A} (p : x ≈ y) (u : P x) : P y :=
path.rec_on p u

-- This idiom makes the operation right associative.
notation p `▹`:65 x:64 := transport _ p x

definition ap ⦃A B : Type⦄ (f : A → B) {x y:A} (p : x ≈ y) : f x ≈ f y :=
path.rec_on p idp

definition ap01 := ap

definition homotopy [reducible] {A : Type} {P : A → Type} (f g : Πx, P x) : Type :=
Πx : A, f x ≈ g x

notation f ∼ g := homotopy f g

definition apD10 {A} {B : A → Type} {f g : Πx, B x} (H : f ≈ g) : f ∼ g :=
λx, path.rec_on H idp

definition ap10 {A B} {f g : A → B} (H : f ≈ g) : f ∼ g := apD10 H

definition ap11 {A B} {f g : A → B} (H : f ≈ g) {x y : A} (p : x ≈ y) : f x ≈ g y :=
rec_on H (rec_on p idp)

definition apD {A:Type} {B : A → Type} (f : Πa:A, B a) {x y : A} (p : x ≈ y) : p ▹ (f x) ≈ f y :=
rec_on p idp


-- calc enviroment
-- ---------------

calc_subst transport
calc_trans concat
calc_refl idpath
calc_symm inverse

-- More theorems for moving things around in equations
-- ---------------------------------------------------

definition moveR_transport_p {A : Type} (P : A → Type) {x y : A} (p : x ≈ y) (u : P x) (v : P y) :
  u ≈ p⁻¹ ▹ v → p ▹ u ≈ v :=
rec_on p (take v, id) v

definition moveR_transport_V {A : Type} (P : A → Type) {x y : A} (p : y ≈ x) (u : P x) (v : P y) :
  u ≈ p ▹ v → p⁻¹ ▹ u ≈ v :=
rec_on p (take u, id) u

definition moveL_transport_V {A : Type} (P : A → Type) {x y : A} (p : x ≈ y) (u : P x) (v : P y) :
  p ▹ u ≈ v → u ≈ p⁻¹ ▹ v :=
rec_on p (take v, id) v

definition moveL_transport_p {A : Type} (P : A → Type) {x y : A} (p : y ≈ x) (u : P x) (v : P y) :
  p⁻¹ ▹ u ≈ v → u ≈ p ▹ v :=
rec_on p (take u, id) u

-- Functoriality of functions
-- --------------------------

-- Here we prove that functions behave like functors between groupoids, and that [ap] itself is
-- functorial.

-- Functions take identity paths to identity paths
definition ap_1 {A B : Type} (x : A) (f : A → B) : (ap f idp) ≈ idp :> (f x ≈ f x) := idp

definition apD_1 {A B} (x : A) (f : Π x : A, B x) : apD f idp ≈ idp :> (f x ≈ f x) := idp

-- Functions commute with concatenation.
definition ap_pp {A B : Type} (f : A → B) {x y z : A} (p : x ≈ y) (q : y ≈ z) :
  ap f (p ⬝ q) ≈ (ap f p) ⬝ (ap f q) :=
rec_on q (rec_on p idp)

definition ap_p_pp {A B : Type} (f : A → B) {w x y z : A} (r : f w ≈ f x) (p : x ≈ y) (q : y ≈ z) :
  r ⬝ (ap f (p ⬝ q)) ≈ (r ⬝ ap f p) ⬝ (ap f q) :=
rec_on q (take p, rec_on p (concat_p_pp r idp idp)) p

definition ap_pp_p {A B : Type} (f : A → B) {w x y z : A} (p : x ≈ y) (q : y ≈ z) (r : f z ≈ f w) :
  (ap f (p ⬝ q)) ⬝ r ≈ (ap f p) ⬝ (ap f q ⬝ r) :=
rec_on q (rec_on p (take r, concat_pp_p _ _ _)) r

-- Functions commute with path inverses.
definition inverse_ap {A B : Type} (f : A → B) {x y : A} (p : x ≈ y) : (ap f p)⁻¹ ≈ ap f (p⁻¹) :=
rec_on p idp

definition ap_V {A B : Type} (f : A → B) {x y : A} (p : x ≈ y) : ap f (p⁻¹) ≈ (ap f p)⁻¹ :=
rec_on p idp

-- [ap] itself is functorial in the first argument.

definition ap_idmap {A : Type} {x y : A} (p : x ≈ y) : ap id p ≈ p :=
rec_on p idp

definition ap_compose {A B C : Type} (f : A → B) (g : B → C) {x y : A} (p : x ≈ y) :
  ap (g ∘ f) p ≈ ap g (ap f p) :=
rec_on p idp

-- Sometimes we don't have the actual function [compose].
definition ap_compose' {A B C : Type} (f : A → B) (g : B → C) {x y : A} (p : x ≈ y) :
  ap (λa, g (f a)) p ≈ ap g (ap f p) :=
rec_on p idp

-- The action of constant maps.
definition ap_const {A B : Type} {x y : A} (p : x ≈ y) (z : B) :
  ap (λu, z) p ≈ idp :=
rec_on p idp

-- Naturality of [ap].
definition concat_Ap {A B : Type} {f g : A → B} (p : Π x, f x ≈ g x) {x y : A} (q : x ≈ y) :
  (ap f q) ⬝ (p y) ≈ (p x) ⬝ (ap g q) :=
rec_on q (concat_1p _ ⬝ (concat_p1 _)⁻¹)

-- Naturality of [ap] at identity.
definition concat_A1p {A : Type} {f : A → A} (p : Πx, f x ≈ x) {x y : A} (q : x ≈ y) :
  (ap f q) ⬝ (p y) ≈ (p x) ⬝ q :=
rec_on q (concat_1p _ ⬝ (concat_p1 _)⁻¹)

definition concat_pA1 {A : Type} {f : A → A} (p : Πx, x ≈ f x) {x y : A} (q : x ≈ y) :
  (p x) ⬝ (ap f q) ≈  q ⬝ (p y) :=
rec_on q (concat_p1 _ ⬝ (concat_1p _)⁻¹)

-- Naturality with other paths hanging around.

definition concat_pA_pp {A B : Type} {f g : A → B} (p : Πx, f x ≈ g x) {x y : A} (q : x ≈ y)
    {w z : B} (r : w ≈ f x) (s : g y ≈ z) :
  (r ⬝ ap f q) ⬝ (p y ⬝ s) ≈ (r ⬝ p x) ⬝ (ap g q ⬝ s) :=
rec_on s (rec_on q idp)

definition concat_pA_p {A B : Type} {f g : A → B} (p : Πx, f x ≈ g x) {x y : A} (q : x ≈ y)
    {w : B} (r : w ≈ f x) :
  (r ⬝ ap f q) ⬝ p y ≈ (r ⬝ p x) ⬝ ap g q :=
rec_on q idp

-- TODO: try this using the simplifier, and compare proofs
definition concat_A_pp {A B : Type} {f g : A → B} (p : Πx, f x ≈ g x) {x y : A} (q : x ≈ y)
    {z : B} (s : g y ≈ z) :
  (ap f q) ⬝ (p y ⬝ s) ≈ (p x) ⬝ (ap g q ⬝ s) :=
rec_on s (rec_on q
  (calc
    (ap f idp) ⬝ (p x ⬝ idp) ≈ idp ⬝ p x : idp
      ... ≈ p x : concat_1p _
      ... ≈ (p x) ⬝ (ap g idp ⬝ idp) : idp))
-- This also works:
-- rec_on s (rec_on q (concat_1p _ ▹ idp))

definition concat_pA1_pp {A : Type} {f : A → A} (p : Πx, f x ≈ x) {x y : A} (q : x ≈ y)
    {w z : A} (r : w ≈ f x) (s : y ≈ z) :
  (r ⬝ ap f q) ⬝ (p y ⬝ s) ≈ (r ⬝ p x) ⬝ (q ⬝ s) :=
rec_on s (rec_on q idp)

definition concat_pp_A1p {A : Type} {g : A → A} (p : Πx, x ≈ g x) {x y : A} (q : x ≈ y)
    {w z : A} (r : w ≈ x) (s : g y ≈ z) :
  (r ⬝ p x) ⬝ (ap g q ⬝ s) ≈ (r ⬝ q) ⬝ (p y ⬝ s) :=
rec_on s (rec_on q idp)

definition concat_pA1_p {A : Type} {f : A → A} (p : Πx, f x ≈ x) {x y : A} (q : x ≈ y)
    {w : A} (r : w ≈ f x) :
  (r ⬝ ap f q) ⬝ p y ≈ (r ⬝ p x) ⬝ q :=
rec_on q idp

definition concat_A1_pp {A : Type} {f : A → A} (p : Πx, f x ≈ x) {x y : A} (q : x ≈ y)
    {z : A} (s : y ≈ z) :
  (ap f q) ⬝ (p y ⬝ s) ≈ (p x) ⬝ (q ⬝ s) :=
rec_on s (rec_on q (concat_1p _ ▹ idp))

definition concat_pp_A1 {A : Type} {g : A → A} (p : Πx, x ≈ g x) {x y : A} (q : x ≈ y)
    {w : A} (r : w ≈ x) :
  (r ⬝ p x) ⬝ ap g q ≈ (r ⬝ q) ⬝ p y :=
rec_on q idp

definition concat_p_A1p {A : Type} {g : A → A} (p : Πx, x ≈ g x) {x y : A} (q : x ≈ y)
    {z : A} (s : g y ≈ z) :
  p x ⬝ (ap g q ⬝ s) ≈ q ⬝ (p y ⬝ s) :=
begin
  apply (rec_on s),
  apply (rec_on q),
  apply (concat_1p (p x) ▹ idp)
end

-- Action of [apD10] and [ap10] on paths
-- -------------------------------------

-- Application of paths between functions preserves the groupoid structure

definition apD10_1 {A} {B : A → Type} (f : Πx, B x) (x : A) : apD10 (idpath f) x ≈ idp := idp

definition apD10_pp {A} {B : A → Type} {f f' f'' : Πx, B x} (h : f ≈ f') (h' : f' ≈ f'') (x : A) :
  apD10 (h ⬝ h') x ≈ apD10 h x ⬝ apD10 h' x :=
rec_on h (take h', rec_on h' idp) h'

definition apD10_V {A : Type} {B : A → Type} {f g : Πx : A, B x} (h : f ≈ g) (x : A) :
  apD10 (h⁻¹) x ≈ (apD10 h x)⁻¹ :=
rec_on h idp

definition ap10_1 {A B} {f : A → B} (x : A) : ap10 (idpath f) x ≈ idp := idp

definition ap10_pp {A B} {f f' f'' : A → B} (h : f ≈ f') (h' : f' ≈ f'') (x : A) :
  ap10 (h ⬝ h') x ≈ ap10 h x ⬝ ap10 h' x := apD10_pp h h' x

definition ap10_V {A B} {f g : A→B} (h : f ≈ g) (x:A) : ap10 (h⁻¹) x ≈ (ap10 h x)⁻¹ := apD10_V h x

-- [ap10] also behaves nicely on paths produced by [ap]
definition ap_ap10 {A B C} (f g : A → B) (h : B → C) (p : f ≈ g) (a : A) :
  ap h (ap10 p a) ≈ ap10 (ap (λ f', h ∘ f') p) a:=
rec_on p idp


-- Transport and the groupoid structure of paths
-- ---------------------------------------------

definition transport_1 {A : Type} (P : A → Type) {x : A} (u : P x) :
  idp ▹ u ≈ u := idp

definition transport_pp {A : Type} (P : A → Type) {x y z : A} (p : x ≈ y) (q : y ≈ z) (u : P x) :
  p ⬝ q ▹ u ≈ q ▹ p ▹ u :=
rec_on q (rec_on p idp)

definition transport_pV {A : Type} (P : A → Type) {x y : A} (p : x ≈ y) (z : P y) :
  p ▹ p⁻¹ ▹ z ≈ z :=
(transport_pp P (p⁻¹) p z)⁻¹ ⬝ ap (λr, transport P r z) (concat_Vp p)

definition transport_Vp {A : Type} (P : A → Type) {x y : A} (p : x ≈ y) (z : P x) :
  p⁻¹ ▹ p ▹ z ≈ z :=
(transport_pp P p (p⁻¹) z)⁻¹ ⬝ ap (λr, transport P r z) (concat_pV p)

definition transport_p_pp {A : Type} (P : A → Type)
    {x y z w : A} (p : x ≈ y) (q : y ≈ z) (r : z ≈ w) (u : P x) :
  ap (λe, e ▹ u) (concat_p_pp p q r) ⬝ (transport_pp P (p ⬝ q) r u) ⬝
      ap (transport P r) (transport_pp P p q u)
    ≈ (transport_pp P p (q ⬝ r) u) ⬝ (transport_pp P q r (p ▹ u))
    :> ((p ⬝ (q ⬝ r)) ▹ u ≈ r ▹ q ▹ p ▹ u) :=
rec_on r (rec_on q (rec_on p idp))

--  Here is another coherence lemma for transport.
definition transport_pVp {A} (P : A → Type) {x y : A} (p : x ≈ y) (z : P x) :
  transport_pV P p (transport P p z) ≈ ap (transport P p) (transport_Vp P p z) :=
rec_on p idp

-- Dependent transport in a doubly dependent type.
-- should B, C and y all be explicit here?
definition transportD {A : Type} (B : A → Type) (C : Π a : A, B a → Type)
    {x1 x2 : A} (p : x1 ≈ x2) (y : B x1) (z : C x1 y) : C x2 (p ▹ y) :=
rec_on p z
-- In Coq the variables B, C and y are explicit, but in Lean we can probably have them implicit using the following notation
notation p `▹D`:65 x:64 := transportD _ _ p _ x

-- Transporting along higher-dimensional paths
definition transport2 {A : Type} (P : A → Type) {x y : A} {p q : x ≈ y} (r : p ≈ q) (z : P x) :
  p ▹ z ≈ q ▹ z :=
ap (λp', p' ▹ z) r

notation p `▹2`:65 x:64 := transport2 _ p _ x

-- An alternative definition.
definition transport2_is_ap10 {A : Type} (Q : A → Type) {x y : A} {p q : x ≈ y} (r : p ≈ q)
    (z : Q x) :
  transport2 Q r z ≈ ap10 (ap (transport Q) r) z :=
rec_on r idp

definition transport2_p2p {A : Type} (P : A → Type) {x y : A} {p1 p2 p3 : x ≈ y}
    (r1 : p1 ≈ p2) (r2 : p2 ≈ p3) (z : P x) :
  transport2 P (r1 ⬝ r2) z ≈ transport2 P r1 z ⬝ transport2 P r2 z :=
rec_on r1 (rec_on r2 idp)

definition transport2_V {A : Type} (Q : A → Type) {x y : A} {p q : x ≈ y} (r : p ≈ q) (z : Q x) :
  transport2 Q (r⁻¹) z ≈ ((transport2 Q r z)⁻¹) :=
rec_on r idp

definition transportD2 {A : Type} (B C : A → Type) (D : Π(a:A), B a → C a → Type)
  {x1 x2 : A} (p : x1 ≈ x2) (y : B x1) (z : C x1) (w : D x1 y z) : D x2 (p ▹ y) (p ▹ z) :=
rec_on p w

notation p `▹D2`:65 x:64 := transportD2 _ _ _ p _ _ x

definition concat_AT {A : Type} (P : A → Type) {x y : A} {p q : x ≈ y} {z w : P x} (r : p ≈ q)
    (s : z ≈ w) :
  ap (transport P p) s  ⬝  transport2 P r w ≈ transport2 P r z  ⬝  ap (transport P q) s :=
rec_on r (concat_p1 _ ⬝ (concat_1p _)⁻¹)

-- TODO (from Coq library): What should this be called?
definition ap_transport {A} {P Q : A → Type} {x y : A} (p : x ≈ y) (f : Πx, P x → Q x) (z : P x) :
  f y (p ▹ z) ≈ (p ▹ (f x z)) :=
rec_on p idp


-- Transporting in particular fibrations
-- -------------------------------------

/-
From the Coq HoTT library:

One frequently needs lemmas showing that transport in a certain dependent type is equal to some
more explicitly defined operation, defined according to the structure of that dependent type.
For most dependent types, we prove these lemmas in the appropriate file in the types/
subdirectory.  Here we consider only the most basic cases.
-/

-- Transporting in a constant fibration.
definition transport_const {A B : Type} {x1 x2 : A} (p : x1 ≈ x2) (y : B) :
  transport (λx, B) p y ≈ y :=
rec_on p idp

definition transport2_const {A B : Type} {x1 x2 : A} {p q : x1 ≈ x2} (r : p ≈ q) (y : B) :
  transport_const p y ≈ transport2 (λu, B) r y ⬝ transport_const q y :=
rec_on r (concat_1p _)⁻¹

-- Transporting in a pulled back fibration.
-- TODO: P can probably be implicit
definition transport_compose {A B} {x y : A} (P : B → Type) (f : A → B) (p : x ≈ y) (z : P (f x)) :
  transport (λx, P (f x)) p z  ≈  transport P (ap f p) z :=
rec_on p idp

definition transport_precompose {A B C} (f : A → B) (g g' : B → C) (p : g ≈ g') :
  transport (λh : B → C, g ∘ f ≈ h ∘ f) p idp ≈ ap (λh, h ∘ f) p :=
rec_on p idp

definition apD10_ap_precompose {A B C} (f : A → B) (g g' : B → C) (p : g ≈ g') (a : A) :
  apD10 (ap (λh : B → C, h ∘ f) p) a ≈ apD10 p (f a) :=
rec_on p idp

definition apD10_ap_postcompose {A B C} (f : B → C) (g g' : A → B) (p : g ≈ g') (a : A) :
  apD10 (ap (λh : A → B, f ∘ h) p) a ≈ ap f (apD10 p a) :=
rec_on p idp

-- A special case of [transport_compose] which seems to come up a lot.
definition transport_idmap_ap A (P : A → Type) x y (p : x ≈ y) (u : P x) :
  transport P p u ≈ transport (λz, z) (ap P p) u :=
rec_on p idp


-- The behavior of [ap] and [apD]
-- ------------------------------

-- In a constant fibration, [apD] reduces to [ap], modulo [transport_const].
definition apD_const {A B} {x y : A} (f : A → B) (p: x ≈ y) :
  apD f p ≈ transport_const p (f x) ⬝ ap f p :=
rec_on p idp


-- The 2-dimensional groupoid structure
-- ------------------------------------

-- Horizontal composition of 2-dimensional paths.
definition concat2 {A} {x y z : A} {p p' : x ≈ y} {q q' : y ≈ z} (h : p ≈ p') (h' : q ≈ q') :
  p ⬝ q ≈ p' ⬝ q' :=
rec_on h (rec_on h' idp)

infixl `◾`:75 := concat2

-- 2-dimensional path inversion
definition inverse2 {A : Type} {x y : A} {p q : x ≈ y} (h : p ≈ q) : p⁻¹ ≈ q⁻¹ :=
rec_on h idp


-- Whiskering
-- ----------

definition whiskerL {A : Type} {x y z : A} (p : x ≈ y) {q r : y ≈ z} (h : q ≈ r) : p ⬝ q ≈ p ⬝ r :=
idp ◾ h

definition whiskerR {A : Type} {x y z : A} {p q : x ≈ y} (h : p ≈ q) (r : y ≈ z) : p ⬝ r ≈ q ⬝ r :=
h ◾ idp

-- Unwhiskering, a.k.a. cancelling

definition cancelL {A} {x y z : A} (p : x ≈ y) (q r : y ≈ z) : (p ⬝ q ≈ p ⬝ r) → (q ≈ r) :=
rec_on p (take r, rec_on r (take q a, (concat_1p q)⁻¹ ⬝ a)) r q

definition cancelR {A} {x y z : A} (p q : x ≈ y) (r : y ≈ z) : (p ⬝ r ≈ q ⬝ r) → (p ≈ q) :=
rec_on r (rec_on p (take q a, a ⬝ concat_p1 q)) q

-- Whiskering and identity paths.

definition whiskerR_p1 {A : Type} {x y : A} {p q : x ≈ y} (h : p ≈ q) :
  (concat_p1 p)⁻¹ ⬝ whiskerR h idp ⬝ concat_p1 q ≈ h :=
rec_on h (rec_on p idp)

definition whiskerR_1p {A : Type} {x y z : A} (p : x ≈ y) (q : y ≈ z) :
  whiskerR idp q ≈ idp :> (p ⬝ q ≈ p ⬝ q) :=
rec_on q idp

definition whiskerL_p1 {A : Type} {x y z : A} (p : x ≈ y) (q : y ≈ z) :
  whiskerL p idp ≈ idp :> (p ⬝ q ≈ p ⬝ q) :=
rec_on q idp

definition whiskerL_1p {A : Type} {x y : A} {p q : x ≈ y} (h : p ≈ q) :
  (concat_1p p) ⁻¹ ⬝ whiskerL idp h ⬝ concat_1p q ≈ h :=
rec_on h (rec_on p idp)

definition concat2_p1 {A : Type} {x y : A} {p q : x ≈ y} (h : p ≈ q) :
  h ◾ idp ≈ whiskerR h idp :> (p ⬝ idp ≈ q ⬝ idp) :=
rec_on h idp

definition concat2_1p {A : Type} {x y : A} {p q : x ≈ y} (h : p ≈ q) :
  idp ◾ h ≈ whiskerL idp h :> (idp ⬝ p ≈ idp ⬝ q) :=
rec_on h idp

-- TODO: note, 4 inductions
-- The interchange law for concatenation.
definition concat_concat2 {A : Type} {x y z : A} {p p' p'' : x ≈ y} {q q' q'' : y ≈ z}
    (a : p ≈ p') (b : p' ≈ p'') (c : q ≈ q') (d : q' ≈ q'') :
  (a ◾ c) ⬝ (b ◾ d) ≈ (a ⬝ b) ◾ (c ⬝ d) :=
rec_on d (rec_on c (rec_on b (rec_on a idp)))

definition concat_whisker {A} {x y z : A} (p p' : x ≈ y) (q q' : y ≈ z) (a : p ≈ p') (b : q ≈ q') :
  (whiskerR a q) ⬝ (whiskerL p' b) ≈ (whiskerL p b) ⬝ (whiskerR a q') :=
rec_on b (rec_on a (concat_1p _)⁻¹)

-- Structure corresponding to the coherence equations of a bicategory.

-- The "pentagonator": the 3-cell witnessing the associativity pentagon.
definition pentagon {A : Type} {v w x y z : A} (p : v ≈ w) (q : w ≈ x) (r : x ≈ y) (s : y ≈ z) :
  whiskerL p (concat_p_pp q r s)
    ⬝ concat_p_pp p (q ⬝ r) s
    ⬝ whiskerR (concat_p_pp p q r) s
  ≈ concat_p_pp p q (r ⬝ s) ⬝ concat_p_pp (p ⬝ q) r s :=
rec_on s (rec_on r (rec_on q (rec_on p idp)))

-- The 3-cell witnessing the left unit triangle.
definition triangulator {A : Type} {x y z : A} (p : x ≈ y) (q : y ≈ z) :
  concat_p_pp p idp q ⬝ whiskerR (concat_p1 p) q ≈ whiskerL p (concat_1p q) :=
rec_on q (rec_on p idp)

definition eckmann_hilton {A : Type} {x:A} (p q : idp ≈ idp :> (x ≈ x)) : p ⬝ q ≈ q ⬝ p :=
  (!whiskerR_p1 ◾ !whiskerL_1p)⁻¹
  ⬝ (!concat_p1 ◾ !concat_p1)
  ⬝ (!concat_1p ◾ !concat_1p)
  ⬝ !concat_whisker
  ⬝ (!concat_1p ◾ !concat_1p)⁻¹
  ⬝ (!concat_p1 ◾ !concat_p1)⁻¹
  ⬝ (!whiskerL_1p ◾ !whiskerR_p1)

-- The action of functions on 2-dimensional paths
definition ap02 {A B : Type} (f:A → B) {x y : A} {p q : x ≈ y} (r : p ≈ q) : ap f p ≈ ap f q :=
rec_on r idp

definition ap02_pp {A B} (f : A → B) {x y : A} {p p' p'' : x ≈ y} (r : p ≈ p') (r' : p' ≈ p'') :
  ap02 f (r ⬝ r') ≈ ap02 f r ⬝ ap02 f r' :=
rec_on r (rec_on r' idp)

definition ap02_p2p {A B} (f : A → B) {x y z : A} {p p' : x ≈ y} {q q' :y ≈ z} (r : p ≈ p')
    (s : q ≈ q') :
  ap02 f (r ◾ s) ≈   ap_pp f p q
                      ⬝ (ap02 f r  ◾  ap02 f s)
                      ⬝ (ap_pp f p' q')⁻¹ :=
rec_on r (rec_on s (rec_on q (rec_on p idp)))

-- rec_on r (rec_on s (rec_on p (rec_on q idp)))

definition apD02 {A : Type} {B : A → Type} {x y : A} {p q : x ≈ y} (f : Π x, B x) (r : p ≈ q) :
  apD f p ≈ transport2 B r (f x) ⬝ apD f q :=
rec_on r (concat_1p _)⁻¹

-- And now for a lemma whose statement is much longer than its proof.
definition apD02_pp {A} (B : A → Type) (f : Π x:A, B x) {x y : A}
    {p1 p2 p3 : x ≈ y} (r1 : p1 ≈ p2) (r2 : p2 ≈ p3) :
  apD02 f (r1 ⬝ r2) ≈ apD02 f r1
    ⬝ whiskerL (transport2 B r1 (f x)) (apD02 f r2)
    ⬝ concat_p_pp _ _ _
    ⬝ (whiskerR ((transport2_p2p B r1 r2 (f x))⁻¹) (apD f p3)) :=
rec_on r2 (rec_on r1 (rec_on p1 idp))

section
variables {A B C D E : Type} {a a' : A} {b b' : B} {c c' : C} {d d' : D}

theorem congr_arg2 (f : A → B → C) (Ha : a ≈ a') (Hb : b ≈ b') : f a b ≈ f a' b' :=
rec_on Ha (rec_on Hb idp)

theorem congr_arg3 (f : A → B → C → D) (Ha : a ≈ a') (Hb : b ≈ b') (Hc : c ≈ c')
    : f a b c ≈ f a' b' c' :=
rec_on Ha (congr_arg2 (f a) Hb Hc)

theorem congr_arg4 (f : A → B → C → D → E) (Ha : a ≈ a') (Hb : b ≈ b') (Hc : c ≈ c') (Hd : d ≈ d')
    : f a b c d ≈ f a' b' c' d' :=
rec_on Ha (congr_arg3 (f a) Hb Hc Hd)

end

section
variables {A : Type} {B : A → Type} {C : Πa, B a → Type} {D : Πa b, C a b → Type}
          {E : Πa b c, D a b c → Type} {F : Type}
variables {a a' : A}
          {b : B a} {b' : B a'}
          {c : C a b} {c' : C a' b'}
          {d : D a b c} {d' : D a' b' c'}

theorem dcongr_arg2 (f : Πa, B a → F) (Ha : a ≈ a') (Hb : Ha ▹ b ≈ b')
    : f a b ≈ f a' b' :=
rec_on Hb (rec_on Ha idp)

end

/- From the Coq version:

-- ** Tactics, hints, and aliases

-- [concat], with arguments flipped. Useful mainly in the idiom [apply (concatR (expression))].
-- Given as a notation not a definition so that the resultant terms are literally instances of
-- [concat], with no unfolding required.
Notation concatR := (λp q, concat q p).

Hint Resolve
  concat_1p concat_p1 concat_p_pp
  inv_pp inv_V
 : path_hints.

(* First try at a paths db
We want the RHS of the equation to become strictly simpler
Hint Rewrite
⬝concat_p1
⬝concat_1p
⬝concat_p_pp (* there is a choice here !*)
⬝concat_pV
⬝concat_Vp
⬝concat_V_pp
⬝concat_p_Vp
⬝concat_pp_V
⬝concat_pV_p
(*⬝inv_pp*) (* I am not sure about this one
⬝inv_V
⬝moveR_Mp
⬝moveR_pM
⬝moveL_Mp
⬝moveL_pM
⬝moveL_1M
⬝moveL_M1
⬝moveR_M1
⬝moveR_1M
⬝ap_1
(* ⬝ap_pp
⬝ap_p_pp ?*)
⬝inverse_ap
⬝ap_idmap
(* ⬝ap_compose
⬝ap_compose'*)
⬝ap_const
(* Unsure about naturality of [ap], was absent in the old implementation*)
⬝apD10_1
:paths.

Ltac hott_simpl :=
  autorewrite with paths in * |- * ; auto with path_hints.

-/

end path
