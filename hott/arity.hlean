/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.path
Author: Floris van Doorn

Theorems about functions with multiple arguments
-/

variables {A U V W X Y Z : Type} {B : A → Type} {C : Πa, B a → Type} {D : Πa b, C a b → Type}
          {E : Πa b c, D a b c → Type}
variables {a a' : A} {u u' : U} {v v' : V} {w w' : W} {x x' x'' : X} {y y' : Y}
          {b : B a} {b' : B a'}
          {c : C a b} {c' : C a' b'}
          {d : D a b c} {d' : D a' b' c'}

namespace eq
  /-
    Naming convention:
      The theorem which states how to construct an path between two function applications is
        api₀i₁...iₙ.
      Here i₀, ... iₙ are digits, n is the arity of the function(s),
        and iⱼ specifies the dimension of the path between the jᵗʰ argument
        (i₀ specifies the dimension of the path between the functions).
      A value iⱼ ≡ 0 means that the jᵗʰ arguments are definitionally equal
      The functions are non-dependent, except when the theorem name contains trailing zeroes
        (where the function is dependent only in the arguments where it doesn't result in any
         transports in the theorem statement).
      For the fully-dependent versions (except that the conclusion doesn't contain a transport)
      we write
        apDi₀i₁...iₙ.

      For versions where only some arguments depend on some other arguments,
      or for versions with transport in the conclusion (like apD), we don't have a
      consistent naming scheme (yet).

      We don't prove each theorem systematically, but prove only the ones which we actually need.
  -/

  definition homotopy2 [reducible] (f g : Πa b, C a b)         : Type :=
  Πa b, f a b = g a b
  definition homotopy3 [reducible] (f g : Πa b c, D a b c)     : Type :=
  Πa b c, f a b c = g a b c
  definition homotopy4 [reducible] (f g : Πa b c d, E a b c d) : Type :=
  Πa b c d, f a b c d = g a b c d

  notation f `∼2`:50 g := homotopy2 f g
  notation f `∼3`:50 g := homotopy3 f g

  definition ap011 (f : U → V → W) (Hu : u = u') (Hv : v = v') : f u v = f u' v' :=
  eq.rec_on Hu (ap (f u) Hv)

  definition ap0111 (f : U → V → W → X) (Hu : u = u') (Hv : v = v') (Hw : w = w')
      : f u v w = f u' v' w' :=
  eq.rec_on Hu (ap011 (f u) Hv Hw)

  definition ap01111 (f : U → V → W → X → Y) (Hu : u = u') (Hv : v = v') (Hw : w = w') (Hx : x = x')
      : f u v w x = f u' v' w' x' :=
  eq.rec_on Hu (ap0111 (f u) Hv Hw Hx)

  definition ap010 (f : X → Πa, B a) (Hx : x = x') : f x ∼ f x' :=
  λa, eq.rec_on Hx idp

  definition ap0100 (f : X → Πa b, C a b) (Hx : x = x') : f x ∼2 f x' :=
  λa b, eq.rec_on Hx idp

  definition ap01000 (f : X → Πa b c, D a b c) (Hx : x = x') : f x ∼3 f x' :=
  λa b c, eq.rec_on Hx idp

  definition apD011 (f : Πa, B a → Z) (Ha : a = a') (Hb : (Ha ▹ b) = b')
      : f a b = f a' b' :=
  eq.rec_on Hb (eq.rec_on Ha idp)

  definition apD0111 (f : Πa b, C a b → Z) (Ha : a = a') (Hb : (Ha ▹ b) = b')
    (Hc : apD011 C Ha Hb ▹ c = c')
      : f a b c = f a' b' c' :=
  eq.rec_on Hc (eq.rec_on Hb (eq.rec_on Ha idp))

  definition apD01111 (f : Πa b c, D a b c → Z) (Ha : a = a') (Hb : (Ha ▹ b) = b')
    (Hc : apD011 C Ha Hb ▹ c = c') (Hd : apD0111 D Ha Hb Hc ▹ d = d')
      : f a b c d = f a' b' c' d' :=
  eq.rec_on Hd (eq.rec_on Hc (eq.rec_on Hb (eq.rec_on Ha idp)))

  definition apD100 {f g : Πa b, C a b} (p : f = g) : f ∼2 g :=
  λa b, apD10 (apD10 p a) b

  definition apD1000 {f g : Πa b c, D a b c} (p : f = g) : f ∼3 g :=
  λa b c, apD100 (apD10 p a) b c

  /- some properties of these variants of ap -/

  -- we only prove what is needed somewhere

  definition ap010_con (f : X → Πa, B a) (p : x = x') (q : x' = x'') :
    ap010 f (p ⬝ q) a = ap010 f p a ⬝ ap010 f q a :=
  eq.rec_on q (eq.rec_on p idp)

  definition ap010_ap (f : X → Πa, B a) (g : Y → X) (p : y = y') :
    ap010 f (ap g p) a = ap010 (λy, f (g y)) p a :=
  eq.rec_on p idp

  /- the following theorems are function extentionality for functions with multiple arguments -/

  definition eq_of_homotopy2 {f g : Πa b, C a b} (H : f ∼2 g) : f = g :=
  eq_of_homotopy (λa, eq_of_homotopy (H a))

  definition eq_of_homotopy3 {f g : Πa b c, D a b c} (H : f ∼3 g) : f = g :=
  eq_of_homotopy (λa, eq_of_homotopy2 (H a))

  definition eq_of_homotopy2_id (f : Πa b, C a b)
    : eq_of_homotopy2 (λa b, idpath (f a b)) = idpath f :=
  begin
    apply concat,
      {apply (ap (λx, eq_of_homotopy x)), apply eq_of_homotopy, intro a, apply eq_of_homotopy_id},
    apply eq_of_homotopy_id
  end

  definition eq_of_homotopy3_id (f : Πa b c, D a b c)
    : eq_of_homotopy3 (λa b c, idpath (f a b c)) = idpath f :=
  begin
    apply concat,
      {apply (ap (λx, eq_of_homotopy x)), apply eq_of_homotopy, intro a, apply eq_of_homotopy2_id},
    apply eq_of_homotopy_id
  end

end eq

open eq is_equiv
namespace funext
  definition is_equiv_apD100 [instance] (f g : Πa b, C a b) : is_equiv (@apD100 A B C f g) :=
  adjointify _
             eq_of_homotopy2
             begin
               intro H, esimp [apD100, eq_of_homotopy2, function.compose],
               apply eq_of_homotopy, intro a,
               apply concat, apply (ap (λx, @apD10 _ (λb : B a, _) _ _ (x a))), apply (retr apD10),
--TODO: remove implicit argument after #469 is closed
               apply (retr apD10)
             end
             begin
               intro p, cases p, apply eq_of_homotopy2_id
             end

  definition is_equiv_apD1000 [instance] (f g : Πa b c, D a b c)
    : is_equiv (@apD1000 A B C D f g) :=
  adjointify _
             eq_of_homotopy3
             begin
               intro H, apply eq_of_homotopy, intro a,
               apply concat,
                 {apply (ap (λx, @apD100 _ _ (λ(b : B a)(c : C a b), _) _ _ (x a))),
                   apply (retr apD10)},
--TODO: remove implicit argument after #469 is closed
               apply (@retr _ _ apD100 !is_equiv_apD100) --is explicit argument needed here?
             end
             begin
               intro p, cases p, apply eq_of_homotopy3_id
             end
end funext

namespace eq
  open funext
  local attribute funext.is_equiv_apD100 [instance]
  protected definition homotopy2.rec_on {f g : Πa b, C a b} {P : (f ∼2 g) → Type}
    (p : f ∼2 g) (H : Π(q : f = g), P (apD100 q)) : P p :=
  retr apD100 p ▹ H (eq_of_homotopy2 p)

  protected definition homotopy3.rec_on {f g : Πa b c, D a b c} {P : (f ∼3 g) → Type}
    (p : f ∼3 g) (H : Π(q : f = g), P (apD1000 q)) : P p :=
  retr apD1000 p ▹ H (eq_of_homotopy3 p)

  definition apD10_ap (f : X → Πa, B a) (p : x = x')
    : apD10 (ap f p) = ap010 f p :=
  eq.rec_on p idp

  definition eq_of_homotopy_ap010 (f : X → Πa, B a) (p : x = x')
    : eq_of_homotopy (ap010 f p) = ap f p :=
  inv_eq_of_eq !apD10_ap⁻¹

  definition ap_eq_ap_of_homotopy {f : X → Πa, B a} {p q : x = x'} (H : ap010 f p ∼ ap010 f q)
    : ap f p = ap f q :=
  calc
    ap f p = eq_of_homotopy (ap010 f p) : eq_of_homotopy_ap010
       ... = eq_of_homotopy (ap010 f q) : eq_of_homotopy H
       ... = ap f q                     : eq_of_homotopy_ap010

end eq
