Import macros

Definition TypeU := (Type U)
Definition TypeM := (Type M)

Definition SubstP {A : TypeU} {a b : A} (P : A → Bool) (H1 : P a) (H2 : a == b) : P b
:= Subst H1 H2.

Theorem Trivial : true
:= Refl true.

Theorem TrueNeFalse : not (true == false)
:= Trivial.

Theorem EM (a : Bool) : a ∨ ¬ a
:= Case (λ x, x ∨ ¬ x) Trivial Trivial a.

Theorem FalseElim (a : Bool) (H : false) : a
:= Case (λ x, x) Trivial H a.

Theorem Absurd {a : Bool} (H1 : a) (H2 : ¬ a) : false
:= MP H2 H1.

Theorem EqMP {a b : Bool} (H1 : a == b) (H2 : a) : b
:= Subst H2 H1.

Theorem DoubleNeg (a : Bool) : (¬ ¬ a) == a
:= Case (λ x, (¬ ¬ x) == x) Trivial Trivial a.

Theorem DoubleNegElim {a : Bool} (H : ¬ ¬ a) : a
:= EqMP (DoubleNeg a) H.

Theorem MT {a b : Bool} (H1 : a ⇒ b) (H2 : ¬ b) : ¬ a
:= assume H : a, Absurd (MP H1 H) H2.

Theorem Contrapos {a b : Bool} (H : a ⇒ b) : ¬ b ⇒ ¬ a
:= assume H1 : ¬ b, MT H H1.

Theorem AbsurdElim {a : Bool} (b : Bool) (H1 : a) (H2 : ¬ a) : b
:= FalseElim b (Absurd H1 H2).

Theorem NotImp1 {a b : Bool} (H : ¬ (a ⇒ b)) : a
:= DoubleNegElim
      (show ¬ ¬ a,
       assume H1 : ¬ a, Absurd (show a ⇒ b,     assume H2 : a, AbsurdElim b H2 H1)
                               (show ¬ (a ⇒ b), H)).

Theorem NotImp2 {a b : Bool} (H : ¬ (a ⇒ b)) : ¬ b
:= assume H1 : b, Absurd (show a ⇒ b, assume H2 : a, H1)
                         (show ¬ (a ⇒ b), H).

(* Remark: conjunction is defined as ¬ (a ⇒ ¬ b) in Lean *)

Theorem Conj {a b : Bool} (H1 : a) (H2 : b) : a ∧ b
:= assume H : a ⇒ ¬ b, Absurd H2 (MP H H1).

Theorem Conjunct1 {a b : Bool} (H : a ∧ b) : a
:= NotImp1 H.

Theorem Conjunct2 {a b : Bool} (H : a ∧ b) : b
:= DoubleNegElim (NotImp2 H).

(* Remark: disjunction is defined as ¬ a ⇒ b in Lean *)

Theorem Disj1 {a : Bool} (H : a) (b : Bool) : a ∨ b
:= assume H1 : ¬ a, AbsurdElim b H H1.

Theorem Disj2 {b : Bool} (a : Bool) (H : b) : a ∨ b
:= assume H1 : ¬ a, H.

Theorem ArrowToImplies {a b : Bool} (H : a → b) : a ⇒ b
:= assume H1 : a, H H1.

Theorem Resolve1 {a b : Bool} (H1 : a ∨ b) (H2 : ¬ a) : b
:= MP H1 H2.

Theorem DisjCases {a b c : Bool} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= DoubleNegElim
     (assume H : ¬ c,
        Absurd (show c, H3 (show b, Resolve1 H1 (show ¬ a, (MT (ArrowToImplies H2) H))))
               H)

Theorem Refute {a : Bool} (H : ¬ a → false) : a
:= DisjCases (EM a) (λ H1 : a, H1) (λ H1 : ¬ a, FalseElim a (H H1)).

Theorem Symm {A : TypeU} {a b : A} (H : a == b) : b == a
:= Subst (Refl a) H.

Theorem Trans {A : TypeU} {a b c : A} (H1 : a == b) (H2 : b == c) : a == c
:= Subst H1 H2.

Theorem EqTElim {a : Bool} (H : a == true) : a
:= EqMP (Symm H) Trivial.

Theorem EqTIntro {a : Bool} (H : a) : a == true
:= ImpAntisym (assume H1 : a, Trivial)
              (assume H2 : true, H).

Theorem Congr1 {A : TypeU} {B : A → TypeU} {f g : Π x : A, B x} (a : A) (H : f == g) : f a == g a
:= SubstP (fun h : (Π x : A, B x), f a == h a) (Refl (f a)) H.

(*
Remark: we must use heterogeneous equality in the following theorem because the types of (f a) and (f b)
are not "definitionally equal". They are (B a) and (B b).
They are provably equal, we just have to apply Congr1.
*)

Theorem Congr2 {A : TypeU} {B : A → TypeU} {a b : A} (f : Π x : A, B x) (H : a == b) : f a == f b
:= SubstP (fun x : A, f a == f x) (Refl (f a)) H.

(*
Remark: like the previous theorem we use heterogeneous equality. We cannot use Trans theorem
because the types are not definitionally equal.
*)

Theorem Congr {A : TypeU} {B : A → TypeU} {f g : Π x : A, B x} {a b : A} (H1 : f == g) (H2 : a == b) : f a == g b
:= HTrans (Congr2 f H2) (Congr1 b H1).

Theorem ForallElim {A : TypeU} {P : A → Bool} (H : Forall A P) (a : A) : P a
:= EqTElim (Congr1 a H).

Theorem ForallIntro {A : TypeU} {P : A → Bool} (H : Π x : A, P x) : Forall A P
:= Trans (Symm (Eta P))
         (Abst (λ x, EqTIntro (H x))).

(* Remark: the existential is defined as (¬ (forall x : A, ¬ P x)) *)

Theorem ExistsElim {A : TypeU} {P : A → Bool} {B : Bool} (H1 : Exists A P) (H2 : Π (a : A) (H : P a), B) : B
:= Refute (λ R : ¬ B,
             Absurd (ForallIntro (λ a : A, MT (assume H : P a, H2 a H) R))
                    H1).

Theorem ExistsIntro {A : TypeU} {P : A → Bool} (a : A) (H : P a) : Exists A P
:= assume H1 : (∀ x : A, ¬ P x),
      Absurd H (ForallElim H1 a).

(*
At this point, we have proved the theorems we need using the
definitions of forall, exists, and, or, =>, not.  We mark (some of)
them as opaque. Opaque definitions improve performance, and
effectiveness of Lean's elaborator.
*)

SetOpaque implies true.
SetOpaque iff     true.
SetOpaque not     true.
SetOpaque or      true.
SetOpaque and     true.
SetOpaque forall  true.

Theorem OrComm (a b : Bool) : (a ∨ b) == (b ∨ a)
:= ImpAntisym (assume H, DisjCases H (λ H1, Disj2 b H1) (λ H2, Disj1 H2 a))
              (assume H, DisjCases H (λ H1, Disj2 a H1) (λ H2, Disj1 H2 b)).


Theorem OrAssoc (a b c : Bool) : ((a ∨ b) ∨ c) == (a ∨ (b ∨ c))
:= ImpAntisym (assume H : (a ∨ b) ∨ c,
                      DisjCases H (λ H1 : a ∨ b, DisjCases H1 (λ Ha : a, Disj1 Ha (b ∨ c)) (λ Hb : b, Disj2 a (Disj1 Hb c)))
                                  (λ Hc : c, Disj2 a (Disj2 b Hc)))
              (assume H : a ∨ (b ∨ c),
                      DisjCases H (λ Ha : a, (Disj1 (Disj1 Ha b) c))
                                  (λ H1 : b ∨ c, DisjCases H1 (λ Hb : b, Disj1 (Disj2 a Hb) c)
                                                              (λ Hc : c, Disj2 (a ∨ b) Hc))).

Theorem OrId (a : Bool) : (a ∨ a) == a
:= ImpAntisym (assume H, DisjCases H (λ H1, H1) (λ H2, H2))
              (assume H, Disj1 H a).

Theorem OrRhsFalse (a : Bool) : (a ∨ false) == a
:= ImpAntisym (assume H, DisjCases H (λ H1, H1) (λ H2, FalseElim a H2))
              (assume H, Disj1 H false).

Theorem OrLhsFalse (a : Bool) : (false ∨ a) == a
:= Trans (OrComm false a) (OrRhsFalse a).

Theorem OrLhsTrue (a : Bool) : (true ∨ a) == true
:= EqTIntro (Case (λ x : Bool, true ∨ x) Trivial Trivial a).

Theorem OrRhsTrue (a : Bool) : (a ∨ true) == true
:= Trans (OrComm a true) (OrLhsTrue a).

Theorem OrAnotA (a : Bool) : (a ∨ ¬ a) == true
:= EqTIntro (EM a).

Theorem AndComm (a b : Bool) : (a ∧ b) == (b ∧ a)
:= ImpAntisym (assume H, Conj (Conjunct2 H) (Conjunct1 H))
              (assume H, Conj (Conjunct2 H) (Conjunct1 H)).

Theorem AndId (a : Bool) : (a ∧ a) == a
:= ImpAntisym (assume H, Conjunct1 H)
              (assume H, Conj H H).

Theorem AndAssoc (a b c : Bool) : ((a ∧ b) ∧ c) == (a ∧ (b ∧ c))
:= ImpAntisym (assume H, Conj (Conjunct1 (Conjunct1 H)) (Conj (Conjunct2 (Conjunct1 H)) (Conjunct2 H)))
              (assume H, Conj (Conj (Conjunct1 H) (Conjunct1 (Conjunct2 H))) (Conjunct2 (Conjunct2 H))).

Theorem AndRhsTrue (a : Bool) : (a ∧ true) == a
:= ImpAntisym (assume H : a ∧ true,  Conjunct1 H)
              (assume H : a,         Conj H Trivial).

Theorem AndLhsTrue (a : Bool) : (true ∧ a) == a
:= Trans (AndComm true a) (AndRhsTrue a).

Theorem AndRhsFalse (a : Bool) : (a ∧ false) == false
:= ImpAntisym (assume H, Conjunct2 H)
              (assume H, FalseElim (a ∧ false) H).

Theorem AndLhsFalse (a : Bool) : (false ∧ a) == false
:= Trans (AndComm false a) (AndRhsFalse a).

Theorem AndAnotA (a : Bool) : (a ∧ ¬ a) == false
:= ImpAntisym (assume H, Absurd (Conjunct1 H) (Conjunct2 H))
              (assume H, FalseElim (a ∧ ¬ a) H).

Theorem NotTrue : (¬ true) == false
:= Trivial

Theorem NotFalse : (¬ false) == true
:= Trivial

Theorem NotAnd (a b : Bool) : (¬ (a ∧ b)) == (¬ a ∨ ¬ b)
:= Case (λ x, (¬ (x ∧ b)) == (¬ x ∨ ¬ b))
        (Case (λ y, (¬ (true ∧ y)) == (¬ true ∨ ¬ y))   Trivial Trivial b)
        (Case (λ y, (¬ (false ∧ y)) == (¬ false ∨ ¬ y)) Trivial Trivial b)
        a

Theorem NotOr (a b : Bool) : (¬ (a ∨ b)) == (¬ a ∧ ¬ b)
:= Case (λ x, (¬ (x ∨ b)) == (¬ x ∧ ¬ b))
        (Case (λ y, (¬ (true ∨ y)) == (¬ true ∧ ¬ y))   Trivial Trivial b)
        (Case (λ y, (¬ (false ∨ y)) == (¬ false ∧ ¬ y)) Trivial Trivial b)
        a

Theorem NotEq (a b : Bool) : (¬ (a == b)) == ((¬ a) == b)
:= Case (λ x, (¬ (x == b)) == ((¬ x) == b))
        (Case (λ y, (¬ (true == y)) == ((¬ true) == y)) Trivial Trivial b)
        (Case (λ y, (¬ (false == y)) == ((¬ false) == y)) Trivial Trivial b)
        a

Theorem NotImp (a b : Bool) : (¬ (a ⇒ b)) == (a ∧ ¬ b)
:= Case (λ x, (¬ (x ⇒ b)) == (x ∧ ¬ b))
        (Case (λ y, (¬ (true ⇒ y)) == (true ∧ ¬ y)) Trivial Trivial b)
        (Case (λ y, (¬ (false ⇒ y)) == (false ∧ ¬ y)) Trivial Trivial b)
        a

Theorem NotCongr {a b : Bool} (H : a == b) : (¬ a) == (¬ b)
:= Congr2 not H.

Theorem ForallEqIntro {A : (Type U)} {P Q : A → Bool} (H : Pi x : A, P x == Q x) : (∀ x : A, P x) == (∀ x : A, Q x)
:= Congr2 (Forall A) (Abst H).

Theorem ExistsEqIntro {A : (Type U)} {P Q : A → Bool} (H : Pi x : A, P x == Q x) : (∃ x : A, P x) == (∃ x : A, Q x)
:= Congr2 (Exists A) (Abst H).

Theorem NotForall (A : (Type U)) (P : A → Bool) : (¬ (∀ x : A, P x)) == (∃ x : A, ¬ (P x))
:= let L1 : (¬ (∀ x : A, ¬ (¬ (P x)))) == (∃ x : A, (¬ (P x))) := Refl (∃ x : A, ¬ (P x)),
       L2 : (¬ (∀ x : A, P x)) == (¬ (∀ x : A, ¬ (¬ (P x)))) :=
            NotCongr (ForallEqIntro (λ x : A, (Symm (DoubleNeg (P x)))))
   in Trans L2 L1.

Theorem NotExists (A : (Type U)) (P : A → Bool) : (¬ (∃ x : A, P x)) == (∀ x : A, ¬ (P x))
:= let L1 : (¬ (∃ x : A, P x)) == (¬ (¬ (∀ x : A, ¬ (P x)))) := Refl (¬ (∃ x : A, P x)),
       L2 : (¬ (¬ (∀ x : A, ¬ (P x)))) == (∀ x : A, ¬ (P x)) := DoubleNeg (∀ x : A, ¬ (P x))
   in Trans L1 L2.
