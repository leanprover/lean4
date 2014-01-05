Import macros

Universe M : 512.
Universe U : M+512.

Variable Bool : Type.
-- The following builtin declarations can be removed as soon as Lean supports inductive datatypes and match expressions.
Builtin true : Bool.
Builtin false : Bool.
Builtin if {A : (Type U)} : Bool → A → A → A.

Definition TypeU := (Type U)
Definition TypeM := (Type M)

Definition implies (a b : Bool) : Bool
:= if a b true.

Infixr 25 => : implies.
Infixr 25 ⇒ : implies.

Definition iff (a b : Bool) : Bool
:= a == b.

Infixr 25 <=> : iff.
Infixr 25 ⇔ : iff.

Definition not (a : Bool) : Bool
:= if a false true.

Notation 40 ¬ _ : not.

Definition or (a b : Bool) : Bool
:= ¬ a ⇒ b.

Infixr 30 || : or.
Infixr 30 \/ : or.
Infixr 30 ∨  : or.

Definition and (a b : Bool) : Bool
:= ¬ (a ⇒ ¬ b).

Infixr 35 && : and.
Infixr 35 /\ : and.
Infixr 35 ∧  : and.

-- Forall is a macro for the identifier forall, we use that
--   because the Lean parser has the builtin syntax sugar:
--      forall x : T, P x
--   for
--      (forall T (fun x : T, P x))
Definition Forall (A : TypeU) (P : A → Bool) : Bool
:= P == (λ x : A, true).

Definition Exists (A : TypeU) (P : A → Bool) : Bool
:= ¬ (Forall A (λ x : A, ¬ (P x))).

Definition eq {A : TypeU} (a b : A) : Bool
:= a == b.

Infix 50 = : eq.

Definition neq {A : TypeU} (a b : A) : Bool
:= ¬ (a == b).

Infix 50 ≠ : neq.

Axiom MP {a b : Bool} (H1 : a ⇒ b) (H2 : a) : b.

Axiom Discharge {a b : Bool} (H : a → b) : a ⇒ b.

Axiom Case (P : Bool → Bool) (H1 : P true) (H2 : P false) (a : Bool) : P a.

Axiom Refl {A : TypeU} (a : A) : a == a.

Axiom Subst {A : TypeU} {a b : A} {P : A → Bool} (H1 : P a) (H2 : a == b) : P b.

Definition SubstP {A : TypeU} {a b : A} (P : A → Bool) (H1 : P a) (H2 : a == b) : P b
:= Subst H1 H2.

Axiom Eta {A : TypeU} {B : A → TypeU} (f : Π x : A, B x) : (λ x : A, f x) == f.

Axiom ImpAntisym {a b : Bool} (H1 : a ⇒ b) (H2 : b ⇒ a) : a == b.

Axiom Abst {A : TypeU} {B : A → TypeU} {f g : Π x : A, B x} (H : Π x : A, f x == g x) : f == g.

Axiom HSymm {A B : TypeU} {a : A} {b : B} (H : a == b) : b == a.

Axiom HTrans {A B C : TypeU} {a : A} {b : B} {c : C} (H1 : a == b) (H2 : b == c) : a == c.

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

-- Assume is a 'macro' that expands into a Discharge

Theorem ImpTrans {a b c : Bool} (H1 : a ⇒ b) (H2 : b ⇒ c) : a ⇒ c
:= Assume Ha, MP H2 (MP H1 Ha).

Theorem ImpEqTrans {a b c : Bool} (H1 : a ⇒ b) (H2 : b == c) : a ⇒ c
:= Assume Ha, EqMP H2 (MP H1 Ha).

Theorem EqImpTrans {a b c : Bool} (H1 : a == b) (H2 : b ⇒ c) : a ⇒ c
:= Assume Ha, MP H2 (EqMP H1 Ha).

Theorem DoubleNeg (a : Bool) : (¬ ¬ a) == a
:= Case (λ x, (¬ ¬ x) == x) Trivial Trivial a.

Theorem DoubleNegElim {a : Bool} (H : ¬ ¬ a) : a
:= EqMP (DoubleNeg a) H.

Theorem MT {a b : Bool} (H1 : a ⇒ b) (H2 : ¬ b) : ¬ a
:= Assume H : a, Absurd (MP H1 H) H2.

Theorem Contrapos {a b : Bool} (H : a ⇒ b) : ¬ b ⇒ ¬ a
:= Assume H1 : ¬ b, MT H H1.

Theorem AbsurdElim {a : Bool} (b : Bool) (H1 : a) (H2 : ¬ a) : b
:= FalseElim b (Absurd H1 H2).

Theorem NotImp1 {a b : Bool} (H : ¬ (a ⇒ b)) : a
:= DoubleNegElim
      (show ¬ ¬ a,
       Assume H1 : ¬ a, Absurd (show a ⇒ b,     Assume H2 : a, AbsurdElim b H2 H1)
                               (show ¬ (a ⇒ b), H)).

Theorem NotImp2 {a b : Bool} (H : ¬ (a ⇒ b)) : ¬ b
:= Assume H1 : b, Absurd (show a ⇒ b, Assume H2 : a, H1)
                         (show ¬ (a ⇒ b), H).

-- Remark: conjunction is defined as ¬ (a ⇒ ¬ b) in Lean

Theorem Conj {a b : Bool} (H1 : a) (H2 : b) : a ∧ b
:= Assume H : a ⇒ ¬ b, Absurd H2 (MP H H1).

Theorem Conjunct1 {a b : Bool} (H : a ∧ b) : a
:= NotImp1 H.

Theorem Conjunct2 {a b : Bool} (H : a ∧ b) : b
:= DoubleNegElim (NotImp2 H).

-- Remark: disjunction is defined as ¬ a ⇒ b in Lean

Theorem Disj1 {a : Bool} (H : a) (b : Bool) : a ∨ b
:= Assume H1 : ¬ a, AbsurdElim b H H1.

Theorem Disj2 {b : Bool} (a : Bool) (H : b) : a ∨ b
:= Assume H1 : ¬ a, H.

Theorem ArrowToImplies {a b : Bool} (H : a → b) : a ⇒ b
:= Assume H1 : a, H H1.

Theorem Resolve1 {a b : Bool} (H1 : a ∨ b) (H2 : ¬ a) : b
:= MP H1 H2.

Theorem DisjCases {a b c : Bool} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= DoubleNegElim
     (Assume H : ¬ c,
        Absurd (show c, H3 (show b, Resolve1 H1 (show ¬ a, (MT (ArrowToImplies H2) H))))
               H)

Theorem Refute {a : Bool} (H : ¬ a → false) : a
:= DisjCases (EM a) (λ H1 : a, H1) (λ H1 : ¬ a, FalseElim a (H H1)).

Theorem Symm {A : TypeU} {a b : A} (H : a == b) : b == a
:= Subst (Refl a) H.

Theorem NeSymm {A : TypeU} {a b : A} (H : a ≠ b) : b ≠ a
:= Assume H1 : b = a, MP H (Symm H1).

Theorem EqNeTrans {A : TypeU} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c
:= Subst H2 (Symm H1).

Theorem NeEqTrans {A : TypeU} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c
:= Subst H1 H2.

Theorem Trans {A : TypeU} {a b c : A} (H1 : a == b) (H2 : b == c) : a == c
:= Subst H1 H2.

Theorem EqTElim {a : Bool} (H : a == true) : a
:= EqMP (Symm H) Trivial.

Theorem EqTIntro {a : Bool} (H : a) : a == true
:= ImpAntisym (Assume H1 : a, Trivial)
              (Assume H2 : true, H).

Theorem Congr1 {A : TypeU} {B : A → TypeU} {f g : Π x : A, B x} (a : A) (H : f == g) : f a == g a
:= SubstP (fun h : (Π x : A, B x), f a == h a) (Refl (f a)) H.

-- Remark: we must use heterogeneous equality in the following theorem because the types of (f a) and (f b)
-- are not "definitionally equal". They are (B a) and (B b).
-- They are provably equal, we just have to apply Congr1.

Theorem Congr2 {A : TypeU} {B : A → TypeU} {a b : A} (f : Π x : A, B x) (H : a == b) : f a == f b
:= SubstP (fun x : A, f a == f x) (Refl (f a)) H.

-- Remark: like the previous theorem we use heterogeneous equality. We cannot use Trans theorem
-- because the types are not definitionally equal.

Theorem Congr {A : TypeU} {B : A → TypeU} {f g : Π x : A, B x} {a b : A} (H1 : f == g) (H2 : a == b) : f a == g b
:= HTrans (Congr2 f H2) (Congr1 b H1).

Theorem ForallElim {A : TypeU} {P : A → Bool} (H : Forall A P) (a : A) : P a
:= EqTElim (Congr1 a H).

Theorem ForallIntro {A : TypeU} {P : A → Bool} (H : Π x : A, P x) : Forall A P
:= Trans (Symm (Eta P))
         (Abst (λ x, EqTIntro (H x))).

-- Remark: the existential is defined as (¬ (forall x : A, ¬ P x))

Theorem ExistsElim {A : TypeU} {P : A → Bool} {B : Bool} (H1 : Exists A P) (H2 : Π (a : A) (H : P a), B) : B
:= Refute (λ R : ¬ B,
             Absurd (ForallIntro (λ a : A, MT (Assume H : P a, H2 a H) R))
                    H1).

Theorem ExistsIntro {A : TypeU} {P : A → Bool} (a : A) (H : P a) : Exists A P
:= Assume H1 : (∀ x : A, ¬ P x),
      Absurd H (ForallElim H1 a).

-- At this point, we have proved the theorems we need using the
-- definitions of forall, exists, and, or, =>, not.  We mark (some of)
-- them as opaque. Opaque definitions improve performance, and
-- effectiveness of Lean's elaborator.

SetOpaque implies true.
SetOpaque not     true.
SetOpaque or      true.
SetOpaque and     true.
SetOpaque forall  true.

Theorem OrComm (a b : Bool) : (a ∨ b) == (b ∨ a)
:= ImpAntisym (Assume H, DisjCases H (λ H1, Disj2 b H1) (λ H2, Disj1 H2 a))
              (Assume H, DisjCases H (λ H1, Disj2 a H1) (λ H2, Disj1 H2 b)).


Theorem OrAssoc (a b c : Bool) : ((a ∨ b) ∨ c) == (a ∨ (b ∨ c))
:= ImpAntisym (Assume H : (a ∨ b) ∨ c,
                      DisjCases H (λ H1 : a ∨ b, DisjCases H1 (λ Ha : a, Disj1 Ha (b ∨ c)) (λ Hb : b, Disj2 a (Disj1 Hb c)))
                                  (λ Hc : c, Disj2 a (Disj2 b Hc)))
              (Assume H : a ∨ (b ∨ c),
                      DisjCases H (λ Ha : a, (Disj1 (Disj1 Ha b) c))
                                  (λ H1 : b ∨ c, DisjCases H1 (λ Hb : b, Disj1 (Disj2 a Hb) c)
                                                              (λ Hc : c, Disj2 (a ∨ b) Hc))).

Theorem OrId (a : Bool) : (a ∨ a) == a
:= ImpAntisym (Assume H, DisjCases H (λ H1, H1) (λ H2, H2))
              (Assume H, Disj1 H a).

Theorem OrRhsFalse (a : Bool) : (a ∨ false) == a
:= ImpAntisym (Assume H, DisjCases H (λ H1, H1) (λ H2, FalseElim a H2))
              (Assume H, Disj1 H false).

Theorem OrLhsFalse (a : Bool) : (false ∨ a) == a
:= Trans (OrComm false a) (OrRhsFalse a).

Theorem OrLhsTrue (a : Bool) : (true ∨ a) == true
:= EqTIntro (Case (λ x : Bool, true ∨ x) Trivial Trivial a).

Theorem OrRhsTrue (a : Bool) : (a ∨ true) == true
:= Trans (OrComm a true) (OrLhsTrue a).

Theorem OrAnotA (a : Bool) : (a ∨ ¬ a) == true
:= EqTIntro (EM a).

Theorem AndComm (a b : Bool) : (a ∧ b) == (b ∧ a)
:= ImpAntisym (Assume H, Conj (Conjunct2 H) (Conjunct1 H))
              (Assume H, Conj (Conjunct2 H) (Conjunct1 H)).

Theorem AndId (a : Bool) : (a ∧ a) == a
:= ImpAntisym (Assume H, Conjunct1 H)
              (Assume H, Conj H H).

Theorem AndAssoc (a b c : Bool) : ((a ∧ b) ∧ c) == (a ∧ (b ∧ c))
:= ImpAntisym (Assume H, Conj (Conjunct1 (Conjunct1 H)) (Conj (Conjunct2 (Conjunct1 H)) (Conjunct2 H)))
              (Assume H, Conj (Conj (Conjunct1 H) (Conjunct1 (Conjunct2 H))) (Conjunct2 (Conjunct2 H))).

Theorem AndRhsTrue (a : Bool) : (a ∧ true) == a
:= ImpAntisym (Assume H : a ∧ true,  Conjunct1 H)
              (Assume H : a,         Conj H Trivial).

Theorem AndLhsTrue (a : Bool) : (true ∧ a) == a
:= Trans (AndComm true a) (AndRhsTrue a).

Theorem AndRhsFalse (a : Bool) : (a ∧ false) == false
:= ImpAntisym (Assume H, Conjunct2 H)
              (Assume H, FalseElim (a ∧ false) H).

Theorem AndLhsFalse (a : Bool) : (false ∧ a) == false
:= Trans (AndComm false a) (AndRhsFalse a).

Theorem AndAnotA (a : Bool) : (a ∧ ¬ a) == false
:= ImpAntisym (Assume H, Absurd (Conjunct1 H) (Conjunct2 H))
              (Assume H, FalseElim (a ∧ ¬ a) H).

Theorem NotTrue : (¬ true) == false
:= Trivial

Theorem NotFalse : (¬ false) == true
:= Trivial

Theorem NotAnd (a b : Bool) : (¬ (a ∧ b)) == (¬ a ∨ ¬ b)
:= Case (λ x, (¬ (x ∧ b)) == (¬ x ∨ ¬ b))
        (Case (λ y, (¬ (true ∧ y)) == (¬ true ∨ ¬ y))   Trivial Trivial b)
        (Case (λ y, (¬ (false ∧ y)) == (¬ false ∨ ¬ y)) Trivial Trivial b)
        a

Theorem NotAndElim {a b : Bool} (H : ¬ (a ∧ b)) : ¬ a ∨ ¬ b
:= EqMP (NotAnd a b) H.

Theorem NotOr (a b : Bool) : (¬ (a ∨ b)) == (¬ a ∧ ¬ b)
:= Case (λ x, (¬ (x ∨ b)) == (¬ x ∧ ¬ b))
        (Case (λ y, (¬ (true ∨ y)) == (¬ true ∧ ¬ y))   Trivial Trivial b)
        (Case (λ y, (¬ (false ∨ y)) == (¬ false ∧ ¬ y)) Trivial Trivial b)
        a

Theorem NotOrElim {a b : Bool} (H : ¬ (a ∨ b)) : ¬ a ∧ ¬ b
:= EqMP (NotOr a b) H.

Theorem NotEq (a b : Bool) : (¬ (a == b)) == ((¬ a) == b)
:= Case (λ x, (¬ (x == b)) == ((¬ x) == b))
        (Case (λ y, (¬ (true == y)) == ((¬ true) == y)) Trivial Trivial b)
        (Case (λ y, (¬ (false == y)) == ((¬ false) == y)) Trivial Trivial b)
        a

Theorem NotEqElim {a b : Bool} (H : ¬ (a == b)) : (¬ a) == b
:= EqMP (NotEq a b) H.

Theorem NotImp (a b : Bool) : (¬ (a ⇒ b)) == (a ∧ ¬ b)
:= Case (λ x, (¬ (x ⇒ b)) == (x ∧ ¬ b))
        (Case (λ y, (¬ (true ⇒ y)) == (true ∧ ¬ y)) Trivial Trivial b)
        (Case (λ y, (¬ (false ⇒ y)) == (false ∧ ¬ y)) Trivial Trivial b)
        a

Theorem NotImpElim {a b : Bool} (H : ¬ (a ⇒ b)) : a ∧ ¬ b
:= EqMP (NotImp a b) H.

Theorem NotCongr {a b : Bool} (H : a == b) : (¬ a) == (¬ b)
:= Congr2 not H.

Theorem ForallEqIntro {A : (Type U)} {P Q : A → Bool} (H : Pi x : A, P x == Q x) : (∀ x : A, P x) == (∀ x : A, Q x)
:= Congr2 (Forall A) (Abst H).

Theorem ExistsEqIntro {A : (Type U)} {P Q : A → Bool} (H : Pi x : A, P x == Q x) : (∃ x : A, P x) == (∃ x : A, Q x)
:= Congr2 (Exists A) (Abst H).

Theorem NotForall (A : (Type U)) (P : A → Bool) : (¬ (∀ x : A, P x)) == (∃ x : A, ¬ P x)
:= let L1 : (¬ ∀ x : A, ¬ ¬ P x) == (∃ x : A, ¬ P x) := Refl (∃ x : A, ¬ P x),
       L2 : (¬ ∀ x : A, P x) == (¬ ∀ x : A, ¬ ¬ P x) :=
            NotCongr (ForallEqIntro (λ x : A, (Symm (DoubleNeg (P x)))))
   in Trans L2 L1.

Theorem NotForallElim {A : (Type U)} {P : A → Bool} (H : ¬ (∀ x : A, P x)) : ∃ x : A, ¬ P x
:= EqMP (NotForall A P) H.

Theorem NotExists (A : (Type U)) (P : A → Bool) : (¬ ∃ x : A, P x) == (∀ x : A, ¬ P x)
:= let L1 : (¬ ∃ x : A, P x) == (¬ ¬ ∀ x : A, ¬ P x) := Refl (¬ ∃ x : A, P x),
       L2 : (¬ ¬ ∀ x : A, ¬ P x) == (∀ x : A, ¬ P x) := DoubleNeg (∀ x : A, ¬ P x)
   in Trans L1 L2.

Theorem NotExistsElim {A : (Type U)} {P : A → Bool} (H : ¬ ∃ x : A, P x) : ∀ x : A, ¬ P x
:= EqMP (NotExists A P) H.

Theorem UnfoldExists1 {A : TypeU} {P : A → Bool} (a : A) (H : ∃ x : A, P x) : P a ∨ (∃ x : A, x ≠ a ∧ P x)
:= ExistsElim H
     (λ (w : A) (H1 : P w),
        DisjCases (EM (w = a))
          (λ Heq : w = a, Disj1 (Subst H1 Heq) (∃ x : A, x ≠ a ∧ P x))
          (λ Hne : w ≠ a, Disj2 (P a) (ExistsIntro w (Conj Hne H1)))).

Theorem UnfoldExists2 {A : TypeU} {P : A → Bool} (a : A) (H : P a ∨ (∃ x : A, x ≠ a ∧ P x)) : ∃ x : A, P x
:= DisjCases H
      (λ H1 : P a, ExistsIntro a H1)
      (λ H2 : (∃ x : A, x ≠ a ∧ P x),
          ExistsElim H2
               (λ (w : A) (Hw : w ≠ a ∧ P w),
                  ExistsIntro w (Conjunct2 Hw))).

Theorem UnfoldExists {A : TypeU} (P : A → Bool) (a : A) : (∃ x : A, P x) = (P a ∨ (∃ x : A, x ≠ a ∧ P x))
:= ImpAntisym (Assume H : (∃ x : A, P x), UnfoldExists1 a H)
              (Assume H : (P a ∨ (∃ x : A, x ≠ a ∧ P x)), UnfoldExists2 a H).

SetOpaque exists true.
