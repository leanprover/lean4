prelude
-- Porting Vladimir's file to Lean
notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r

inductive empty : Type
inductive unit : Type :=
tt : unit
definition tt := @unit.tt
inductive nat : Type :=
| O : nat
| S : nat → nat

inductive paths {A : Type} (a : A) : A → Type :=
idpath : paths a a
definition idpath := @paths.idpath

inductive sum (A : Type) (B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B

definition coprod := sum
definition ii1fun {A : Type} (B : Type) (a : A) := sum.inl B a
definition ii2fun (A : Type) {B : Type} (b : B) := sum.inr A b
definition ii1 {A : Type} {B : Type} (a : A) := sum.inl B a
definition ii2 {A : Type} {B : Type} (b : B) := sum.inl A b

inductive total2 {T: Type} (P: T → Type) : Type :=
tpair : Π (t : T) (tp : P t), total2 P
definition tpair := @total2.tpair

definition pr1 {T : Type} {P : T → Type} (tp : total2 P) : T
:= total2.rec (λ a b, a) tp
definition pr2 {T : Type} {P : T → Type} (tp : total2 P) : P (pr1 tp)
:= total2.rec (λ a b, b) tp

inductive Phant (T : Type) : Type :=
phant : Phant T

definition fromempty {X : Type} : empty → X
:= λe, empty.rec (λe, X) e

definition tounit {X : Type} : X → unit
:= λx, tt

definition termfun {X : Type} (x : X) : unit → X
:= λt, x

definition idfun (T : Type) := λt : T, t

definition funcomp {X : Type} {Y : Type} {Z : Type} (f : X → Y) (g : Y → Z)
:= λx, g (f x)

infixl `∘`:60 := funcomp

definition iteration {T : Type} (f : T → T) (n : nat) : T → T
:= nat.rec (idfun T) (λ m fm, funcomp fm f) n

definition adjev {X : Type} {Y : Type} (x : X) (f : X → Y) := f x

definition adjev2 {X : Type} {Y : Type} (phi : ((X → Y) → Y ) → Y ) : X → Y
:= λx, phi (λf, f x)

definition dirprod (X : Type) (Y : Type) := total2 (λ x : X, Y)
definition dirprodpair {X : Type} {Y : Type} := @tpair _ (λ x : X, Y)
definition dirprodadj {X : Type} {Y : Type} {Z : Type} (f : dirprod X Y → Z ) : X → Y → Z
:=  λx y, f (dirprodpair x y)
definition dirprodf {X : Type} {Y : Type} {X' : Type} {Y' : Type} (f : X → Y) (f' : X' → Y')  (xx' : dirprod X X') : dirprod Y Y'
:= dirprodpair (f (pr1 xx')) (f' (pr2 xx'))
definition ddualand {X : Type} {Y : Type} {P : Type} (xp : (X → P) → P) (yp : (Y → P) → P) : (dirprod X Y → P) → P
:= λ X0,
   let int1 := λ (ypp : (Y → P) → P) (x : X), yp (λ y : Y, X0 (dirprodpair x y)) in
   xp (int1 yp)

definition neg (X : Type) : Type := X → empty
definition negf {X : Type} {Y : Type} (f : X → Y) : neg Y → neg X
:= λ (phi : Y → empty) (x : X), phi (f x)

definition dneg (X : Type) : Type := (X → empty) → empty
definition dnegf {X : Type} {Y : Type} (f : X → Y) : dneg X → dneg Y
:= negf (negf f)

definition todneg (X : Type) : X → dneg X
:= adjev

definition dnegnegtoneg {X : Type} : dneg (neg X) → neg X
:= adjev2

lemma dneganddnegl1 {X : Type} {Y : Type} (dnx : dneg X) (dny : dneg Y) : neg (X → neg Y)
:= take X2 : X → neg Y,
   have X3 : dneg X → neg Y, from
     take xx : dneg X, dnegnegtoneg (dnegf X2 xx),
   dny (X3 dnx)

definition logeq (X : Type) (Y : Type) := dirprod (X → Y) (Y → X)
infix `<->`:25 := logeq
infix `↔`:25 := logeq

definition logeqnegs {X : Type} {Y : Type} (l : X ↔ Y) : (neg X) ↔ (neg Y)
:= dirprodpair (negf (pr2 l)) (negf (pr1 l))

infix `=`:50      := paths

definition pathscomp0 {X : Type} {a b c : X} (e1 : a = b) (e2 : b = c) : a = c
:= paths.rec e1 e2

definition pathscomp0rid {X : Type} {a b : X} (e1 : a = b) : pathscomp0 e1 (idpath b) = e1
:= idpath _

definition pathsinv0 {X : Type} {a b : X} (e : a = b) : b = a
:= paths.rec (idpath _) e

definition transport {A : Type} {a b : A} {P : A → Type} (H1 : a = b) (H2 : P a) : P b
:= paths.rec H2 H1

infixr `▸`:75     := transport
infixr `⬝`:75     := pathscomp0
postfix `⁻¹`:100  := pathsinv0

definition idinv {X : Type} (x : X) : (idpath x)⁻¹ = idpath x
:= idpath (idpath x)

definition idtrans {A : Type} (x : A) : (idpath x) ⬝ (idpath x) = (idpath x)
:= idpath (idpath x)

definition pathsinv0l {X : Type} {a b : X} (e : a = b) : e⁻¹ ⬝ e = idpath b
:= paths.rec (idinv a⁻¹ ▸ idtrans a) e

definition pathsinv0r {A : Type} {x y : A} (p : x = y) : p⁻¹ ⬝ p = idpath y
:= paths.rec (idinv x⁻¹ ▸ idtrans x) p

definition pathsinv0inv0 {A : Type} {x y : A} (p : x = y) : (p⁻¹)⁻¹ = p
:= paths.rec (idpath (idpath x)) p

definition pathsdirprod {X : Type} {Y : Type} {x1 x2 : X} {y1 y2 : Y} (ex : x1 = x2) (ey : y1 = y2 ) : dirprodpair x1 y1 =  dirprodpair x2 y2
:= ex ▸ ey ▸ idpath (dirprodpair x1 y1)

definition maponpaths {T1 : Type} {T2 : Type} (f : T1 → T2) {t1 t2 : T1} (e : t1 = t2) : f t1 = f t2
:= e ▸ idpath (f t1)

definition ap {T1 : Type} {T2 : Type} := @maponpaths T1 T2

definition maponpathscomp0 {X : Type} {Y : Type} {x y z : X} (f : X → Y) (p : x = y) (q : y = z) : ap f (p ⬝ q) = (ap f p) ⬝ (ap f q)
:= paths.rec (idpath _) q

definition maponpathsinv0 {X : Type} {Y : Type} (f : X → Y) {x1 x2 : X} (e : x1 = x2 ) : ap f (e⁻¹) = (ap f e)⁻¹
:= paths.rec (idpath _) e

lemma maponpathsidfun {X : Type} {x x' : X} (e : x = x') : ap (idfun X) e = e
:= paths.rec (idpath _) e

lemma maponpathscomp {X : Type} {Y : Type} {Z : Type} {x x' : X} (f : X → Y) (g : Y → Z) (e : x = x') : ap g (ap f e) = ap (f ∘ g) e
:= paths.rec (idpath _) e
