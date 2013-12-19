Variable Eq      {A : (Type U+1)} (a b : A) : Bool
Infix 50 === : Eq
Axiom EqSubst {A : (Type U+1)} {a b : A} (P : A -> Bool) (H1 : P a) (H2 : a === b) : P b
Axiom EqRefl  {A : (Type U+1)} (a : A) : a === a
Theorem EqSymm {A : (Type U+1)} {a b : A} (H : a === b) : b === a :=
        EqSubst (fun x, x === a) (EqRefl a) H
Theorem EqTrans {A : (Type U+1)} {a b c : A} (H1 : a === b) (H2 : b === c) : a === c :=
        EqSubst (fun x, a === x) H1 H2
Theorem EqCongr {A B : (Type U+1)} (f : A -> B) {a b : A} (H : a === b) : (f a) === (f b) :=
        EqSubst (fun x, (f a) === (f x)) (EqRefl (f a)) H
Theorem EqCongr1 {A : (Type U+1)} {B : A -> (Type U+1)} {f g : Pi x : A, B x} (a : A) (H : f === g) : (f a) === (g a) :=
        EqSubst (fun h : (Pi x : A, B x), (f a) === (h a)) (EqRefl (f a)) H
Axiom ProofIrrelevance (P : Bool) (pr1 pr2 : P) : pr1 === pr2
Axiom EqCast {A B : (Type U)} (H : A === B) (a : A) : B
Axiom EqCastHom {A B : (Type U)} {a1 a2 : A} (HAB : A === B) (H : a1 === a2) : (EqCast HAB a1) === (EqCast HAB a2)
Axiom EqCastRefl {A : (Type U)} (a : A) : (EqCast (EqRefl A) a) === a

Variable Vector : (Type U) -> Nat -> (Type U)
Variable empty {A : (Type U)} : Vector A 0
Variable append {A : (Type U)} {m n : Nat} (v1 : Vector A m) (v2 : Vector A n) : Vector A (m + n)
Axiom Plus0 (n : Nat) : (n + 0) === n
Theorem VectorPlus0 (A : (Type U)) (n : Nat) : (Vector A (n + 0)) === (Vector A n) :=
        EqSubst (fun x : Nat, (Vector A x) === (Vector A n))
                (EqRefl (Vector A n))
                (EqSymm (Plus0 n))
SetOption pp::implicit true
(* Check fun (A : Type) (n : Nat), VectorPlus0 A n *)
Axiom AppendNil {A : Type} {n : Nat} (v : Vector A n) : (EqCast (VectorPlus0 A n) (append v empty)) === v

Variable List : (Type U) -> (Type U).
Variables A B : (Type U)
Axiom H1 : A === B.
Theorem LAB : (List A) === (List B) :=
        EqCongr List H1
Variable l1 : List A
Variable l2 : List B
Variable H2 : (EqCast LAB l1) == l2


(*
Theorem EqCastInv {A B : (Type U)} (H : A === B) (a : A) : (EqCast (EqSymm H) (EqCast H a)) === a :=
*)

(*
Variable ReflCast : Pi (A : (Type U)) (a : A) (H : Eq (Type U) A A), Eq A (Casting A A H a) a
Theorem AppEq (A : (Type U)) (B : A -> (Type U)) (a b : A) (H : Eq A a b) : (Eq (Type U) (B b) (B a)) :=
        EqCongr A (Type U) B b a (EqSymm A a b H)
Theorem EqCongr2 (A : (Type U)) (B : A -> (Type U)) (f : Pi x : A, B x) (a b : A) (H : Eq A a b) : Eq (B a) (f a) (Casting (B b) (B a) (AppEq A B a b H) (f a)) (f b) :=
        EqSubst (B a) a b (fun x : A, Eq (B a) (f a) (Casting (B x) (B a) (AppEq A B a b H) (f a)) (f x)
*)