inductive fibrant [class] (T : Type) : Type :=
fibrant_mk : fibrant T

axiom pi_fibrant {A : Type} {B : A → Type} [C1 : fibrant A] [C2 : Πx : A, fibrant (B x)] :
  fibrant (Πx : A, B x)
attribute pi_fibrant [instance]

inductive path {A : Type} [fA : fibrant A] (a : A) : A → Type :=
idpath : path a a

axiom path_fibrant {A : Type} [fA : fibrant A] (a b : A) : fibrant (path a b)
attribute path_fibrant [instance]

notation a ≈ b := path a b

noncomputable definition test {A : Type} [fA : fibrant A] {x y : A} :
  Π (z : A), y ≈ z → fibrant (x ≈ y → x ≈ z) := take z p, _

noncomputable definition test2 {A : Type} [fA : fibrant A] {x y : A} :
Π (z : A), y ≈ z → fibrant (x ≈ y → x ≈ z) := _

noncomputable definition test3 {A : Type} [fA : fibrant A] {x y : A} :
  Π (z : A), y ≈ z → fibrant (x ≈ z) := _

noncomputable definition test4 {A : Type} [fA : fibrant A] {x y z : A} :
  fibrant (x ≈ y → x ≈ z) := _

axiom imp_fibrant {A : Type} {B : Type} [C1 : fibrant A] [C2 : fibrant B] : fibrant (A → B)
attribute imp_fibrant [instance]

noncomputable definition test5 {A : Type} [fA : fibrant A] {x y : A} :
Π (z : A), y ≈ z → fibrant (x ≈ y → x ≈ z) := _
