prelude set_option pp.beta false check λ {A : Type} (B : Type) (a : A) (b : B), a
check λ {A : Type} {B : Type} (a : A) (b : B), a
check λ (A : Type) {B : Type} (a : A) (b : B), a
check λ (A : Type) (B : Type) (a : A) (b : B), a
check λ [A : Type] (B : Type) (a : A) (b : B), a
check λ {{A : Type}} {B : Type} (a : A) (b : B), a
check λ {{A : Type}} {{B : Type}} (a : A) (b : B), a
