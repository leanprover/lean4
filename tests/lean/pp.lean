prelude set_option pp.beta false check λ {A : Type.{1}} (B : Type.{1}) (a : A) (b : B), a
check λ {A : Type.{1}} {B : Type.{1}} (a : A) (b : B), a
check λ (A : Type.{1}) {B : Type.{1}} (a : A) (b : B), a
check λ (A : Type.{1}) (B : Type.{1}) (a : A) (b : B), a
check λ [A : Type.{1}] (B : Type.{1}) (a : A) (b : B), a
check λ {{A : Type.{1}}} {B : Type.{1}} (a : A) (b : B), a
check λ {{A : Type.{1}}} {{B : Type.{1}}} (a : A) (b : B), a
