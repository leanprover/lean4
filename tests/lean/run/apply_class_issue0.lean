structure is_trunc [class] (A : Type) : Type

theorem foo (A : Type) [H : is_trunc A] (B : Type) : B := sorry

theorem bar [H : is_trunc false] : false :=
by apply (@foo false _)
