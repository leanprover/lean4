open eq sigma

variables {A : Type} {B : A → Type} {C : Πa, B a → Type} {D : Πa b, C a b → Type}
          {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {u v w : Σa, B a}

definition path_sigma_dpair (p : a = a') (q : p ▹ b = b') : dpair a b = dpair a' b' :=
eq.rec_on p (λb b' q, eq.rec_on q idp) b b' q

definition path_sigma (p :  dpr1 u = dpr1 v) (q : p ▹ dpr2 u = dpr2 v) : u = v :=
destruct u
         (λu1 u2, destruct v (λ v1 v2, path_sigma_dpair))
         p q

definition path_path_sigma_lemma' {p1 : a = a'} {p2 : p1 ▹ b = b'} {q2 : p1 ▹ b = b'}
    (s : idp ▹ p2 = q2) : path_sigma p1 p2 = path_sigma p1 q2 :=
begin
  apply (eq.rec_on s),
  apply idp,
end
