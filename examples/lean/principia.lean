import macros

-- Some theorems from Pricipia Mathematica
theorem p1 {A : TypeU} (p : Bool) (φ : A → Bool) : (∀ x, p ∨ φ x) = (p ∨ ∀ x, φ x)
:= boolext
     (assume H : (∀ x, p ∨ φ x),
        or_elim (em p)
            (λ Hp  : p,   or_introl Hp (∀ x, φ x))
            (λ Hnp : ¬ p, or_intror p  (take x,
                                             resolve1 (H x) Hnp)))
     (assume H : (p ∨ ∀ x, φ x),
        take x,
            or_elim H
              (λ H1 : p,          or_introl H1 (φ x))
              (λ H2 : (∀ x, φ x), or_intror p  (H2 x)))

theorem p2 {A : TypeU} (p : Bool) (φ : A → Bool) : (∀ x, φ x ∨ p) = ((∀ x, φ x) ∨ p)
:= calc (∀ x, φ x ∨ p) = (∀ x, p ∨ φ x)   : allext (λ x, or_comm (φ x) p)
                  ...  = (p ∨ ∀ x, φ x)   : p1 p φ
                  ...  = ((∀ x, φ x) ∨ p) : or_comm p (∀ x, φ x)

theorem p3 {A : TypeU} (φ ψ : A → Bool) : (∀ x, φ x ∧ ψ x) = ((∀ x, φ x) ∧ (∀ x, ψ x))
:= boolext
     (assume H : (∀ x, φ x ∧ ψ x),
        and_intro (take x, and_eliml (H x)) (take x, and_elimr (H x)))
     (assume H : (∀ x, φ x) ∧ (∀ x, ψ x),
        take x, and_intro (and_eliml H x) (and_elimr H x))

theorem p4 {A : TypeU} (p : Bool) (φ : A → Bool) : (∃ x, p ∧ φ x) = (p ∧ ∃ x, φ x)
:= boolext
     (assume H : (∃ x, p ∧ φ x),
        obtain (w : A) (Hw : p ∧ φ w), from H,
            and_intro (and_eliml Hw) (exists_intro w (and_elimr Hw)))
     (assume H : (p ∧ ∃ x, φ x),
        obtain (w : A) (Hw : φ w), from (and_elimr H),
            exists_intro w (and_intro (and_eliml H) Hw))

theorem p5 {A : TypeU} (p : Bool) (φ : A → Bool) : (∃ x, φ x ∧ p) = ((∃ x, φ x) ∧ p)
:= calc (∃ x, φ x ∧ p) = (∃ x, p ∧ φ x)   : eq_exists_intro (λ x, and_comm (φ x) p)
                 ...   = (p ∧ (∃ x, φ x)) : p4 p φ
                 ...   = ((∃ x, φ x) ∧ p) : and_comm p (∃ x, φ x)

theorem p6 {A : TypeU} (φ ψ : A → Bool) : (∃ x, φ x ∨ ψ x) = ((∃ x, φ x) ∨ (∃ x, ψ x))
:= boolext
    (assume H : (∃ x, φ x ∨ ψ x),
        obtain (w : A) (Hw : φ w ∨ ψ w), from H,
            or_elim Hw
                (λ Hw1 : φ w, or_introl (exists_intro w Hw1) (∃ x, ψ x))
                (λ Hw2 : ψ w, or_intror (∃ x, φ x) (exists_intro w Hw2)))
    (assume H : (∃ x, φ x) ∨ (∃ x, ψ x),
        or_elim H
            (λ H1 : (∃ x, φ x),
                obtain (w : A) (Hw : φ w), from H1,
                    exists_intro w (or_introl Hw (ψ w)))
            (λ H2 : (∃ x, ψ x),
                obtain (w : A) (Hw : ψ w), from H2,
                    exists_intro w (or_intror (φ w) Hw)))
