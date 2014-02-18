import macros

theorem bool_inhab : inhabited Bool
:= inhabited_intro true

-- Excluded middle from eps_ax, boolext, funext, and subst
theorem em_new (p : Bool) : p ∨ ¬ p
:= let u := @eps Bool bool_inhab (λ x, x = true ∨ p),
       v := @eps Bool bool_inhab (λ x, x = false ∨ p) in
   have Hu : u = true ∨ p,
     from @eps_ax Bool bool_inhab (λ x, x = true ∨ p) true (or_introl (refl true) p),
   have Hv : v = false ∨ p,
     from @eps_ax Bool bool_inhab (λ x, x = false ∨ p) false (or_introl (refl false) p),
   have H1 : u ≠ v ∨ p,
     from or_elim Hu
            (assume Hut : u = true,
               or_elim Hv
                 (assume Hvf : v = false,
                    have Hne : u ≠ v,
                      from subst (subst true_ne_false (symm Hut)) (symm Hvf),
                    or_introl Hne p)
                 (assume Hp : p, or_intror (u ≠ v) Hp))
            (assume Hp : p, or_intror (u ≠ v) Hp),
   have H2 : p → u = v,
     from assume Hp : p,
            have Hpred : (λ x, x = true ∨ p) = (λ x, x = false ∨ p),
              from funext (take x : Bool,
                              have Hl : (x = true ∨ p) → (x = false ∨ p),
                                from assume A, or_intror (x = false) Hp,
                              have Hr : (x = false ∨ p) → (x = true ∨ p),
                                from assume A, or_intror (x = true) Hp,
                              show (x = true ∨ p) = (x = false ∨ p),
                                from boolext Hl Hr),
            show u = v,
               from @subst (Bool → Bool) (λ x : Bool, (@eq Bool x true) ∨ p) (λ x : Bool, (@eq Bool x false) ∨ p)
                           (λ q : Bool → Bool, @eps Bool bool_inhab (λ x : Bool, (@eq Bool x true) ∨ p) = @eps Bool bool_inhab q)
                           (@refl Bool (@eps Bool bool_inhab (λ x : Bool, (@eq Bool x true) ∨ p)))
                           Hpred,
   have H3 : u ≠ v → ¬ p,
     from contrapos H2,
   or_elim H1
     (assume Hne : u ≠ v, or_intror p (H3 Hne))
     (assume Hp : p, or_introl Hp (¬ p))