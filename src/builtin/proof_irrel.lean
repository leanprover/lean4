import macros

definition has_fixpoint (A : Bool) : Bool
:= ∃ F : (A → A) → A, ∀ f : A → A, F f = f (F f)

theorem eq_arrow (A : Bool) : inhabited A → (A → A) = A
:= assume Hin : inhabited A,
   obtain (p : A) (Hp : true), from Hin,
   iff_intro
     (assume Hl : A → A, p)
     (assume Hr : A, (assume H : A, H))

theorem bool_fixpoint (A : Bool) : inhabited A → has_fixpoint A
:= assume Hin : inhabited A,
   have Heq1 : (A → A) == A,
     from (to_heq (eq_arrow A Hin)),
   have Heq2 : A == (A → A),
     from hsymm Heq1,
   let g1 : A → (A → A)  := λ x : A,      cast Heq2 x,
       g2 : (A → A) → A  := λ x : A → A, cast Heq1 x,
       Y  : (A → A) → A  := (λ f : A → A, (λ x : A, f (g1 x x)) (g2 (λ x : A, f (g1 x x)))) in
   have R : ∀ f, g1 (g2 f) = f,
       from take f : A → A,
            calc g1 (g2 f) = cast Heq2 (cast Heq1 f)   : refl _
                      ...  = cast (htrans Heq1 Heq2) f : cast_trans _ _ _
                      ...  = f                         : cast_eq _ _,
   have Fix : (∀ f, Y f = f (Y f)),
     from take f : A → A,
          let  h : A → A := λ x : A, f (g1 x x) in
          have H1 : Y f = f (g1 (g2 h) (g2 h)),
            from refl (Y f),
          have H2 : g1 (g2 h) = h,
            from R h,
          have H3 : Y f = f (h (g2 h)),
            from substp (λ x, Y f = f (x (g2 h))) H1 H2,
          have H4 : f (Y f) = f (h (g2 h)),
            from refl (f (Y f)),
          trans H3 (symm H4),
   @exists_intro ((A → A) → A) (λ Y, ∀ f, Y f = f (Y f)) Y Fix

theorem proof_irrel_new (A : Bool) (p1 p2 : A) : p1 = p2
:= have H1 : inhabited A,
     from inhabited_intro p1,
   obtain (Y : (A → A) → A) (HY : ∀ f : A → A, Y f = f (Y f)), from bool_fixpoint A H1,
   let h : A → A := (λ x : A, if x = p1 then p2 else p1) in
   have HYh : Y h = h (Y h),
     from HY h,
   or_elim (em (Y h = p1))
     (assume Heq : Y h = p1,
        have Heq1 : h (Y h) = p2,
          from calc h (Y h)  = if Y h = p1 then p2 else p1 : refl _
                         ... = if true then p2 else p1     : { eqt_intro Heq }
                         ... = p2                          : if_true _ _,
        calc p1  =  Y h      : symm Heq
             ... =  h (Y h)  : HYh
             ... =  p2       : Heq1)
     (assume Hne : Y h ≠ p1,
        have Heq1 : h (Y h) = p1,
          from calc h (Y h)  = if Y h = p1 then p2 else p1 : refl _
                         ... = if false then p2 else p1    : { eqf_intro Hne }
                         ... = p1                          : if_false _ _,
        have Heq2 : Y h = p1,
          from trans HYh Heq1,
        absurd_elim (p1 = p2) Heq2 Hne)
