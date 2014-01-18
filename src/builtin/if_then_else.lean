import macros

-- if_then_else expression support
builtin ite {A : (Type U)} : Bool → A → A → A
notation 45 if _ then _ else _ : ite

axiom if_true {A : TypeU} (a b : A) : (if true then a else b) = a
axiom if_false {A : TypeU} (a b : A) : (if false then a else b) = b

theorem if_a_a {A : TypeU} (c : Bool) (a : A) : (if c then a else a) = a
:= case (λ x, (if x then a else a) = a) (if_true a a) (if_false a a) c

-- Simplify the then branch using the fact that c is true, and the else branch that c is false
theorem if_congr {A : TypeU} {b c : Bool} {x y u v : A} (H_bc : b = c)
                 (H_xu : ∀ (H_c : c), x = u) (H_yv : ∀ (H_nc : ¬ c), y = v) :
        (if b then x else y) = if c then u else v
:= or_elim (em c)
     (λ H_c : c, calc
          (if b then x else y) = if c then x else y      : { H_bc }
                          ...  = if true then x else y   : { eqt_intro H_c }
                          ...  = x                       : if_true _ _
                          ...  = u                       : H_xu H_c
                          ...  = if true then u else v   : symm (if_true _ _)
                          ...  = if c then u else v      : { symm (eqt_intro H_c) })
     (λ H_nc : ¬ c, calc
          (if b then x else y) = if c then x else y      : { H_bc }
                          ...  = if false then x else y  : { eqf_intro H_nc }
                          ...  = y                       : if_false _ _
                          ...  = v                       : H_yv H_nc
                          ...  = if false then u else v  : symm (if_false _ _)
                          ...  = if c then u else v      : { symm (eqf_intro H_nc) })

theorem if_imp_then {a b c : Bool} (H : if a then b else c)  : a → b
:= assume Ha : a, eqt_elim (calc   b = if true then b else c : symm (if_true b c)
                                 ... = if a then b else c    : { symm (eqt_intro Ha) }
                                 ... = true                  : eqt_intro H)

theorem if_imp_else {a b c : Bool} (H : if a then b else c) : ¬ a → c
:= assume Hna : ¬ a, eqt_elim (calc   c = if false then b else c : symm (if_false b c)
                                    ... = if a then b else c     : { symm (eqf_intro Hna) }
                                    ... = true                   : eqt_intro H)

theorem app_if_distribute {A B : TypeU} (c : Bool) (f : A → B) (a b : A) : f (if c then a else b) = if c then f a else f b
:= or_elim (em c)
     (λ Hc : c , calc
          f (if c then a else b) = f (if true then a else b)    : { eqt_intro Hc }
                            ...  = f a                          : { if_true a b }
                            ...  = if true then f a else f b    : symm (if_true (f a) (f b))
                            ...  = if c then f a else f b       : { symm (eqt_intro Hc) })
     (λ Hnc : ¬ c, calc
          f (if c then a else b) = f (if false then a else b)   : { eqf_intro Hnc }
                            ...  = f b                          : { if_false a b }
                            ...  = if false then f a else f b   : symm (if_false (f a) (f b))
                            ...  = if c then f a else f b       : { symm (eqf_intro Hnc) })

theorem eq_if_distributer {A : TypeU} (c : Bool) (a b v : A) : (v = (if c then a else b)) = if c then v = a else v = b
:= app_if_distribute c (eq v) a b

theorem eq_if_distributel {A : TypeU} (c : Bool) (a b v : A) : ((if c then a else b) = v) = if c then a = v else b = v
:= app_if_distribute c (λ x, x = v) a b

set_opaque ite true