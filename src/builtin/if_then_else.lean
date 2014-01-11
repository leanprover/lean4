-- if_then_else expression support
builtin ite {A : (Type U)} : Bool → A → A → A
notation 60 if _ then _ else _ : ite

axiom if_true {A : TypeU} (a b : A) : if true then a else b = a
axiom if_false {A : TypeU} (a b : A) : if false then a else b = b

theorem if_a_a {A : TypeU} (c : Bool) (a : A) : if c then a else a = a
:= case (λ x, if x then a else a = a) (if_true a a) (if_false a a) c

-- Simplify the then branch using the fact that c is true, and the else branch that c is false
theorem if_congr {A : TypeU} {b c : Bool} {x y u v : A} (H_bc : b = c) (H_xu : ∀ (H_c : c), x = u) (H_yv : ∀ (H_nc : ¬ c), y = v) :
        (if b then x else y) = (if c then u else v)
:= or_elim (em c)
     (λ H_c : c, calc (if b then x else y) = (if c then x else y)    : { H_bc }
                                      ...  = (if true then x else y) : { eqt_intro H_c }
                                      ...  = x                       : if_true _ _
                                      ...  = u                       : H_xu H_c
                                      ...  = (if true then u else v) : symm (if_true _ _)
                                      ...  = (if c then u else v)    : { symm (eqt_intro H_c) })
     (λ H_nc : ¬ c, calc (if b then x else y) = (if c then x else y)     : { H_bc }
                                         ...  = (if false then x else y) : { eqf_intro H_nc }
                                         ...  = y                        : if_false _ _
                                         ...  = v                        : H_yv H_nc
                                         ...  = (if false then u else v) : symm (if_false _ _)
                                         ...  = (if c then u else v)     : { symm (eqf_intro H_nc) })

set_opaque ite true