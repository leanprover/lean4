import macros

definition associative {A : (Type U)} (f : A → A → A)          := ∀ x y z, f (f x y) z = f x (f y z)
definition is_identity {A : (Type U)} (f : A → A → A) (id : A) := ∀ x, f x id = x
definition inverse_ex {A : (Type U)} (f : A → A → A) (id : A)  := ∀ x, ∃ y, f x y = id

universe s ≥ 1

definition group := sig A : (Type s), sig mul : A → A → A, sig one : A, (associative mul) # (is_identity mul one) # (inverse_ex mul one)
definition to_group (A : (Type s)) (mul : A → A → A) (one : A) (H1 : associative mul) (H2 : is_identity mul one) (H3 : inverse_ex mul one) : group
:= pair A (pair mul (pair one (pair H1 (pair H2 H3))))

-- The following definitions can be generated automatically.
definition carrier (g : group) := proj1 g
definition G_mul   {g : group} : carrier g → carrier g → carrier g
:= proj1 (proj2 g)
infixl 70 * : G_mul
definition one   {g : group} : carrier g
:= proj1 (proj2 (proj2 g))
theorem G_assoc {g : group} (x y z : carrier g) : (x * y) * z = x * (y * z)
:= (proj1 (proj2 (proj2 (proj2 g)))) x y z
theorem G_id {g : group} (x : carrier g) : x * one = x
:= (proj1 (proj2 (proj2 (proj2 (proj2 g))))) x
theorem G_inv {g : group} (x : carrier g) : ∃ y, x * y = one
:= (proj2 (proj2 (proj2 (proj2 (proj2 g))))) x

set_opaque group   true
set_opaque carrier true
set_opaque G_mul   true
set_opaque one     true

-- First example: the pairwise product of two groups is a group
definition product (g1 g2 : group) : group
:= let S       := carrier g1 # carrier g2,
       -- It would be nice to be able to define local notation, and write _*_ instead of f
       f       := λ x y, pair (proj1 x * proj1 y) (proj2 x * proj2 y),
       o       := pair one one  -- this is actually (pair (@one g1) (@one g2))
   in have assoc : associative f,
        -- The elaborator failed to infer the type of the pairs.
        -- I had to annotate the pairs with their types.
        from take x y z : S,  -- We don't really need to provide S, but it will make the elaborator to work much harder
                              -- since * is an overloaded operator, we also have * as notation for Nat::mul in the context.
               calc f (f x y) z = (pair ((proj1 x * proj1 y) * proj1 z) ((proj2 x * proj2 y) * proj2 z) : S)   : refl (f (f x y) z)
                          ...   = (pair (proj1 x * (proj1 y * proj1 z)) ((proj2 x * proj2 y) * proj2 z) : S)   : { G_assoc (proj1 x) (proj1 y) (proj1 z) }
                          ...   = (pair (proj1 x * (proj1 y * proj1 z)) (proj2 x * (proj2 y * proj2 z)) : S)   : { G_assoc (proj2 x) (proj2 y) (proj2 z) }
                          ...   = f x (f y z)                                                                  : refl (f x (f y z)),
      have id : is_identity f o,
        from take x : S,
                calc f x o  =  (pair (proj1 x * one) (proj2 x * one) : S)  : refl (f x o)
                        ... =  (pair (proj1 x) (proj2 x * one) : S)        : { G_id (proj1 x) }
                        ... =  (pair (proj1 x) (proj2 x) : S)              : { G_id (proj2 x) }
                        ... =  x                                           : pair_proj_eq x,
      have inv : inverse_ex f o,
        from take x : S,
          obtain (y1 : carrier g1) (Hy1 : proj1 x * y1 = one), from G_inv (proj1 x),
          obtain (y2 : carrier g2) (Hy2 : proj2 x * y2 = one), from G_inv (proj2 x),
          show ∃ y, f x y = o,
             from exists_intro (pair y1 y2 : S)
                    (calc f x (pair y1 y2 : S) = (pair (proj1 x * y1) (proj2 x * y2) : S)  : refl (f x (pair y1 y2 : S))
                                          ...  = (pair one (proj2 x * y2) : S)             : { Hy1 }
                                          ...  = (pair one one : S)                        : { Hy2 }
                                          ...  = o                                         : refl o),
      to_group S f o assoc id inv

set_opaque product true

-- It would be nice to be able to write x.first and x.second instead of (proj1 x) and (proj2 x)

-- Remark: * is overloaded since Lean loads Nat.lean by default.
-- The type errors related to * are quite cryptic because of that

-- Use 'star' for creating products
infixr 50 ⋆ : product

-- It would be nice to be able to write (p1 p2 : g1 ⋆ g2 ⋆ g3)
check λ (g1 g2 g3 : group) (p1 p2 : carrier (g1 ⋆ g2 ⋆ g3)), p1 * p2 = p2 * p1

theorem group_inhab (g : group) : inhabited (carrier g)
:= inhabited_intro (@one g)

definition inv {g : group} (a : carrier g) : carrier g
:= ε (group_inhab g) (λ x : carrier g, a * x = one)

theorem G_idl {g : group} (x : carrier g) : x * one = x
:= G_id x

theorem G_invl {g : group} (x : carrier g) : x * inv x = one
:= obtain (y : carrier g) (Hy : x * y = one), from G_inv x,
   eps_ax (group_inhab g) y Hy
set_opaque inv true

theorem G_inv_aux {g : group} (x : carrier g) : inv x = (inv x * x) * inv x
:= symm (calc (inv x * x) * inv x = inv x * (x * inv x) : G_assoc (inv x) x (inv x)
                           ...    = inv x * one         : { G_invl x }
                           ...    = inv x               : G_idl (inv x))

theorem G_invr {g : group} (x : carrier g) : inv x * x = one
:= calc inv x * x  = (inv x * x) * one                   :  symm (G_idl (inv x * x))
               ... = (inv x * x) * (inv x * inv (inv x)) :  { symm (G_invl (inv x)) }
               ... = ((inv x * x) * inv x) * inv (inv x) :  symm (G_assoc (inv x * x) (inv x) (inv (inv x)))
               ... = (inv x * (x * inv x)) * inv (inv x) :  { G_assoc (inv x) x (inv x) }
               ... = (inv x * one) * inv (inv x)         :  { G_invl x }
               ... = (inv x) * inv (inv x)               :  { G_idl (inv x) }
               ... = one                                 :  G_invl (inv x)

theorem G_idr {g : group} (x : carrier g) : one * x = x
:= calc one * x = (x * inv x) * x   : { symm (G_invl x) }
           ...  = x * (inv x * x)   : G_assoc x (inv x) x
           ...  = x * one           : { G_invr x }
           ...  = x                 : G_idl x

theorem G_inv_inv {g : group} (x : carrier g) : inv (inv x) = x
:= calc inv (inv x)  =  inv (inv x) * one          : symm (G_idl (inv (inv x)))
                ...  =  inv (inv x) * (inv x * x)  : { symm (G_invr x) }
                ...  =  (inv (inv x) * inv x) * x  : symm (G_assoc (inv (inv x)) (inv x) x)
                ...  =  one * x                    : { G_invr (inv x) }
                ...  =  x                          : G_idr x


definition commutative {A : (Type U)} (f : A → A → A) := ∀ x y, f x y = f y x

definition abelian_group := sig g : group, commutative (@G_mul g)
definition ab_to_g (ag : abelian_group) : group
:= proj1 ag
-- Coercions currently only work with opaque types
-- We must first define "extract" the information we want, and then
-- mark abelian_group as opaque
definition AG_comm {g : abelian_group} (x y : carrier (ab_to_g g)) : x * y = y * x
:= (proj2 g) x y

set_opaque abelian_group true
set_opaque ab_to_g       true
set_opaque AG_comm       true

coercion ab_to_g
-- Now, we can use abelian groups where groups are expected.

theorem AG_left_comm {g : abelian_group} (x y z : carrier g) : x * (y * z) = y * (x * z)
:= calc x * (y * z) = (x * y) * z    : symm (G_assoc x y z)
              ...   = (y * x) * z    : { AG_comm x y }
              ...   = y * (x * z)    : G_assoc y x z




