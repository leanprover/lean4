-- Setoid example/test
import macros

definition reflexive {A : (Type U)} (r : A → A → Bool) := ∀ x, r x x
definition symmetric {A : (Type U)} (r : A → A → Bool) := ∀ x y, r x y → r y x
definition transitive {A : (Type U)} (r : A → A → Bool) := ∀ x y z, r x y → r y z → r x z

-- We need to create a universe smaller than U for defining setoids.
-- If we use (Type U) in the definition of setoid, then we will not be
-- able to write s1 = s2 given  s1 s2 : setoid.
-- Writing the universes explicitily is really annoying. We should try to hide them.
universe s ≥ 1
-- We currently don't have records. So, we use sigma types.
definition setoid := sig A : (Type s), sig eq : A → A → Bool, (reflexive eq) # (symmetric eq) # (transitive eq)
definition to_setoid (S : (Type s)) (eq : S → S → Bool) (Hrefl : reflexive eq) (Hsymm : symmetric eq) (Htrans : transitive eq) : setoid
:= pair S (pair eq (pair Hrefl (pair Hsymm Htrans)))

-- The following definitions can be generated automatically.
definition carrier (s : setoid) := proj1 s
definition S_eq   {s : setoid} : carrier s → carrier s → Bool
:= proj1 (proj2 s)
infix 50 ≈ : S_eq
definition S_refl  {s : setoid} : ∀ x, x ≈ x
:= proj1 (proj2 (proj2 s))
definition S_symm  {s : setoid} {x y : carrier s} : x ≈ y → y ≈ x
:= proj1 (proj2 (proj2 (proj2 s))) x y
definition S_trans {s : setoid} {x y z : carrier s} : x ≈ y → y ≈ z → x ≈ z
:= proj2 (proj2 (proj2 (proj2 s))) x y z

-- First example: the cross-product of two setoids is a setoid
definition product (s1 s2 : setoid) : setoid
:= to_setoid
     (carrier s1 # carrier s2)
     (λ x y, proj1 x ≈ proj1 y ∧ proj2 x ≈ proj2 y)
     (take x, and_intro (S_refl (proj1 x)) (S_refl (proj2 x)))
     (take x y,
          assume H : proj1 x ≈ proj1 y ∧ proj2 x ≈ proj2 y,
          and_intro (S_symm (and_eliml H)) (S_symm (and_elimr H)))
     (take x y z,
          assume H1 : proj1 x ≈ proj1 y ∧ proj2 x ≈ proj2 y,
          assume H2 : proj1 y ≈ proj1 z ∧ proj2 y ≈ proj2 z,
          and_intro (S_trans (and_eliml H1) (and_eliml H2))
                    (S_trans (and_elimr H1) (and_elimr H2)))

scope
   -- We need to extend the elaborator to be able to write
   --    p1 p2 : product s1 s2
   set_option pp::implicit true
   check λ (s1 s2 : setoid) (p1 p2 : carrier (product s1 s2)), p1 ≈ p2
end

definition morphism (s1 s2 : setoid) := sig f : carrier s1 → carrier s2, ∀ x y, x ≈ y → f x ≈ f y
definition morphism_intro {s1 s2 : setoid} (f : carrier s1 → carrier s2) (H : ∀ x y, x ≈ y → f x ≈ f y) : morphism s1 s2
:= pair f H
definition f {s1 s2 : setoid} (m : morphism s1 s2) : carrier s1 → carrier s2
:= proj1 m
-- It would be nice to support (m.f x) as syntax sugar for (f m x)
definition is_compat {s1 s2 : setoid} (m : morphism s1 s2) {x y : carrier s1} : x ≈ y → f m x ≈ f m y
:= proj2 m x y

-- Second example: the composition of two morphism is a morphism
definition compose {s1 s2 s3 : setoid} (m1 : morphism s1 s2) (m2 : morphism s2 s3) : morphism s1 s3
:= morphism_intro
      (λ x, f m2 (f m1 x))
      (take x y, assume Hxy : x ≈ y,
         have Hfxy : f m1 x ≈ f m1 y,
           from is_compat m1 Hxy,
         show f m2 (f m1 x) ≈ f m2 (f m1 y),
           from is_compat m2 Hfxy)

