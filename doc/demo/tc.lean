import macros

definition reflexive {A : TypeU}  (R : A → A → Bool) := ∀ x, R x x
definition transitive {A : TypeU} (R : A → A → Bool) := ∀ x y z, R x y → R y z → R x z
definition subrelation {A : TypeU} (R1 : A → A → Bool) (R2 : A → A → Bool) := ∀ x y, R1 x y → R2 x y
infix 50 ⊆ : subrelation

-- (tcls R) is the transitive closure of relation R
-- We define it as the intersection of all transitive relations containing R
definition tcls {A : TypeU} (R : A → A → Bool) (a b : A)
:= ∀ P, (reflexive P) → (transitive P) → (R ⊆ P) → P a b
notation 65 _⁺ : tcls  -- use superscript + as notation for transitive closure

theorem tcls_trans {A : TypeU} {R : A → A → Bool} {a b c : A} (Hab : R⁺ a b) (Hbc : R⁺ b c) : R⁺ a c
:= take P, assume Hrefl Htrans Hsub,
     let Pab : P a b := Hab P Hrefl Htrans Hsub,
         Pbc : P b c := Hbc P Hrefl Htrans Hsub
     in Htrans a b c Pab Pbc

theorem tcls_refl {A : TypeU} (R : A → A → Bool) : ∀ a, R⁺ a a
:= take a P, assume Hrefl Htrans Hsub,
      Hrefl a

theorem tcls_sub {A : TypeU} (R : A → A → Bool) : R ⊆ R⁺
:= take a b,
     assume Hab : R a b,
          have R⁺ a b :
             take P, assume Hrefl Htrans Hsub,
                Hsub a b Hab

theorem tcls_step {A : TypeU} {R : A → A → Bool} {a b c : A} (H1 : R a b) (H2 : R⁺ b c) : R⁺ a c
:= take P, assume Hrefl Htrans Hsub,
      Htrans a b c (Hsub a b H1) (H2 P Hrefl Htrans Hsub)

theorem tcls_smallest {A : TypeU} (R : A → A → Bool) : ∀ P, (reflexive P) → (transitive P) → (R ⊆ P) → (R⁺ ⊆ P)
:= take P, assume Hrefl Htrans Hsub,
     take a b, assume H : R⁺ a b,
         have P a b : H P Hrefl Htrans Hsub
