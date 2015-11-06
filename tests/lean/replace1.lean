constant f : Π {A : Type}, A → A → A
variables a b c : nat
variables H : a = b

set_option pp.all true

#replace f a a, [a], [b]
#replace f (f a b) b, [a,b], [b,a]

variables x y : bool

-- [nat] and [bool] are instances of the telescope (A : Type),
-- but the resulting expression is type incorrect.
-- Thus, #replace correctly detects the error.
#replace f a a, [nat], [bool] -- Error
-- An error is not detected in the following one,
-- since there is no telescope s.t., [a] and [x] are instances of.
#replace f a a, [a], [x]
-- The following should work, [nat, a] and [bool, x] are instances
-- of the telescope (A : Type, a : A), and the result is type correct
#replace f a a, [nat, a], [bool, x]

variable p : nat → Prop
variable H1 : p a

-- [b] and [a] are instances of the telescope (x : nat),
-- but the resulting expression is type incorrect.
-- Thus, #replace correctly detects the error.
#replace @eq.rec nat a (λ x : nat, p x) H1 b H, [b], [a]         -- Error
-- There is no telescope s.t. [H] and [eq.refl a] are instances of.
#replace @eq.rec nat a (λ x : nat, p x) H1 b H, [H], [eq.refl a]
-- [b, H] and [a, eq.refl a] are both instances of the telescope
-- (x : nat, H : a = x), and the resulting expression is type correct
#replace @eq.rec nat a (λ x : nat, p x) H1 b H, [b, H], [a, eq.refl a]

constant bv : nat → Type₁

variables v₁ v₂ : bv 10

#replace v₁ = v₂, [(10:nat)], [(11:nat)] -- Error
#replace (λ v₁ v₂ : bv 10, v₁ = v₂), [(10:nat)], [(11:nat)]
