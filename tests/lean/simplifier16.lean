-- Canonicalizing subsingletons
import algebra.ring
open algebra

set_option pp.all true
universes l j k
constants (A : Type.{l}) (s : comm_ring A)
attribute s [instance]
constants (x y : A) (P : A → Type.{j}) (P_ss : ∀ a, subsingleton (P a))
constants (f : Π a, P a → A) (Px1 Px2 Px3 : P x)
constants (g : A → A → A)
attribute P_ss [instance]

#simplify eq env 0 g (f x Px1) (f x Px2)
#simplify eq env 0 g (f x Px1) (g (f x Px2) (f x Px3))
