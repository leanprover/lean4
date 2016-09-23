prelude
import init.logic init.classical

universe variables u

-- For n-ary support
structure [class] is_associative {A : Type u} (op : A → A → A) :=
(op_assoc : ∀ x y z : A, op (op x y) z = op x (op y z))

instance : is_associative and :=
is_associative.mk (λ x y z, propext (@and.assoc x y z))

instance : is_associative or :=
is_associative.mk (λ x y z, propext (@or.assoc x y z))

-- Basic congruence theorems over equality (using propext)
attribute [congr]
theorem imp_congr_ctx_eq {P₁ P₂ Q₁ Q₂ : Prop} (H₁ : P₁ = P₂) (H₂ : P₂ → (Q₁ = Q₂)) : (P₁ → Q₁) = (P₂ → Q₂) :=
propext (imp_congr_ctx (iff.of_eq H₁) (assume p₂, iff.of_eq (H₂ p₂)))

attribute [congr]
theorem forall_congr_eq {A : Type u} (P Q : A → Prop) (H : ∀ a, P a = Q a) : ((∀ a, P a) = (∀ a, Q a)) :=
propext (forall_congr (assume a, iff.of_eq (H a)))

-- Congruence theorems for flattening
namespace simplifier
variables {A : Type u}

theorem congr_bin_op {op op' : A → A → A} (H : op = op') (x y : A) : op x y = op' x y :=
congr_fun (congr_fun H x) y

theorem congr_bin_arg1 {op : A → A → A} {x x' y : A} (Hx : x = x') : op x y = op x' y :=
congr_fun (congr_arg op Hx) y

theorem congr_bin_arg2 {op : A → A → A} {x y y' : A} (Hy : y = y') : op x y = op x y' :=
congr_arg (op x) Hy

theorem congr_bin_args {op : A → A → A} {x x' y y' : A} (Hx : x = x') (Hy : y = y') : op x y = op x' y' :=
congr (congr_arg op Hx) Hy

theorem assoc_subst {op op' : A → A → A} (H : op = op') (H_assoc : ∀ x y z, op (op x y) z = op x (op y z))
  : (∀ x y z, op' (op' x y) z = op' x (op' y z)) :=
H ▸ H_assoc

end simplifier
