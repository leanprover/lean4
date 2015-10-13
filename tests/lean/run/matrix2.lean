import logic

constant matrix.{l} : Type.{l} → Type.{l}
constant same_dim {A : Type} : matrix A → matrix A → Prop
constant add1 {A : Type} (m1 m2 : matrix A) {H : same_dim m1 m2} : matrix A
open eq
theorem same_dim_eq_args {A : Type} {m1 m2 m1' m2' : matrix A} (H1 : m1 = m1') (H2 : m2 = m2') (H : same_dim m1 m2) : same_dim m1' m2' :=
subst H1 (subst H2 H)

theorem add1_congr {A : Type} (m1 m2 m1' m2' : matrix A) (H1 : m1 = m1') (H2 : m2 = m2') (H : same_dim m1 m2) : @add1 A m1 m2 H = @add1 A m1' m2' (same_dim_eq_args H1 H2 H) :=
have base : ∀ (H1 : m1 = m1) (H2 : m2 = m2), @add1 A m1 m2 H = @add1 A m1 m2 (eq.rec (eq.rec H H1) H2), from
  assume H1 H2, rfl,
have general : ∀ (H1 : m1 = m1') (H2 : m2 = m2'), @add1 A m1 m2 H = @add1 A m1' m2' (eq.rec (eq.rec H H1) H2), from
  subst H1 (subst H2 base),
general H1 H2
