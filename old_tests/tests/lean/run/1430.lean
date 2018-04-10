universe variables u

inductive foo_basic (A : Type u) : psum unit ℕ → Type u
| mk : Π n, foo_basic (psum.inr n) → foo_basic (psum.inl ())
| nil : foo_basic (psum.inr 0)
| cons : Π {n}, A → foo_basic (psum.inr n) → foo_basic (psum.inr (n+1))

def foo (A : Type u) : Type u := foo_basic A (psum.inl ())
def foo.vec (A : Type u) (n : ℕ) : Type u := foo_basic A (psum.inr n)

def foo.mk (A : Type u) : Π n, foo.vec A n → foo A := foo_basic.mk

lemma layer3.foo.mk.inj (A : Type u) :
  ∀ (n₁ n₂ : ℕ) (xs₁ : foo.vec A n₁) (xs₂ : foo.vec A n₂),
    @foo.mk A n₁ xs₁ = @foo.mk A n₂ xs₂
    → xs₁ == xs₂ :=
begin
dunfold foo.mk,
begin [smt]
intros n₁ n₂ xs₁ xs₂ H,
end
end
