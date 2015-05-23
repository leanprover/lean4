constant set    : Type₁ → Type₁
constant finset : Type₁ → Type₁
constant set.mem : Π {A : Type₁}, A → set A → Prop
constant finset.mem : Π {A : Type₁}, A → finset A → Prop

infix ∈ := set.mem
infix ∈ := finset.mem

definition set.subset {A : Type₁} (s₁ s₂ : set A) : Prop :=
∀ ⦃a : A⦄, a ∈ s₁ → a ∈ s₂

definition finset.subset {A : Type₁} (s₁ s₂ : finset A) : Prop :=
∀ ⦃a : A⦄, a ∈ s₁ → a ∈ s₂

infix `⊆` := set.subset
infix `⊆` := finset.subset

example (A : Type₁) (x : A) (S H : set A) (Pin : x ∈ S) (Psub : S ⊆ H) : x ∈ H :=
Psub Pin -- Error, we cannot infer at preprocessing time the binder information for Psub
