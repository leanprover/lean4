inductive dvec {X : Type} (Y : X → Type) : list X → Type
| dnil {}  : dvec []
| dcons : Π {x : X}, Y x → Π {xs : list X}, dvec xs → dvec (x::xs)

namespace dvec

notation `⟦` l:(foldr `, ` (h t, dvec.dcons h t) dvec.dnil `⟧`) := l

def get {X : Type} [decidable_eq X] {Y : X → Type} (x₀ : X) [inhabited (Y x₀)]
  : Π {xs : list X}, dvec Y xs → ℕ → Y x₀
| []      _                _      := default (Y x₀)
| (x::xs) (dvec.dcons y ys) 0     := if H : x = x₀ then eq.rec_on H y else default (Y x₀)
| (x::xs) (dvec.dcons y ys) (n+1) := get ys n

end dvec

constant tensor : list ℕ → Type
noncomputable instance inhabited_tensor (shape : list ℕ) : inhabited (tensor shape) := sorry
constant f {shape : list ℕ} : tensor shape → tensor shape → tensor shape

noncomputable def bar {shape : list ℕ} (μσ : dvec tensor [shape, shape]) : tensor shape :=
  let μ := dvec.get shape μσ 0, σ := dvec.get shape μσ 1 in f μ σ

lemma foo {shape : list ℕ} (μ σ : tensor shape) :
      bar ⟦μ, σ⟧ = bar ⟦μ, σ⟧ :=
suffices H_suffices : true, from
begin
dunfold bar, dsimp,
dunfold dvec.get,
reflexivity
end,
trivial
