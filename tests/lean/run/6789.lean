/-!
# Ensure equational theorems generation doesn't fail when metadata is involved

https://github.com/leanprover/lean4/issues/6789

The original error would happen because `casesOnStuckLHS` (https://github.com/leanprover/lean4/blob/4ca98dcca2b0995dddff444cfef1f3ccc89c7b12/src/Lean/Meta/Match/MatchEqs.lean#L51)
would fail to find an fvar to do `cases` on when that fvar would be encapsulated by some metadata.
-/

inductive Con
| nil
| ext (Γ : Con) (n : Nat)

variable {Op : Con → Con → Type u}

inductive Extension : Con → Con → Type
| zero : Extension Γ Γ
| succ : Extension Γ Δ → (n : Nat) → Extension Γ (.ext Δ n)

def Extension.recOn'
  {motive : (Γ Δ : Con) → Extension Γ Δ → Sort v}
  (zero : {Γ : Con} → motive Γ Γ .zero)
  (succ
    : {Γ Δ : Con} → (xt : Extension Γ Δ)
    → (A : Nat)
    → motive Γ Δ xt
    → motive Γ (.ext Δ A) (.succ xt A))
  : {Γ Δ : Con} → (xt : Extension Γ Δ) → motive Γ Δ xt
| _, _, .zero => zero
| _, _, .succ xt A => succ xt A (Extension.recOn' zero succ xt)


/--
info: equations:
theorem Extension.recOn'.eq_1.{v} : ∀ {motive : (Γ Δ : Con) → Extension Γ Δ → Sort v}
  (zero : {Γ : Con} → motive Γ Γ Extension.zero)
  (succ : {Γ Δ : Con} → (xt : Extension Γ Δ) → (A : Nat) → motive Γ Δ xt → motive Γ (Δ.ext A) (xt.succ A)) (x : Con),
  Extension.recOn' zero succ Extension.zero = zero
theorem Extension.recOn'.eq_2.{v} : ∀ {motive : (Γ Δ : Con) → Extension Γ Δ → Sort v}
  (zero : {Γ : Con} → motive Γ Γ Extension.zero)
  (succ : {Γ Δ : Con} → (xt : Extension Γ Δ) → (A : Nat) → motive Γ Δ xt → motive Γ (Δ.ext A) (xt.succ A)) (x Δ : Con)
  (A : Nat) (xt : Extension x Δ),
  Extension.recOn' zero succ (xt.succ A) = succ xt A (Extension.recOn' (fun {Γ} => zero) (fun {Γ Δ} => succ) xt)
-/
#guard_msgs in
#print equations Extension.recOn'

def Extension.pullback_con
  : (xt : Extension B Δ) → (σ : Op B' B)
  → Con
| .zero, σ => B'
| .succ xt A, σ => .ext (pullback_con xt σ) A

/--
info: equations:
theorem Extension.pullback_con.eq_1.{u} : ∀ {Op : Con → Con → Type u} {B B' : Con} (x : Op B' B),
  Extension.zero.pullback_con x = B'
theorem Extension.pullback_con.eq_2.{u} : ∀ {Op : Con → Con → Type u} {B B' : Con} (x : Op B' B) (Δ_2 : Con)
  (xt : Extension B Δ_2) (A : Nat), (xt.succ A).pullback_con x = (xt.pullback_con x).ext A
-/
#guard_msgs in
#print equations Extension.pullback_con
