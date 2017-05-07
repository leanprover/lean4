inductive ty
| base : string → ty
| arr : ty → ty → ty

namespace ty
instance : decidable_eq ty := by tactic.mk_dec_eq_instance
instance : inhabited ty := ⟨ty.base "o"⟩
end ty

@[reducible] def ctx := list ty

inductive lamexp_core : ctx → ty → Type
| var : Π {Γ : ctx} {t} (n : ℕ), list.nth Γ n = some t → lamexp_core Γ t
| fv : Π {Γ}, string → Π t : ty, lamexp_core Γ t
| con : Π {Γ}, string → Π t : ty, lamexp_core Γ t
| app : Π {Γ} {t s}, lamexp_core Γ (ty.arr t s) → lamexp_core Γ t → lamexp_core Γ s
| abs : Π {Γ : ctx} {t s}, lamexp_core (t::Γ) s → lamexp_core Γ (ty.arr t s)

namespace lamexp_core
-- instance {Γ t} : decidable_eq (lamexp_core Γ t) := by tactic.mk_dec_eq_instance
instance {Γ t} : inhabited (lamexp_core Γ t) := ⟨lamexp_core.con "c" t⟩
end lamexp_core

@[reducible] def lamexp := lamexp_core []

namespace lamexp

lemma nth_append {α} {ys : list α} : Π {n xs}, list.nth xs n ≠ none → list.nth (xs ++ ys) n = list.nth xs n
| 0     []      h := by contradiction
| (n+1) []      h := by contradiction
| 0     (x::xs) h := rfl
| (n+1) (x::xs) h := @nth_append n xs h

def weaken_core : ∀ {Γ Δ t}, lamexp_core Γ t → lamexp_core (Γ ++ Δ) t
| Γ Δ .(t) (@lamexp_core.var .(Γ) t n h) := lamexp_core.var n $
    begin rw nth_append, assumption, rw h, intro, contradiction end
| Γ Δ .(t) (lamexp_core.fv n t) := lamexp_core.fv n t
| Γ Δ .(t) (lamexp_core.con n t) := lamexp_core.con n t
| Γ Δ .(s) (@lamexp_core.app .(Γ) t s a b) := lamexp_core.app (weaken_core a) (weaken_core b)
| Γ Δ (ty.arr .(t) .(s)) (@lamexp_core.abs .(Γ) t s a) :=
  lamexp_core.abs $ cast (by simp) (weaken_core a)

def weaken {Γ t} : lamexp t → lamexp_core Γ t :=
weaken_core

end lamexp
