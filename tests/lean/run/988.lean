instance {α : Type u} : HAppend (Fin m → α) (Fin n → α) (Fin (m + n) → α) where
  hAppend a b i := if h : i < m then a ⟨i, h⟩ else b ⟨i - m, sorry⟩

def empty : Fin 0 → Nat := (nomatch ·)

theorem append_empty (x : Fin i → Nat) : x ++ empty = x :=
  funext fun i => dif_pos _

constant f : (Fin 0 → Nat) → Prop
example : f (empty ++ empty) = f empty := by simp only [append_empty] -- should work

@[congr] theorem Array.get_congr (as bs : Array α) (h : as = bs) (i : Fin as.size) (j : Nat) (hi : i = j) :
    as.get i = bs.get ⟨j, h ▸ hi ▸ i.2⟩ := by
  subst bs; subst j; rfl

example (as : Array Nat) (h : 0 + x < as.size) :
    as.get ⟨0 + x, h⟩ = as.get ⟨x, Nat.zero_add x ▸ h⟩ := by
  simp -- should work

example (as : Array (Nat → Nat)) (h : 0 + x < as.size) :
    as.get ⟨0 + x, h⟩ i = as.get ⟨x, Nat.zero_add x ▸ h⟩ i := by
  simp -- should also work

example (as : Array (Nat → Nat)) (h : 0 + x < as.size) :
    as.get ⟨0 + x, h⟩ i = as.get ⟨x, Nat.zero_add x ▸ h⟩ (0+i) := by
  simp -- should also work

-- TODO: generate the following lemma automatically
@[congr] theorem decide_congr (p q : Prop) (h : p = q) [s₁ : Decidable p] [s₂ : Decidable q] : decide p = decide q := by
  subst h
  have : s₁ = s₂ := Subsingleton.elim s₁ s₂
  subst this
  rfl

example [Decidable p] : decide (p ∧ True) = decide p := by simp -- should work

def Pi.single [DecidableEq ι] {f : ι → Type u} [∀ i, Inhabited (f i)] (i : ι) (x : f i) : ∀ i, f i :=
  fun j => if h : j = i then h ▸ x else default

structure Set (α : Type u) where of :: mem : α → Prop

instance : CoeSort (Set α) (Type u) where coe s := Subtype s.mem

@[congr]
theorem dep_congr [DecidableEq ι] {p : ι → Set α} [∀ i, Inhabited (p i)] :
    ∀ {i j} (h : i = j) (x : p i) (y : α) (hx : x = y), Pi.single (f := (p ·)) i x = Pi.single (f := (p ·)) j ⟨y, hx ▸ h ▸ x.2⟩
  | _, _, rfl, _, _, rfl => rfl

theorem aux {p : Nat → Set Nat} {i j y : Nat} (x : p j) (h₁ : x = y) (h₂ : i = j) : Set.mem (p i) y := by
  have := x.2
  subst h₁ h₂
  assumption

example {p : Nat → Set Nat} [∀ i, Inhabited (p i)] (i : Nat) (x : p (0 + i)) (y : Nat) : Pi.single (f := (p ·)) (0 + i) x = Pi.single (f := (p ·)) i ⟨x, aux x rfl (Nat.zero_add i).symm ⟩ := by
  simp
