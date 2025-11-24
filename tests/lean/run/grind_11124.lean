example (a b : List Nat)
    : a ≍ ([] : List Int) → b ≍ ([1] : List Int) → a = b ∨ p → p := by
  grind

example (a b : List Nat)
    : a = [] → a ≍ ([] : List Int) → b = [1] → a = b ∨ p → p := by
  grind

example (a b : List Nat)
    : a = [] → a ≍ ([] : List Int) → b = [1] → b ≍ [(1 : Int)] → a = b ∨ p → p := by
  grind

example (a b : List Nat)
    : a = [] → b = [1] → a = b ∨ p → p := by
  grind

example (a b : List Nat)
    : a = [] → a ≍ ([] : List Int) → b = [1] → a = b ∨ p → p := by
  grind

/--
error: `grind` failed
case grind
p : Prop
a b : List Nat
h : a = []
h_1 : b ≍ [1]
h_2 : a = b ∨ p
h_3 : ¬p
⊢ False
-/
#guard_msgs in
example (a b : List Nat)
    : a = [] → b ≍ ([1] : List Int) → a = b ∨ p → p := by
  grind -verbose


section Mathlib.Data.List.Sigma

namespace List

variable {β : α → Type}

def keys : List (Sigma β) → List α :=
  map Sigma.fst

@[grind =]
theorem mem_keys {a} {l : List (Sigma β)} : a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l := sorry

def NodupKeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup

theorem notMem_keys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    s.1 ∉ l.keys := sorry

variable [DecidableEq α]

def dlookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else dlookup a l

@[grind =]
theorem dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a (⟨a, b⟩ :: l) = some b := sorry

theorem dlookup_eq_none {a : α} {l : List (Sigma β)} : dlookup a l = none ↔ a ∉ l.keys := sorry

theorem of_mem_dlookup {a : α} {b : β a} {l : List (Sigma β)} :
    b ∈ dlookup a l → Sigma.mk a b ∈ l := sorry

theorem map_dlookup_eq_find (a : α) (l : List (Sigma β)) :
    (dlookup a l).map (Sigma.mk a) = find? (fun s => a = s.1) l := sorry

theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKeys)
    (h : ∀ x y, y ∈ l₀.dlookup x ↔ y ∈ l₁.dlookup x) : l₀ ~ l₁ := sorry

def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  eraseP fun s => a = s.1

def kunion : List (Sigma β) → List (Sigma β) → List (Sigma β)
  | [], l₂ => l₂
  | s :: l₁, l₂ => s :: kunion l₁ (kerase s.1 l₂)

end List

end Mathlib.Data.List.Sigma

section Mathlib.Data.List.AList

open List

variable {α : Type} {β : α → Type}

structure AList (β : α → Type) where
  entries : List (Sigma β)

namespace AList

def keys (s : AList β) : List α := sorry

variable [DecidableEq α]

instance : Union (AList β) := sorry

theorem union_entries {s₁ s₂ : AList β} : (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
  sorry

/-- Two associative lists are disjoint if they have no common keys. -/
def Disjoint (s₁ s₂ : AList β) : Prop :=
  ∀ k ∈ s₁.keys, k ∉ s₂.keys

/--
error: `grind` failed
case grind.1.1.2.2.1.1.1
α : Type
β : α → Type
inst : DecidableEq α
s₁ s₂ : AList β
h : s₁.Disjoint s₂
x : α
y : β x
h_1 : (y ∈ dlookup x (s₁.entries.kunion s₂.entries)) = ¬y ∈ dlookup x (s₂.entries.kunion s₁.entries)
left : y ∈ dlookup x (s₁.entries.kunion s₂.entries)
right : ¬y ∈ dlookup x (s₂.entries.kunion s₁.entries)
left_1 : dlookup x (s₂.entries.kunion s₁.entries) = none
right_1 : ¬x ∈ (s₂.entries.kunion s₁.entries).keys
left_2 : ¬dlookup x (s₁.entries.kunion s₂.entries) = none
right_2 : x ∈ (s₁.entries.kunion s₂.entries).keys
w : β x
h_5 : ⟨x, w⟩ ∈ s₁.entries.kunion s₂.entries
left_3 : ¬find? (fun s => decide (x = s.fst)) (s₁.entries.kunion s₂.entries) = none
right_3 : ¬∀ (x_1 : Sigma β), x_1 ∈ s₁.entries.kunion s₂.entries → decide (x = x_1.fst) = false
w_1 : Sigma β
h_8 : ¬(w_1 ∈ s₁.entries.kunion s₂.entries → decide (x = w_1.fst) = false)
w_2 : Sigma β
h_10 : ¬(w_2 ∈ s₁.entries.kunion s₂.entries → decide (w_1.fst = w_2.fst) = false)
w_3 : Sigma β
h_12 : ¬(w_3 ∈ s₁.entries.kunion s₂.entries → decide (w_2.fst = w_3.fst) = false)
h_13 : (fun s => decide (w_1.fst = s.fst)) = fun s => decide (x = s.fst)
left_4 : ⟨x, cast ⋯ w_1.snd⟩ ∈ ⟨x, w⟩ :: s₂.entries.kunion s₁.entries
right_4 : ⟨x, cast ⋯ w_1.snd⟩ = ⟨x, w⟩ ∨ ⟨x, cast ⋯ w_1.snd⟩ ∈ s₂.entries.kunion s₁.entries
h_15 : (fun s => decide (w_2.fst = s.fst)) = fun s => decide (x = s.fst)
⊢ False
-/
#guard_msgs in
theorem union_comm_of_disjoint {s₁ s₂ : AList β} (h : Disjoint s₁ s₂) :
    (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
  lookup_ext sorry sorry
    (by
      intros; simp only [union_entries]
      grind -verbose [
      dlookup_eq_none,
      map_dlookup_eq_find,
      of_mem_dlookup,
      notMem_keys_of_nodupKeys_cons
      ]
    )

end AList

end Mathlib.Data.List.AList
