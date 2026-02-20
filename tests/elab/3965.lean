section Mathlib.Logic.Function.Iterate

universe u v

variable {α : Type u}

/-- Iterate a function. -/
def Nat.iterate {α : Sort u} (op : α → α) : Nat → α → α := sorry

notation:max f "^["n"]" => Nat.iterate f n

theorem Function.iterate_succ' (f : α → α) (n : Nat) : f^[n.succ] = f ∘ f^[n] := sorry

end Mathlib.Logic.Function.Iterate

section Mathlib.Data.Quot

variable {α : Sort _}

noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α := sorry

end Mathlib.Data.Quot

section Mathlib.Init.Order.Defs

universe u
variable {α : Type u}

section Preorder

class Preorder (α : Type u) extends LE α, LT α where

variable [Preorder α]

theorem lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c := sorry

end Preorder

variable [LE α]

theorem le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := sorry

end Mathlib.Init.Order.Defs

section Mathlib.Order.RelClasses

universe u

class IsWellOrder (α : Type u) (r : α → α → Prop) : Prop

end Mathlib.Order.RelClasses

section Mathlib.Order.SetNotation

universe u v
variable {α : Type u} {ι : Sort v}

class SupSet (α : Type _) where

def iSup [SupSet α] (s : ι → α) : α := sorry

end Mathlib.Order.SetNotation

section Mathlib.SetTheory.Ordinal.Basic

noncomputable section

universe u v w

variable {α : Type u}

structure WellOrder : Type (u + 1) where
  α : Type u

instance Ordinal.isEquivalent : Setoid WellOrder := sorry

def Ordinal : Type (u + 1) := Quotient Ordinal.isEquivalent

instance (o : Ordinal) : LT o.out.α := sorry

namespace Ordinal

def typein (r : α → α → Prop) [IsWellOrder α r] (a : α) : Ordinal := sorry

instance partialOrder : Preorder Ordinal := sorry

theorem typein_lt_self {o : Ordinal} (i : o.out.α) :
    @typein _ (· < ·) sorry i < o := sorry

instance : SupSet Ordinal := sorry

end Ordinal

end

end Mathlib.SetTheory.Ordinal.Basic

section Mathlib.SetTheory.Ordinal.Arithmetic

noncomputable section

universe u v w

namespace Ordinal

def sup {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup f

def lsub {ι} (f : ι → Ordinal) : Ordinal :=
  sup f

def blsub₂ (o₁ o₂ : Ordinal) (op : {a : Ordinal} → (a < o₁) → {b : Ordinal} → (b < o₂) → Ordinal) :
    Ordinal :=
  lsub (fun x : o₁.out.α × o₂.out.α => op (typein_lt_self x.1) (typein_lt_self x.2))

theorem lt_blsub₂ {o₁ o₂ : Ordinal}
    (op : {a : Ordinal} → (a < o₁) → {b : Ordinal} → (b < o₂) → Ordinal) {a b : Ordinal}
    (ha : a < o₁) (hb : b < o₂) : op ha hb < blsub₂ o₁ o₂ op := sorry


end Ordinal

end

end Mathlib.SetTheory.Ordinal.Arithmetic

section Mathlib.SetTheory.Ordinal.FixedPoint

noncomputable section

universe u v

namespace Ordinal

section

variable {ι : Type u} {f : ι → Ordinal.{max u v} → Ordinal.{max u v}}

def nfpFamily (f : ι → Ordinal → Ordinal) (a : Ordinal) : Ordinal :=
  sup (List.foldr f a)

end

section

variable {f : Ordinal.{u} → Ordinal.{u}}

def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f

theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < f^[n] b := sorry

end

end Ordinal

end

end Mathlib.SetTheory.Ordinal.FixedPoint

section Mathlib.SetTheory.Ordinal.Principal

universe u v w

namespace Ordinal

def Principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_nfp_blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b)) o) :=
  fun a b ha hb => by
  rw [lt_nfp] at *
  rcases ha with ⟨m, hm⟩
  rcases hb with ⟨n, hn⟩
  rcases le_total
    ((fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b))^[m] o)
    ((fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b))^[n] o) with h | h
  · refine ⟨n+1, ?_⟩
    rw [Function.iterate_succ']
    -- after https://github.com/leanprover/lean4/pull/3965 this requires `lt_blsub₂.{u}` or we get
    -- `stuck at solving universe constraint max u ?v =?= u`
    -- Note that there are two solutions: 0 and u. Both of them work.
    -- However, when `Meta.Config.univApprox := true`, we solve using `?v := u`
    exact lt_blsub₂ (@fun a _ b _ => op a b) (lt_of_lt_of_le hm h) hn
  · sorry

-- Trying again with 0
theorem principal_nfp_blsub₂' (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b)) o) :=
  fun a b ha hb => by
  rw [lt_nfp] at *
  rcases ha with ⟨m, hm⟩
  rcases hb with ⟨n, hn⟩
  rcases le_total
    ((fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b))^[m] o)
    ((fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b))^[n] o) with h | h
  · refine ⟨n+1, ?_⟩
    rw [Function.iterate_succ']
    -- universe 0 also works here
    exact lt_blsub₂.{_, _, 0} (@fun a _ b _ => op a b) (lt_of_lt_of_le hm h) hn
  · sorry


end Ordinal

end Mathlib.SetTheory.Ordinal.Principal
