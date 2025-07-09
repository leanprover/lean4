module

prelude
public import Init.Core

public section

inductive Noncomputable (α : Type u) where
  | comp : α → Noncomputable α
  | noncomp : (P : α → Prop) → (h : Nonempty (Subtype P)) → Noncomputable α

class Noncomputable' (α : Type u) where
  get : (choose : (P : α → Prop) → Nonempty (Subtype P) → α) → α
  get_const : ∀ c c', get c = get c'

attribute [class] Noncomputable

@[expose]
noncomputable def Noncomputable.inst [i : Noncomputable α] : α :=
  match i with
  | .comp a => a
  | .noncomp P _ => (Classical.ofNonempty : Subtype P)

@[expose]
noncomputable def Noncomputable'.inst [i : Noncomputable' α] : α :=
  i.get (fun P _ => (Classical.ofNonempty : Subtype P).val)

@[expose]
def Noncomputable'.comp {α : Type u} (a : α) : Noncomputable' α :=
  ⟨fun _ => a, fun _ _ => rfl⟩
