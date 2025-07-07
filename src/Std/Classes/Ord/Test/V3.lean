section Prerequisites

inductive Noncomputable (α : Type u) where
  | comp : α → Noncomputable α
  | noncomp : (P : α → Prop) → (h : Nonempty (Subtype P)) → Noncomputable α

class Noncomputable' (α : Type u) where
  get : (choose : (P : α → Prop) → Nonempty (Subtype P) → α) → α
  get_const : ∀ c c', get c = get c'

attribute [class] Noncomputable

noncomputable def Noncomputable.inst [i : Noncomputable α] : α :=
  match i with
  | .comp a => a
  | .noncomp P _ => (Classical.ofNonempty : Subtype P)

noncomputable def Noncomputable'.inst [i : Noncomputable' α] : α :=
  i.get (fun P _ => (Classical.ofNonempty : Subtype P).val)

def Noncomputable'.comp {α : Type u} (a : α) : Noncomputable' α :=
  ⟨fun _ => a, fun _ _ => rfl⟩

end Prerequisites

section LT

class BLT (α : Type u) where
  LT : α → α → Bool

class LawfulBLT (α : Type u) [LT α] [BLT α] where
  lt_iff_lt : ∀ a b : α, LT.lt a b ↔ BLT.LT a b

instance [LT α] [BLT α] [LawfulBLT α] : DecidableLT α :=
  fun a b => if h : BLT.LT a b then .isTrue (LawfulBLT.lt_iff_lt .. |>.mpr h) else .isFalse (h.imp (LawfulBLT.lt_iff_lt ..).mp)

def LT.ofBLT (α : Type u) [BLT α] : LT α where
  lt a b := BLT.LT a b

end LT

section LE

class BLE (α : Type u) where
  LE : α → α → Bool

class LawfulBLE (α : Type u) [LE α] [BLE α] where
  le_iff_le : ∀ a b : α, LE.le a b ↔ BLE.LE a b

instance [LE α] [BLE α] [LawfulBLE α] : DecidableLE α :=
  fun a b => if h : BLE.LE a b then .isTrue (LawfulBLE.le_iff_le .. |>.mpr h) else .isFalse (h.imp (LawfulBLE.le_iff_le ..).mp)

def LE.ofBLE (α : Type u) [BLE α] : LE α where
  le a b := BLE.LE a b

end LE

section Ord

class NoncomputableOrd (α : Type u) where
  noncomputableOrd : Noncomputable' (Ord α)

def NoncomputableOrd.ofComputable {α : Type u} [Ord α] : NoncomputableOrd α where
  noncomputableOrd := .comp inferInstance

class LawfulOrd (α : Type u) [ni : NoncomputableOrd α] [ci : Ord α] where
  eq : ni.noncomputableOrd.inst = ci

instance {α : Type u} [NoncomputableOrd α] :
    haveI : Ord α := NoncomputableOrd.noncomputableOrd.inst
    LawfulOrd α :=
  letI : Ord α := NoncomputableOrd.noncomputableOrd.inst
  ⟨rfl⟩

example {α : Type u} [Ord α] :
    haveI : NoncomputableOrd α := NoncomputableOrd.ofComputable
    LawfulOrd α :=
  inferInstance

-- Making an `Ord` instance noncomputable and then computable again is definitionally equal to the
-- identity.
example {α : Type u} [Ord α] :
    NoncomputableOrd.ofComputable.noncomputableOrd.inst = (inferInstance : Ord α) :=
  rfl

end Ord

section BEq

class NoncomputableBEq (α : Type u) where
  noncomputableBEq : Noncomputable (BEq α)

def NoncomputableBEq.ofRel (P : α → α → Prop) : NoncomputableBEq α where
  noncomputableBEq :=
    .noncomp (fun i => open Classical in i = ⟨fun a b => decide (P a b)⟩) ⟨⟨_, rfl⟩⟩

def NoncomputableBEq.ofComputable {α : Type u} [BEq α] : NoncomputableBEq α where
  noncomputableBEq := .comp inferInstance

-- sadly, the canonical name is already taken
class LawfulComputableBEq (α : Type u) [ni : NoncomputableBEq α] [ci : BEq α] where
  eq : ni.noncomputableBEq.inst = ci

instance {α : Type u} [NoncomputableBEq α] :
    haveI : BEq α := NoncomputableBEq.noncomputableBEq.inst
    LawfulComputableBEq α :=
  letI : BEq α := NoncomputableBEq.noncomputableBEq.inst
  ⟨rfl⟩

end BEq

section PartiallyComparable

class PartiallyComparableMixin (α : Type u) [LT α] [LE α] [NoncomputableBEq α] : Prop

class PartiallyComparable (α : Type u) extends LT α, LE α, NoncomputableBEq α,
    PartiallyComparableMixin α

class LawfulPartiallyComparable (α : Type u) [LT α] [LE α] [NoncomputableBEq α] where
    lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by exact fun _ _ => Iff.rfl

structure PartiallyComparable.OfLEArgs (α : Type u) where
  instLE : LE α := by
    try (infer_instance; done)
    try (exact LE.ofBLE; done)
  instLT : LT α := by
    try (infer_instance; done)
    try (exact LT.ofBLT; done)
    try (exact ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩; done)
  instNoncomputableBEq : NoncomputableBEq α := by
    try (infer_instance; done)
    try (exact NoncomputableBEq.ofComputable; done)
    try (exact NoncomputableBEq.ofRel fun a b => a ≤ b ∧ b ≤ a; done)

def PartiallyComparable.ofLE (args : OfLEArgs α) : PartiallyComparable α where
  toLE := args.instLE
  toLT := args.instLT
  toNoncomputableBEq := args.instNoncomputableBEq

-- TODO: Do we want a variant that automatically spawns computable instances?

instance PartiallyComparable.lawful [LE α] :
    haveI : PartiallyComparable α := .ofLE {}
    LawfulPartiallyComparable α :=
  letI : PartiallyComparable α := .ofLE {}; {}

instance (α : Type u) [LE α] : PartiallyComparable α := .ofLE {}

end PartiallyComparable
