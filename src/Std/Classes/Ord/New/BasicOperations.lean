module

prelude
import Init.Core
public import Init.Data.Ord
public import Std.Classes.Ord.New.Util

public section

section LT

class BLT (α : Type u) where
  LT : α → α → Bool

class LawfulBLT (α : Type u) [LT α] [BLT α] where
  lt_iff_lt : ∀ a b : α, LT.lt a b ↔ BLT.LT a b

instance [LT α] [BLT α] [LawfulBLT α] : DecidableLT α :=
  fun a b => if h : BLT.LT a b then .isTrue (LawfulBLT.lt_iff_lt .. |>.mpr h) else .isFalse (h.imp (LawfulBLT.lt_iff_lt ..).mp)

def LT.ofBLT (α : Type u) [BLT α] : LT α where
  lt a b := BLT.LT a b

instance [BLT α] :
    haveI : LT α := LT.ofBLT α
    LawfulBLT α :=
  letI : LT α := LT.ofBLT α
  ⟨by simp [LT.ofBLT]⟩

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

instance [BLE α] :
    haveI : LE α := LE.ofBLE α
    LawfulBLE α :=
  letI : LE α := LE.ofBLE α
  ⟨by simp [LE.ofBLE]⟩

end LE

section Ord

class NoncomputableOrd (α : Type u) where
  noncomputableOrd : Noncomputable (Ord α)

def NoncomputableOrd.ofComputable {α : Type u} [Ord α] : NoncomputableOrd α where
  noncomputableOrd := .comp inferInstance

class LawfulOrd (α : Type u) [ni : NoncomputableOrd α] [ci : Ord α] where
  eq : ni.noncomputableOrd.inst = ci

noncomputable def NoncomputableOrd.compare {α : Type u} [NoncomputableOrd α] (a b : α) : Ordering :=
  noncomputableOrd.inst.compare a b

theorem LawfulOrd.compare_eq_compare {α : Type u} [NoncomputableOrd α] [Ord α] [LawfulOrd α]
    {a b : α} : NoncomputableOrd.compare a b = Ord.compare a b := by
  simp [NoncomputableOrd.compare, LawfulOrd.eq]

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

instance [Ord α] :
    haveI : NoncomputableOrd α := NoncomputableOrd.ofComputable
    LawfulOrd α :=
  letI : NoncomputableOrd α := NoncomputableOrd.ofComputable
  ⟨by simp [NoncomputableOrd.ofComputable, Noncomputable.inst]⟩

end Ord

section BEq

/-!
One might consider using `HasEquiv.{u, 0}` instead of `NoncomputableBEq`.
-/

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

instance [BEq α] :
    haveI : NoncomputableBEq α := NoncomputableBEq.ofComputable
    LawfulComputableBEq α :=
  letI : NoncomputableBEq α := NoncomputableBEq.ofComputable
  ⟨by simp [NoncomputableBEq.ofComputable, Noncomputable.inst]⟩

end BEq

namespace Classical.Order

noncomputable section

scoped instance (priority := low) ordOfNoncomputableOrd [NoncomputableOrd α] : Ord α :=
  NoncomputableOrd.noncomputableOrd.inst

end

end Classical.Order
