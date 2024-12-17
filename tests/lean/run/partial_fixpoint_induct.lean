-- These can move to Init after a stage0 update
open Lean.Order in
attribute [partial_fixpoint_monotone]
  monotone_ite
  monotone_dite
  monotone_bind
  monotone_mapM
  monotone_mapFinIdxM


def loop (x : Nat) : Unit := loop (x + 1)
partial_fixpoint

/--
info: loop.fixpoint_induct (motive : (Nat → Unit) → Prop) (adm : Lean.Order.admissible motive)
  (h : ∀ (x : Nat → Unit), motive x → motive fun x_1 => x (x_1 + 1)) :
  motive (Lean.Order.fix (fun f x => f (x + 1)) loop.proof_3)
-/
#guard_msgs in #check loop.fixpoint_induct


def find (P : Nat → Bool) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    find P (x +1)
partial_fixpoint

/--
info: find.fixpoint_induct (P : Nat → Bool) (motive : (Nat → Option Nat) → Prop) (adm : Lean.Order.admissible motive)
  (h : ∀ (x : Nat → Option Nat), motive x → motive fun x_1 => if P x_1 = true then some x_1 else x (x_1 + 1)) :
  motive (Lean.Order.fix (fun f x => if P x = true then some x else f (x + 1)) ⋯)
-/
#guard_msgs in #check find.fixpoint_induct


def fib (n : Nat) := go 0 0 1
where
  go i fip fi :=
    if i = n then
      fi
    else
      go (i + 1) fi (fi + fip)
  partial_fixpoint

/--
info: fib.go.fixpoint_induct (n : Nat) (motive : (Nat → Nat → Nat → Nat) → Prop) (adm : Lean.Order.admissible motive)
  (h : ∀ (x : Nat → Nat → Nat → Nat), motive x → motive fun i fip fi => if i = n then fi else x (i + 1) fi (fi + fip)) :
  motive (Lean.Order.fix (fun f i fip fi => if i = n then fi else f (i + 1) fi (fi + fip)) ⋯)
-/
#guard_msgs in #check fib.go.fixpoint_induct


local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (cond b α β) := by
  cases b <;> assumption
local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (if b then α else β) := by
  split <;> assumption

mutual
def dependent2''a (m n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2''a m (n + 1) b else dependent2''b m (n + m) b
partial_fixpoint
def dependent2''b (m n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2''c m (n + 1) b else dependent2''b m (n + m) b
partial_fixpoint
def dependent2''c (m n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2''a m (n + 1) b else dependent2''b m (n + m) b
partial_fixpoint
end

/--
info: dependent2''a.fixpoint_induct (m : Nat)
  (motive_1 motive_2 motive_3 : (Nat → (b : Bool) → if b = true then Nat else Bool) → Prop)
  (adm_1 : Lean.Order.admissible motive_1) (adm_2 : Lean.Order.admissible motive_2)
  (adm_3 : Lean.Order.admissible motive_3)
  (h :
    ∀
      (x :
        (Nat → (b : Bool) → if b = true then Nat else Bool) ×'
          (Nat → (b : Bool) → if b = true then Nat else Bool) ×' (Nat → (b : Bool) → if b = true then Nat else Bool)),
      motive_1 x.1 ∧ motive_2 x.2.1 ∧ motive_3 x.2.2 →
        motive_1
            ⟨fun n b => if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                if x_1 : b = true then x.2.2 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b⟩.1 ∧
          motive_2
              ⟨fun n b => if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                    if x_1 : b = true then x.2.2 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                    if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b⟩.2.1 ∧
            motive_3
              ⟨fun n b => if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                    if x_1 : b = true then x.2.2 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                    if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b⟩.2.2) :
  motive_1
      (Lean.Order.fix
          (fun x =>
            ⟨fun n b => if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b, fun n b =>
              if x_1 : b = true then x.2.2 (n + 1) b else x.2.1 (n + m) b, fun n b =>
              if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b⟩)
          ⋯).1 ∧
    motive_2
        (Lean.Order.fix
              (fun x =>
                ⟨fun n b => if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                  if x_1 : b = true then x.2.2 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                  if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b⟩)
              ⋯).2.1 ∧
      motive_3
        (Lean.Order.fix
              (fun x =>
                ⟨fun n b => if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                  if x_1 : b = true then x.2.2 (n + 1) b else x.2.1 (n + m) b, fun n b =>
                  if x_1 : b = true then x.1 (n + 1) b else x.2.1 (n + m) b⟩)
              ⋯).2.2
-/
#guard_msgs in #check dependent2''a.fixpoint_induct

/-- error: unknown constant 'dependent2''b.fixpoint_induct' -/
#guard_msgs in #check dependent2''b.fixpoint_induct
