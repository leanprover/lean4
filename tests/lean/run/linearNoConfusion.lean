/-!
This test tests and also explains the noConfusionType construction.

It contains copies of the definitions of the constructions, for manual experimentation with
the code, and uses `#guard_msgs` and `rfl` to compare them to the generated ones.

This also serves as documentation to the `NoConfusionLinear` module, so do not delete or remove
from this file without updating that module's docstring.
-/

inductive Vec.{u} (α : Type) : Nat → Type u where
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

@[reducible] protected def Vec.noConfusionType.withCtorType'.{u_1, u} :
    Type → Type u_1 → Nat → Type (max (u + 1) u_1) := fun α P ctorIdx =>
  bif Nat.blt ctorIdx 1
  then PUnit.{u + 2} → P
  else PUnit.{u + 2} → {n : Nat} → α → Vec.{u} α n → P

/--
info: @[reducible] protected def Vec.noConfusionType.withCtorType.{u_1, u} : Type → Type u_1 → Nat → Type (max (u + 1) u_1) :=
fun α P ctorIdx => bif ctorIdx.blt 1 then PUnit → P else PUnit → {n : Nat} → α → Vec α n → P
-/
#guard_msgs in
#print Vec.noConfusionType.withCtorType

example : @Vec.noConfusionType.withCtorType.{u_1,u} = @Vec.noConfusionType.withCtorType'.{u_1,u} := rfl

@[reducible] protected noncomputable def Vec.noConfusionType.withCtor'.{u_1, u} : (α : Type) →
  (P : Type u_1) → (ctorIdx : Nat) → Vec.noConfusionType.withCtorType' α P ctorIdx → P → (a : Nat) → Vec.{u} α a → P :=
fun _α _P ctorIdx k k' _a x =>
  Vec.casesOn x
    (if h : ctorIdx = 0 then Eq.ndrec k h PUnit.unit else k')
    (fun a a_1 => if h : ctorIdx = 1 then Eq.ndrec k h PUnit.unit a a_1 else k')

/--
info: @[reducible] protected def Vec.noConfusionType.withCtor.{u_1, u} : (α : Type) →
  (P : Type u_1) → (ctorIdx : Nat) → Vec.noConfusionType.withCtorType α P ctorIdx → P → (a : Nat) → Vec α a → P :=
fun α P ctorIdx k k' a x =>
  Vec.casesOn x (if h : ctorIdx = 0 then (h ▸ k) PUnit.unit else k') fun {n} a a_1 =>
    if h : ctorIdx = 1 then (h ▸ k) PUnit.unit a a_1 else k'
-/
#guard_msgs in
#print Vec.noConfusionType.withCtor

example : @Vec.noConfusionType.withCtor.{u_1,u} = @Vec.noConfusionType.withCtor'.{u_1,u} := rfl

@[reducible] protected def Vec.noConfusionType'.{u_1, u} : {α : Type} →
  {a : Nat} → Sort u_1 → Vec.{u} α a → Vec α a → Sort u_1 :=
fun {α} {a} P x1 x2 =>
  Vec.casesOn x1
    (Vec.noConfusionType.withCtor' α (Sort u_1) 0 (fun _x => P → P) P a x2)
    (fun {n} a_1 a_2 => Vec.noConfusionType.withCtor' α (Sort u_1) 1 (fun _x {n_1} a a_3 => (n = n_1 → a_1 = a → a_2 ≍ a_3 → P) → P) P a x2)

/--
info: @[reducible] protected def Vec.noConfusionType.{u_1, u} : {α : Type} →
  {a : Nat} → Sort u_1 → Vec α a → Vec α a → Sort u_1 :=
fun {α} {a} P x1 x2 =>
  Vec.casesOn x1 (Vec.noConfusionType.withCtor α (Sort u_1) 0 (fun x => P → P) P a x2) fun {n} a_1 a_2 =>
    Vec.noConfusionType.withCtor α (Sort u_1) 1 (fun x {n_1} a a_3 => (n = n_1 → a_1 = a → a_2 ≍ a_3 → P) → P) P a x2
-/
#guard_msgs in
#print Vec.noConfusionType

example : @Vec.noConfusionType.{u_1,u} = @Vec.noConfusionType'.{u_1,u} := rfl

/-
run_meta do
  let mut i := 0
  for (n, _c) in (← getEnv).constants do
    if let .str indName "noConfusion" := n then
      let ConstantInfo.inductInfo _ ← getConstInfo indName | continue
      logInfo m!"Looking at {.ofConstName indName}"
      mkToCtorIdx' indName
      mkWithCtorType indName
      mkWithCtor indName
      mkNoConfusionType' indName
      i := i + 1
      if i > 10 then
        return
-/

-- inductive Enum.{u} : Type u where | a | b
-- set_option pp.universes true in
-- #print noConfusionTypeEnum
