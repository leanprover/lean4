set_option pp.universes false in

inductive Vec.{u} (α : Type) : Nat → Type u where
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

/--
info: @[reducible] def Vec.withCtorType.{v, u} : Type → Type v → Nat → Type (max u v) :=
fun α P ctorIdx => bif ctorIdx.blt 1 then PUnit → P else PUnit → {n : Nat} → α → Vec α n → P
-/
#guard_msgs in
#print Vec.withCtorType

/--
info: @[reducible] def Vec.withCtor.{v, u} : (α : Type) →
  (P : Type v) → (ctorIdx : Nat) → Vec.withCtorType α P ctorIdx → P → (a : Nat) → Vec α a → P :=
fun α P ctorIdx k k' a x =>
  Vec.casesOn x (if h : ctorIdx = 0 then (h ▸ k) PUnit.unit else k') fun {n} a a_1 =>
    if h : ctorIdx = 1 then (h ▸ k) PUnit.unit a a_1 else k'
-/
#guard_msgs in
#print Vec.withCtor

/--
info: @[reducible] def Vec.noConfusionType.{u_1, u} : {α : Type} → {a : Nat} → Sort u_1 → Vec α a → Vec α a → Sort u_1 :=
fun {α} {a} P x1 x2 =>
  Vec.casesOn x1 (Vec.withCtor α (Sort u_1) 0 (fun x => P → P) P a x2) fun {n} a_1 a_2 =>
    Vec.withCtor α (Sort u_1) 1 (fun x {n_1} a a_3 => (n = n_1 → a_1 = a → HEq a_2 a_3 → P) → P) P a x2
-/
#guard_msgs in
#print Vec.noConfusionType

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
