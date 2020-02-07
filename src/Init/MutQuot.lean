/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

universes u v

structure MutQuot {α : Type u} (r : α → α → Prop) :=
mkAux :: (val : Quot r)

attribute [extern "lean_mutquot_mk"] MutQuot.mkAux
attribute [extern "lean_mutquot_get", neverExtract] MutQuot.val

@[extern "lean_mutquot_mk"]
def MutQuot.mk {α : Type u} (r : α → α → Prop) (a : α) : MutQuot r :=
MutQuot.mkAux (Quot.mk r a)

@[extern "lean_mutquot_set", neverExtract]
unsafe def MutQuot.set {α : Type u} {β : Sort v} {r : α → α → Prop} (q : MutQuot r) (a : α) (b : β) : β := b

/- Internal efficient implementation for `MutQuot.liftUpdate` -/
@[inline] unsafe def MutQuot.liftUpdateUnsafe {α : Type u} {r : α → α → Prop} {β : Sort v}
    (f : α → PProd β α)
    (h₁ : ∀ (a₁ a₂ : α), r a₁ a₂ → (f a₁).1 = (f a₂).1)
    (h₂ : ∀ (a : α), r a (f a).2)
    (q : MutQuot r) : β :=
let ⟨b, a⟩ := f (cast lcProof q.val : α); MutQuot.set q a b

@[implementedBy MutQuot.liftUpdateUnsafe]
def MutQuot.liftUpdate {α : Type u} {r : α → α → Prop} {β : Sort v}
    (f : α → PProd β α)
    (h₁ : ∀ (a₁ a₂ : α), r a₁ a₂ → (f a₁).1 = (f a₂).1)
    (h₂ : ∀ (a : α), r a (f a).2)
    (q : MutQuot r) : β :=
Quot.lift (fun a => (f a).1) h₁ q.val

abbrev MutSquash (α : Type u) := @MutQuot α (fun _ _ => True)

/- Internal efficient implementation for `MutSquash.liftUpdate`. -/
@[inline] unsafe def MutSquash.liftUpdateUnsafe {α : Type u} {β : Sort v}
    (f : α → PProd β α)
    (h : ∀ (a₁ a₂ : α), (f a₁).1 = (f a₂).1)
    (init : α)
    (q : MutSquash α) : β :=
let a : α  := (cast lcProof q.val : α); -- rely on the fact that `@Quot α r` and `α` have the same runtime representation
let a : α  := MutQuot.set q init a;     -- reset value in `q` with `init`. The idea is to take the ownership of `a`.
let ⟨b, a⟩ := f a;                      -- If `q` was the only object referencing `a`, `f` will be able to perform destructive updates
MutQuot.set q a b

@[implementedBy MutSquash.liftUpdateUnsafe]
def MutSquash.liftUpdate {α : Type u} {β : Sort v}
    (f : α → PProd β α)
    (h : ∀ (a₁ a₂ : α), (f a₁).1 = (f a₂).1)
    (init : α)
    (q : MutSquash α) : β :=
MutQuot.liftUpdate f (fun a₁ a₂ _ => h a₁ a₂) (fun _ => True.intro) q

@[inline]
def MutQuot.lift {α : Type u} {r : α → α → Prop} {β : Sort v}
    (f : α → β)
    (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂)
    (q : MutQuot r) : β :=
Quot.lift f h q.val

@[elabAsEliminator]
theorem MutQuot.ind {α : Type u} {r : α → α → Prop} {β : MutQuot r → Prop} :
    (∀ (a : α), β (MutQuot.mk r a)) → ∀ (q : MutQuot r), β q :=
fun h ⟨q⟩ => Quot.ind (fun a => h a) q

theorem MutQuot.sound {α : Type u} {r : α → α → Prop} {a b : α} : r a b → MutQuot.mk r a = MutQuot.mk r b :=
fun h =>
  have Quot.mk r a = Quot.mk r b from Quot.sound h;
  show MutQuot.mkAux (Quot.mk r a) = MutQuot.mkAux (Quot.mk r b) from
    congrArg MutQuot.mkAux this

theorem MutQuot.liftUpdateBeta {α : Type u} {r : α → α → Prop} {β : Sort v}
    (f : α → PProd β α)
    (h₁ : ∀ (a₁ a₂ : α), r a₁ a₂ → (f a₁).1 = (f a₂).1)
    (h₂ : ∀ (a : α), r a (f a).2)
    (a : α) : MutQuot.liftUpdate f h₁ h₂ (MutQuot.mk r a) = (f a).1 :=
rfl

theorem MutQuot.liftBeta {α : Type u} {r : α → α → Prop} {β : Sort v}
    (f : α → β)
    (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂)
    (a : α) : MutQuot.lift f h (MutQuot.mk r a) = f a :=
rfl

theorem MutQuot.indBeta {α : Type u} {r : α → α → Prop} {β : MutQuot r → Prop}
    (p : ∀ a, β (MutQuot.mk r a)) (a : α) : (MutQuot.ind p (MutQuot.mk r a) : β (MutQuot.mk r a)) = p a :=
rfl

theorem MutQuot.existsRep {α : Type u} {r : α → α → Prop} (q : MutQuot r) : Exists (fun a => (MutQuot.mk r a) = q) :=
MutQuot.ind (fun a => ⟨a, rfl⟩) q

section
variable {α : Type u}
variable {r : α → α → Prop}
variable {β : MutQuot r → Sort v}

@[reducible, macroInline]
protected def MutQuot.indep (f : ∀ a, β (MutQuot.mk r a)) (a : α) : PSigma β :=
⟨MutQuot.mk r a, f a⟩

theorem MutQuot.indepCoherent
    (f : ∀ a, β (MutQuot.mk r a))
    (h : ∀ (a b : α) (p : r a b), (Eq.rec (f a) (MutQuot.sound p) : β (MutQuot.mk r b)) = f b)
    : ∀ a b, r a b → MutQuot.indep f a = MutQuot.indep f b  :=
fun a b e => PSigma.eq (MutQuot.sound e) (h a b e)

theorem MutQuot.liftIndepPr1
  (f : ∀ a, β (MutQuot.mk r a)) (h : ∀ (a b : α) (p : r a b), (Eq.rec (f a) (MutQuot.sound p) : β (MutQuot.mk r b)) = f b)
  (q : MutQuot r) : (MutQuot.lift (MutQuot.indep f) (MutQuot.indepCoherent f h) q).1 = q  :=
MutQuot.ind (fun (a : α) => Eq.refl (MutQuot.indep f a).1) q

@[reducible, elabAsEliminator, inline]
protected def MutQuot.dlift
   (f : ∀ a, β (MutQuot.mk r a)) (h : ∀ (a b : α) (p : r a b), (Eq.rec (f a) (MutQuot.sound p) : β (MutQuot.mk r b)) = f b)
   (q : MutQuot r) : β q :=
Eq.ndrecOn (MutQuot.liftIndepPr1 f h q) ((MutQuot.lift (MutQuot.indep f) (MutQuot.indepCoherent f h) q).2)

@[reducible, elabAsEliminator, inline]
def MutQuot.liftSubsingleton
   [h : ∀ a, Subsingleton (β (MutQuot.mk r a))] (f : ∀ a, β (MutQuot.mk r a)) (q : MutQuot r) : β q :=
MutQuot.dlift f (fun a b h => Subsingleton.elim _ (f b)) q

end
