import Lean.Elab.Binders

/-!

This is a test case extracted from Mathlib exhibiting a slow-down in `IsDefEq` after
https://github.com/leanprover/lean4/pull/3807

I've tried to keep this representative of the problem as it exhibits in Mathlib.
Further minimization is certainly possible,
but I think it makes a better test case going forward as is.

The original declaration take around 16,000 heartbeats prior to #3807, but around 210,000 after.

-/



section Mathlib.Tactic.Spread

open Lean Parser.Term Macro

syntax (name := letImplDetailStx) "let_impl_detail " ident " := " term "; " term : term

open Lean Elab Term Meta

@[term_elab letImplDetailStx]
def elabLetImplDetail : TermElab := fun stx expectedType? =>
  match stx with
  | `(let_impl_detail $id := $valStx; $body) => do
    let val ← elabTerm valStx none
    let type ← inferType val
    trace[Elab.let.decl] "{id.getId} : {type} := {val}"
    let result ←
      withLetDecl id.getId (kind := .default) type val fun x => do
        addLocalVarInfo id x
        let lctx ← getLCtx
        let lctx := lctx.modifyLocalDecl x.fvarId! fun decl => decl.setKind .implDetail
        withLCtx lctx (← getLocalInstances) do
          let body ← elabTermEnsuringType body expectedType?
          let body ← instantiateMVars body
          mkLetFVars #[x] body (usedLetOnly := false)
    pure result
  | _ => throwUnsupportedSyntax

macro_rules
| `({ $[$srcs,* with]? $[$fields],* $[: $ty?]? }) => show MacroM Term from do
    let mut spreads := #[]
    let mut newFields := #[]

    for field in fields do
      match field.1 with
        | `(structInstField| $name:ident := $arg) =>
          if name.getId.eraseMacroScopes == `__ then do
            spreads := spreads.push arg
          else
            newFields := newFields.push field
        | _ =>
          throwUnsupported

    if spreads.isEmpty then throwUnsupported

    let spreadData ← withFreshMacroScope <| spreads.mapIdxM fun i spread => do
      let n := Name.num `__spread i
      return (mkIdent <| ← Macro.addMacroScope n, spread)

    let srcs := (srcs.map (·.getElems)).getD {} ++ spreadData.map Prod.fst
    let body ← `({ $srcs,* with $[$newFields],* $[: $ty?]? })
    spreadData.foldrM (init := body) fun (id, val) body => `(let_impl_detail $id := $val; $body)

end Mathlib.Tactic.Spread

section Mathlib.Init.Order.Defs

universe u

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

theorem le_rfl {α} [Preorder α] {a : α} : a ≤ a :=
  Preorder.le_refl a

class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

end Mathlib.Init.Order.Defs

section Mathlib.Init.Function

universe u₁ u₂

namespace Function

variable {α : Sort u₁} {β : Sort u₂}

def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

def LeftInverse (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x

def HasLeftInverse (f : α → β) : Prop :=
  ∃ finv : β → α, LeftInverse finv f

end Function

end Mathlib.Init.Function

section Mathlib.Init.Set

set_option autoImplicit true

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α := p

namespace Set

protected def Mem (s : Set α) (a : α) : Prop := s a

instance : Membership α (Set α) := ⟨Set.Mem⟩

protected def Subset (s₁ s₂ : Set α) := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : LE (Set α) := ⟨Set.Subset⟩

instance : HasSubset (Set α) := ⟨(· ≤ ·)⟩

instance : EmptyCollection (Set α) := ⟨fun _ ↦ False⟩

def univ : Set α := setOf fun _ ↦ True

protected def union (s₁ s₂ : Set α) : Set α := setOf fun a => a ∈ s₁ ∨ a ∈ s₂

instance : Union (Set α) := ⟨Set.union⟩

protected def inter (s₁ s₂ : Set α) : Set α := setOf fun a => a ∈ s₁ ∧ a ∈ s₂

instance : Inter (Set α) := ⟨Set.inter⟩

protected def diff (s t : Set α) : Set α := setOf fun a => a ∈ s ∧ a ∉ t

instance : SDiff (Set α) := ⟨Set.diff⟩

def image (f : α → β) (s : Set α) : Set β := setOf fun b =>  ∃ a ∈ s, f a = b


end Set


end Mathlib.Init.Set

section Mathlib.Logic.Nonempty

instance (priority := 20) Zero.instNonempty {α} [Zero α] : Nonempty α := ⟨0⟩

protected noncomputable def Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h

end Mathlib.Logic.Nonempty

section Mathlib.Logic.Function.Basic

universe u

namespace Function

variable {α β : Sort _} [Nonempty α] {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=
  fun y ↦ if h : (∃ x, f x = y) then h.choose else Classical.arbitrary α

theorem Injective.hasLeftInverse (hf : Injective f) : HasLeftInverse f :=
  ⟨invFun f, sorry⟩

end Function

end Mathlib.Logic.Function.Basic

section Mathlib.Data.FunLike.Basic

class DFunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  coe : F → ∀ a : α, β a

abbrev FunLike F α β := DFunLike F α fun _ => β

instance (priority := 100) hasCoeToFun {F α β} [DFunLike F α β] : CoeFun F (fun _ ↦ ∀ a : α, β a) where
  coe := @DFunLike.coe _ _ β _

end Mathlib.Data.FunLike.Basic

section Mathlib.Data.FunLike.Equiv

class EquivLike (E : Sort _) (α β : outParam (Sort _)) where
  coe : E → α → β
  inv : E → β → α


namespace EquivLike

variable {E α β : Sort _} [iE : EquivLike E α β]

instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E → α → β)

end EquivLike

end Mathlib.Data.FunLike.Equiv

section Mathlib.Logic.Equiv.Defs

open Function

universe u v

variable {α : Sort u} {β : Sort v}

structure Equiv (α : Sort _) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α

infixl:25 " ≃ " => Equiv

namespace Equiv

protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

end Equiv

end Mathlib.Logic.Equiv.Defs

section Mathlib.Data.Subtype

variable {α : Sort _} {p q : α → Prop}

theorem Subtype.coe_injective : Function.Injective (fun (a : Subtype p) ↦ (a : α)) := sorry

end Mathlib.Data.Subtype

section Mathlib.Order.Notation

class HasCompl (α : Type _) where
  compl : α → α

export HasCompl (compl)

postfix:1024 "ᶜ" => compl

class Sup (α : Type _) where
  sup : α → α → α

class Inf (α : Type _) where
  inf : α → α → α

infixl:68 " ⊔ " => Sup.sup

infixl:69 " ⊓ " => Inf.inf

class HImp (α : Type _) where
  himp : α → α → α

class HNot (α : Type _) where
  hnot : α → α

export HImp (himp)
export HNot (hnot)

infixr:60 " ⇨ " => himp

prefix:72 "￢" => hnot


class Top (α : Type _) where
  top : α

class Bot (α : Type _) where
  bot : α

notation "⊤" => Top.top

notation "⊥" => Bot.bot


end Mathlib.Order.Notation

section Mathlib.Data.Set.Defs

universe u v w

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

instance : HasCompl (Set α) := ⟨fun s ↦ setOf fun x => x ∉ s⟩

@[reducible] def Elem (s : Set α) : Type u := {x // x ∈ s}

instance : CoeSort (Set α) (Type u) := ⟨Elem⟩

/-- `f '' s` denotes the image of `s : Set α` under the function `f : α → β`. -/
infixl:80 " '' " => image


variable {ι : Sort _} {f : ι → α}

def range (f : ι → α) : Set α := setOf fun x => ∃ y, f y = x

end Set

end Mathlib.Data.Set.Defs

section Mathlib.Order.SetNotation

open Set

universe u v
variable {α : Type u} {ι : Sort v}

class SupSet (α : Type _) where
  sSup : Set α → α

class InfSet (α : Type _) where
  sInf : Set α → α

def iSup [SupSet α] (s : ι → α) : α :=
  SupSet.sSup (range s)

def iInf [InfSet α] (s : ι → α) : α :=
  InfSet.sInf (range s)


namespace Set

instance : InfSet (Set α) :=
  ⟨fun s => setOf fun a => ∀ t ∈ s, a ∈ t⟩

instance : SupSet (Set α) :=
  ⟨fun s => setOf fun a => ∃ t ∈ s, a ∈ t⟩

def iUnion (s : ι → Set α) : Set α :=
  iSup s

def iInter (s : ι → Set α) : Set α :=
  iInf s

end Set

end Mathlib.Order.SetNotation

section Mathlib.Order.Basic

open Function

universe u v w

variable {ι : Type _} {α : Type u} {β : Type v} {γ : Type w} {π : ι → Type _} {r : α → α → Prop}

instance Prop.hasCompl : HasCompl Prop :=
  ⟨Not⟩

instance Pi.hasCompl {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] : HasCompl (∀ i, α i) :=
  ⟨fun x i ↦ (x i)ᶜ⟩

instance Pi.hasLe {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] :
    LE (∀ i, α i) where le x y := ∀ i, x i ≤ y i

instance Pi.preorder {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] : Preorder (∀ i, α i) where
  __ := inferInstanceAs (LE (∀ i, α i))
  le_refl := sorry
  le_trans := sorry

instance Pi.partialOrder [∀ i, PartialOrder (π i)] : PartialOrder (∀ i, π i) where
  __ := Pi.preorder
  le_antisymm := sorry

instance Pi.sdiff {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] : SDiff (∀ i, α i) :=
  ⟨fun x y i ↦ x i \ y i⟩

def Preorder.lift {α β} [Preorder β] (f : α → β) : Preorder α where
  le x y := f x ≤ f y
  le_refl _ := sorry
  le_trans _ _ _ := sorry
  lt x y := f x < f y
  lt_iff_le_not_le _ _ := sorry

def PartialOrder.lift {α β} [PartialOrder β] (f : α → β) (inj : Injective f) : PartialOrder α :=
  { Preorder.lift f with
    le_antisymm := sorry }

section «Prop»

instance Prop.le : LE Prop :=
  ⟨(· → ·)⟩

instance Prop.partialOrder : PartialOrder Prop where
  __ := Prop.le
  le_refl _ := id
  le_trans _ _ _ f g := g ∘ f
  le_antisymm _ _ Hab Hba := sorry

end «Prop»

end Mathlib.Order.Basic


section Mathlib.Order.Lattice

universe u v w

variable {α : Type u} {β : Type v}

class SemilatticeSup (α : Type u) extends Sup α, PartialOrder α where

  protected le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  protected le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

class SemilatticeInf (α : Type u) extends Inf α, PartialOrder α where
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

class DistribLattice (α) extends Lattice α where
  protected le_sup_inf : ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

def DistribLattice.ofInfSupLe [Lattice α] (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) :
    DistribLattice α where
  le_sup_inf := sorry

namespace Pi

variable {ι : Type _} {α' : ι → Type _}

instance [∀ i, Sup (α' i)] : Sup (∀ i, α' i) :=
  ⟨fun f g i => f i ⊔ g i⟩

instance [∀ i, Inf (α' i)] : Inf (∀ i, α' i) :=
  ⟨fun f g i => f i ⊓ g i⟩

instance instSemilatticeSup [∀ i, SemilatticeSup (α' i)] : SemilatticeSup (∀ i, α' i) where
  le_sup_left _ _ _ := sorry
  le_sup_right _ _ _ := sorry
  sup_le _ _ _ ac bc i := sorry

instance instSemilatticeInf [∀ i, SemilatticeInf (α' i)] : SemilatticeInf (∀ i, α' i) where
  inf_le_left _ _ _ := sorry
  inf_le_right _ _ _ := sorry
  le_inf _ _ _ ac bc i := sorry

instance instLattice [∀ i, Lattice (α' i)] : Lattice (∀ i, α' i) where
  __ := inferInstanceAs (SemilatticeSup (∀ i, α' i))
  __ := inferInstanceAs (SemilatticeInf (∀ i, α' i))

instance instDistribLattice [∀ i, DistribLattice (α' i)] : DistribLattice (∀ i, α' i) where
  le_sup_inf _ _ _ _ := sorry

end Pi


end Mathlib.Order.Lattice

section Mathlib.Order.BoundedOrder

universe u v

variable {α : Type u} {β : Type v} {γ δ : Type _}

class OrderTop (α : Type u) [LE α] extends Top α where
  le_top : ∀ a : α, a ≤ ⊤

section OrderTop

section LE

variable [LE α] [OrderTop α] {a : α}

theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a

end LE

end OrderTop

class OrderBot (α : Type u) [LE α] extends Bot α where
  bot_le : ∀ a : α, ⊥ ≤ a

section OrderBot

section LE

variable [LE α] [OrderBot α] {a : α}

theorem bot_le : ⊥ ≤ a :=
  OrderBot.bot_le a

end LE

end OrderBot

class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α

namespace Pi

variable {ι : Type _} {α' : ι → Type _}

instance instOrderTop [∀ i, LE (α' i)] [∀ i, OrderTop (α' i)] : OrderTop (∀ i, α' i) where
  top := fun _ => ⊤
  le_top _ := fun _ => le_top

instance instOrderBot [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) where
  bot := fun _ => ⊥
  bot_le _ := fun _ => bot_le

end Pi


end Mathlib.Order.BoundedOrder

section Mathlib.Order.PropInstances

instance Prop.instDistribLattice : DistribLattice Prop where
  sup := Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun _ _ _ => Or.rec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun _ _ _ Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun _ _ _ => or_and_left.2

instance Prop.instBoundedOrder : BoundedOrder Prop where
  top := True
  le_top _ _ := True.intro
  bot := False
  bot_le := @False.elim

end Mathlib.Order.PropInstances

section Mathlib.Order.Heyting.Basic

universe u

variable {ι α β : Type _}

namespace Pi

variable {π : ι → Type _}

instance [∀ i, HImp (π i)] : HImp (∀ i, π i) :=
  ⟨fun a b i => a i ⇨ b i⟩

end Pi

class GeneralizedHeytingAlgebra (α : Type _) extends Lattice α, OrderTop α, HImp α where
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c

class GeneralizedCoheytingAlgebra (α : Type _) extends Lattice α, OrderBot α, SDiff α where
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c

class HeytingAlgebra (α : Type _) extends GeneralizedHeytingAlgebra α, OrderBot α, HasCompl α where
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ

class CoheytingAlgebra (α : Type _) extends GeneralizedCoheytingAlgebra α, OrderTop α, HNot α where
  top_sdiff (a : α) : ⊤ \ a = ￢a

class BiheytingAlgebra (α : Type _) extends HeytingAlgebra α, SDiff α, HNot α where
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c
  top_sdiff (a : α) : ⊤ \ a = ￢a

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] {a b c d : α}

instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => sorry

instance Pi.instGeneralizedHeytingAlgebra {α : ι → Type _} [∀ i, GeneralizedHeytingAlgebra (α i)] :
    GeneralizedHeytingAlgebra (∀ i, α i) :=
  { Pi.instLattice, Pi.instOrderTop with
    le_himp_iff := sorry }

end GeneralizedHeytingAlgebra


section HeytingAlgebra

variable [HeytingAlgebra α] {a b c : α}

instance Pi.instHeytingAlgebra {α : ι → Type _} [∀ i, HeytingAlgebra (α i)] :
    HeytingAlgebra (∀ i, α i) :=
  { Pi.instOrderBot, Pi.instGeneralizedHeytingAlgebra with
    himp_bot := sorry }

end HeytingAlgebra

instance Prop.instHeytingAlgebra : HeytingAlgebra Prop :=
  { Prop.instDistribLattice, Prop.instBoundedOrder with
    himp := (· → ·),
    le_himp_iff := sorry
    himp_bot := sorry }

end Mathlib.Order.Heyting.Basic

section Mathlib.Order.BooleanAlgebra

universe u v

variable {α : Type u} {β : Type _} {w x y z : α}

class GeneralizedBooleanAlgebra (α : Type u) extends DistribLattice α, SDiff α, Bot α where
  sup_inf_sdiff : ∀ a b : α, a ⊓ b ⊔ a \ b = a
  inf_inf_sdiff : ∀ a b : α, a ⊓ b ⊓ a \ b = ⊥

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

instance (priority := 100) GeneralizedBooleanAlgebra.toOrderBot : OrderBot α where
  __ := GeneralizedBooleanAlgebra.toBot
  bot_le a := sorry

instance (priority := 100) GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra :
    GeneralizedCoheytingAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  sdiff := (· \ ·)
  sdiff_le_iff y x z := sorry

end GeneralizedBooleanAlgebra

class BooleanAlgebra (α : Type u) extends
    DistribLattice α, HasCompl α, SDiff α, HImp α, Top α, Bot α where
  inf_compl_le_bot : ∀ x : α, x ⊓ xᶜ ≤ ⊥
  top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ xᶜ
  le_top : ∀ a : α, a ≤ ⊤
  bot_le : ∀ a : α, ⊥ ≤ a
  sdiff := fun x y => x ⊓ yᶜ
  himp := fun x y => y ⊔ xᶜ
  sdiff_eq : ∀ x y : α, x \ y = x ⊓ yᶜ
  himp_eq : ∀ x y : α, x ⇨ y = y ⊔ xᶜ

section BooleanAlgebra

variable [BooleanAlgebra α]

instance (priority := 100) BooleanAlgebra.toGeneralizedBooleanAlgebra :
    GeneralizedBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  sup_inf_sdiff a b := sorry
  inf_inf_sdiff a b := sorry

instance (priority := 100) BooleanAlgebra.toBiheytingAlgebra : BiheytingAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra
  hnot := compl
  le_himp_iff a b c := sorry
  himp_bot _ := sorry
  top_sdiff a := sorry

end BooleanAlgebra

instance Prop.instBooleanAlgebra : BooleanAlgebra Prop where
  __ := Prop.instHeytingAlgebra
  __ := GeneralizedHeytingAlgebra.toDistribLattice
  compl := Not
  sdiff_eq := sorry
  himp_eq p q := sorry
  inf_compl_le_bot p H := sorry
  top_le_sup_compl p _ := sorry

instance Pi.instBooleanAlgebra {ι : Type u} {α : ι → Type v} [∀ i, BooleanAlgebra (α i)] :
    BooleanAlgebra (∀ i, α i) where
  __ := Pi.sdiff
  __ := Pi.instHeytingAlgebra
  __ := @Pi.instDistribLattice ι α _
  sdiff_eq _ _ := sorry
  himp_eq _ _ := sorry
  inf_compl_le_bot _ _ := sorry
  top_le_sup_compl _ _ := sorry

end Mathlib.Order.BooleanAlgebra

section Mathlib.Data.Set.Basic

universe u
namespace Set

variable {α : Type u} {s t : Set α}

instance instBooleanAlgebraSet : BooleanAlgebra (Set α) :=
  { (inferInstance : BooleanAlgebra (α → Prop)) with
    sup := (· ∪ ·),
    le := (· ≤ ·),
    lt := fun s t => s ⊆ t ∧ ¬t ⊆ s,
    inf := (· ∩ ·),
    bot := ∅,
    compl := (·ᶜ),
    top := univ,
    sdiff := (· \ ·) }

end Set

namespace Set

variable {α : Type _} {s t u : Set α}

def inclusion (h : s ⊆ t) : s → t := fun x : s => (⟨x, h x.2⟩ : t)

end Set

end Mathlib.Data.Set.Basic

section Mathlib.Data.SetLike.Basic

class SetLike (A : Type _) (B : outParam <| Type _) where
  protected coe : A → Set B

namespace SetLike

variable {A : Type _} {B : Type _} [i : SetLike A B]

instance : CoeTC A (Set B) where coe := SetLike.coe

instance (priority := 100) instMembership : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩

instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

instance (priority := 100) instPartialOrder : PartialOrder A :=
  { PartialOrder.lift (SetLike.coe : A → Set B) sorry with
    le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K }

theorem coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T :=
  Iff.rfl

end SetLike


end Mathlib.Data.SetLike.Basic
section Mathlib.Algebra.Group.Defs

universe u v w

open Function

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

class SMul (M : Type u) (α : Type v) where
  smul : M → α → α

infixr:73 " • " => HSMul.hSMul

macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)

instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

variable {G : Type _}

class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

class Semigroup (G : Type u) extends Mul G where
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

class AddSemigroup (G : Type u) extends Add G where
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

class AddCommMagma (G : Type u) extends Add G where
  protected add_comm : ∀ a b : G, a + b = b + a

class CommMagma (G : Type u) extends Mul G where
  protected mul_comm : ∀ a b : G, a * b = b * a

class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where


class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

class MulOneClass (M : Type u) extends One M, Mul M where
  protected one_mul : ∀ a : M, 1 * a = a
  protected mul_one : ∀ a : M, a * 1 = a

class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a

section

variable {M : Type u}

/-- The fundamental power operation in a monoid. `npowRec n a = a*a*...*a` n times.
Use instead `a ^ n`, which has better definitional behavior. -/
def npowRec [One M] [Mul M] : Nat → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a

/-- The fundamental scalar multiplication in an additive monoid. `nsmulRec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : Nat → M → M
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a

end

class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  protected nsmul : Nat → M → M
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  protected nsmul_succ : ∀ (n : Nat) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZeroClass.toAdd

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  protected npow : Nat → M → M := npowRec
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  protected npow_succ : ∀ (n : Nat) (x), npow (n + 1) x = npow n x * x := by intros; rfl

@[default_instance high] instance Monoid.toNatPow {M : Type _} [Monoid M] : Pow M Nat :=
  ⟨fun x n ↦ Monoid.npow n x⟩

instance AddMonoid.toNatSMul {M : Type _} [AddMonoid M] : SMul Nat M :=
  ⟨AddMonoid.nsmul⟩

class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : Int → M → M
  | Int.ofNat n, a => npowRec n a
  | Int.negSucc n, a => (npowRec n.succ a)⁻¹

def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : Int → M → M
  | Int.ofNat n, a => nsmulRec n a
  | Int.negSucc n, a => -nsmulRec n.succ a

def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  protected zpow : Int → G → G := zpowRec
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  protected zpow_succ' (n : Nat) (a : G) : zpow (Int.ofNat n.succ) a = zpow (Int.ofNat n) a  * a := by
    intros; rfl
  protected zpow_neg' (n : Nat) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl

def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  protected zsmul : Int → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : Nat) (a : G) :
      zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a := by
    intros; rfl
  protected zsmul_neg' (n : Nat) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl

instance DivInvMonoid.Pow {M} [DivInvMonoid M] : Pow M Int :=
  ⟨fun x n ↦ DivInvMonoid.zpow n x⟩

instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul Int M :=
  ⟨SubNegMonoid.zsmul⟩

class Group (G : Type u) extends DivInvMonoid G where
  protected mul_left_inv : ∀ a : G, a⁻¹ * a = 1

class AddGroup (A : Type u) extends SubNegMonoid A where
  protected add_left_neg : ∀ a : A, -a + a = 0

class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

class CommGroup (G : Type u) extends Group G, CommMonoid G

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.GroupWithZero.Defs

universe u

variable {G₀ : Type u} {M₀ M₀' G₀' : Type _}

class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0

class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀ where
  inv_zero : (0 : G₀)⁻¹ = 0
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Algebra.Group.Hom.Defs

variable {ι α β M N A B P : Type _}
variable {G : Type _} {H : Type _}
variable {F : Type _}

section Zero

structure ZeroHom (M : Type _) (N : Type _) [Zero M] [Zero N] where
  protected toFun : M → N
  protected map_zero' : toFun 0 = 0

class ZeroHomClass (F : Type _) (M N : outParam (Type _)) [Zero M] [Zero N] [FunLike F M N] : Prop
    where
  map_zero : ∀ f : F, f 0 = 0

end Zero

section Add

structure AddHom (M : Type _) (N : Type _) [Add M] [Add N] where
  protected toFun : M → N
  protected map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

class AddHomClass (F : Type _) (M N : outParam (Type _)) [Add M] [Add N] [FunLike F M N] : Prop where
  map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y

end Add


structure AddMonoidHom (M : Type _) (N : Type _) [AddZeroClass M] [AddZeroClass N] extends
  ZeroHom M N, AddHom M N

infixr:25 " →+ " => AddMonoidHom

class AddMonoidHomClass (F M N : Type _) [AddZeroClass M] [AddZeroClass N] [FunLike F M N] : Prop
  extends AddHomClass F M N, ZeroHomClass F M N

section One

variable [One M] [One N]

structure OneHom (M : Type _) (N : Type _) [One M] [One N] where
  protected toFun : M → N
  protected map_one' : toFun 1 = 1

class OneHomClass (F : Type _) (M N : outParam (Type _)) [One M] [One N] [FunLike F M N] : Prop where
  map_one : ∀ f : F, f 1 = 1

instance OneHom.funLike : FunLike (OneHom M N) M N where
  coe := OneHom.toFun

variable [FunLike F M N]

def OneHomClass.toOneHom [OneHomClass F M N] (f : F) : OneHom M N where
  toFun := f
  map_one' := sorry

instance [OneHomClass F M N] : CoeTC F (OneHom M N) :=
  ⟨OneHomClass.toOneHom⟩

end One

section Zero

variable [Zero M] [Zero N]

instance ZeroHom.funLike : FunLike (ZeroHom M N) M N where
  coe := ZeroHom.toFun

variable [FunLike F M N]

def ZeroHomClass.toZeroHom [ZeroHomClass F M N] (f : F) : ZeroHom M N where
  toFun := f
  map_zero' := sorry

instance [ZeroHomClass F M N] : CoeTC F (ZeroHom M N) :=
  ⟨ZeroHomClass.toZeroHom⟩

end Zero

section Mul

variable [Mul M] [Mul N]

structure MulHom (M : Type _) (N : Type _) [Mul M] [Mul N] where
  protected toFun : M → N
  protected map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

infixr:25 " →ₙ* " => MulHom

class MulHomClass (F : Type _) (M N : outParam (Type _)) [Mul M] [Mul N] [FunLike F M N] : Prop where
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y

instance MulHom.funLike : FunLike (M →ₙ* N) M N where
  coe := MulHom.toFun

variable [FunLike F M N]

def MulHomClass.toMulHom [MulHomClass F M N] (f : F) : M →ₙ* N where
  toFun := f
  map_mul' := sorry

instance [MulHomClass F M N] : CoeTC F (M →ₙ* N) :=
  ⟨MulHomClass.toMulHom⟩

end Mul

section Add

variable [Add M] [Add N]

instance AddHom.funLike : FunLike (AddHom M N) M N where
  coe := AddHom.toFun

variable [FunLike F M N]

def AddHomClass.toAddHom [AddHomClass F M N] (f : F) : AddHom M N where
  toFun := f
  map_add' := sorry

instance [AddHomClass F M N] : CoeTC F (AddHom M N) :=
  ⟨AddHomClass.toAddHom⟩

end Add

variable [MulOneClass M] [MulOneClass N] [AddZeroClass A] [AddZeroClass B]

structure MonoidHom (M : Type _) (N : Type _) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N

infixr:25 " →* " => MonoidHom

class MonoidHomClass (F : Type _) (M N : outParam (Type _)) [MulOneClass M] [MulOneClass N]
  [FunLike F M N] : Prop
  extends MulHomClass F M N, OneHomClass F M N

instance MonoidHom.instFunLike : FunLike (M →* N) M N where
  coe f := f.toFun

instance AddMonoidHom.instFunLike : FunLike (A →+ B) A B where
  coe f := f.toFun

def MonoidHomClass.toMonoidHom [FunLike F M N] [MonoidHomClass F M N] (f : F) : M →* N :=
  { (f : M →ₙ* N), (f : OneHom M N) with }

def AddMonoidHomClass.toAddMonoidHom [FunLike F A B] [AddMonoidHomClass F A B] (f : F) : A →+ B :=
  { (f : AddHom A B), (f : ZeroHom A B) with }

instance [FunLike F M N] [MonoidHomClass F M N] : CoeTC F (M →* N) :=
  ⟨MonoidHomClass.toMonoidHom⟩

instance [FunLike F A B] [AddMonoidHomClass F A B] : CoeTC F (A →+ B) :=
  ⟨AddMonoidHomClass.toAddMonoidHom⟩

variable {M N P : Type _}

def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P where
  toFun := hnp ∘ hmn
  map_mul' x y := sorry

def MonoidHom.comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (hnp : N →* P) (hmn : M →* N) :
    M →* P where
  toFun := hnp ∘ hmn
  map_one' := sorry
  map_mul' := sorry

def AddHom.comp [Add M] [Add N] [Add P] (hnp : AddHom N P) (hmn : AddHom M N) : AddHom M P where
  toFun := hnp ∘ hmn
  map_add' x y := sorry

def AddMonoidHom.comp [AddZeroClass M] [AddZeroClass N] [AddZeroClass P] (hnp : N →+ P) (hmn : M →+ N) :
    M →+ P where
  toFun := hnp ∘ hmn
  map_zero' := sorry
  map_add' := sorry

end Mathlib.Algebra.Group.Hom.Defs

section Mathlib.Algebra.Group.Equiv.Basic

structure AddEquiv (A B : Type _) [Add A] [Add B] extends A ≃ B, AddHom A B
structure MulEquiv (M N : Type _) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N

infixl:25 " ≃* " => MulEquiv
infixl:25 " ≃+ " => AddEquiv

def AddEquiv.symm {M N : Type _} [Add M] [Add N] (h : M ≃+ N) : N ≃+ M :=
  ⟨h.toEquiv.symm, sorry⟩

def MulEquiv.symm {M N : Type _} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  ⟨h.toEquiv.symm, sorry⟩

end Mathlib.Algebra.Group.Equiv.Basic

section Mathlib.Algebra.GroupWithZero.Hom

variable {F α β γ δ : Type _} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

class MonoidWithZeroHomClass (F : Type _) (α β : outParam (Type _)) [MulZeroOneClass α]
  [MulZeroOneClass β] [FunLike F α β] : Prop extends MonoidHomClass F α β, ZeroHomClass F α β

structure MonoidWithZeroHom (α β : Type _) [MulZeroOneClass α] [MulZeroOneClass β]
  extends ZeroHom α β, MonoidHom α β

/-- `α →*₀ β` denotes the type of zero-preserving monoid homomorphisms from `α` to `β`. -/
infixr:25 " →*₀ " => MonoidWithZeroHom

end Mathlib.Algebra.GroupWithZero.Hom

section Mathlib.Data.Int.Cast.Defs

protected def Nat.unaryCast {R : Type _} [One R] [Zero R] [Add R] : Nat → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

class AddMonoidWithOne (R : Type _) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  natCast_zero : natCast 0 = 0 := by intros; rfl
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R

protected def Int.castDef {R : Type _} [NatCast R] [Neg R] : Int → R
  | (n : Nat) => n
  | Int.negSucc n => -(n + 1 : Nat)

class AddGroupWithOne (R : Type _) extends IntCast R, AddMonoidWithOne R, AddGroup R where
  intCast := Int.castDef
  intCast_ofNat : ∀ n : Nat, intCast (n : Nat) = Nat.cast n := by intros; rfl
  intCast_negSucc : ∀ n : Nat, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros; rfl

class AddCommGroupWithOne (R : Type _)
  extends AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R

end Mathlib.Data.Int.Cast.Defs

section Mathlib.Algebra.Ring.Defs

universe u x

variable {α : Type u} {R : Type x}

class Distrib (R : Type _) extends Mul R, Add R where

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

class NonAssocRing (α : Type _) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

end Mathlib.Algebra.Ring.Defs

section Mathlib.Algebra.Ring.Hom.Defs

open Function

variable {F α β γ : Type _}

structure NonUnitalRingHom (α β : Type _) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β

infixr:25 " →ₙ+* " => NonUnitalRingHom

namespace NonUnitalRingHom

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [NonUnitalNonAssocSemiring γ]

def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

end NonUnitalRingHom

structure RingHom (α : Type _) (β : Type _) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β

infixr:25 " →+* " => RingHom

section RingHomClass

class RingHomClass (F : Type _) (α β : outParam (Type _))
    [NonAssocSemiring α] [NonAssocSemiring β] [FunLike F α β] : Prop
  extends MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β

variable [FunLike F α β]

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} [RingHomClass F α β]

def RingHomClass.toRingHom (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

instance : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩

end RingHomClass

namespace RingHom

section coe

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

instance instFunLike : FunLike (α →+* β) α β where
  coe f := f.toFun

instance instRingHomClass : RingHomClass (α →+* β) α β where
  map_add := sorry
  map_zero := sorry
  map_mul f := sorry
  map_one f := sorry

end coe

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} {_ : NonAssocSemiring γ}

def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with
    toFun := g ∘ f
    map_one' := sorry }

end RingHom


end Mathlib.Algebra.Ring.Hom.Defs


section Mathlib.Algebra.Group.InjSurj
namespace Function

namespace Injective

variable {M₁ : Type _} {M₂ : Type _} [Mul M₁]

protected def semigroup [Semigroup M₂] (f : M₁ → M₂) (hf : Injective f) : Semigroup M₁ :=
  { ‹Mul M₁› with mul_assoc := sorry }

protected def addSemigroup {M₁} [Add M₁] [AddSemigroup M₂] (f : M₁ → M₂) (hf : Injective f) : AddSemigroup M₁ :=
  { ‹Add M₁› with add_assoc := sorry }

protected def commMagma [CommMagma M₂] (f : M₁ → M₂) (hf : Injective f) : CommMagma M₁ where
  mul_comm x y := sorry

protected def addCommMagma {M₁} [Add M₁] [AddCommMagma M₂] (f : M₁ → M₂) (hf : Injective f) : AddCommMagma M₁ where
  add_comm x y := sorry

protected def commSemigroup [CommSemigroup M₂] (f : M₁ → M₂) (hf : Injective f) : CommSemigroup M₁ where
  toSemigroup := hf.semigroup f
  __ := hf.commMagma f

protected def addCommSemigroup {M₁} [Add M₁] [AddCommSemigroup M₂] (f : M₁ → M₂) (hf : Injective f) : AddCommSemigroup M₁ where
  toAddSemigroup := hf.addSemigroup f
  __ := hf.addCommMagma f

variable [One M₁]

protected def mulOneClass [MulOneClass M₂] (f : M₁ → M₂) (hf : Injective f) : MulOneClass M₁ :=
  { ‹One M₁›, ‹Mul M₁› with
    one_mul := sorry,
    mul_one := sorry }

protected def addZeroClass {M₁} [Zero M₁] [Add M₁] [AddZeroClass M₂] (f : M₁ → M₂) (hf : Injective f) : AddZeroClass M₁ :=
  { ‹Zero M₁›, ‹Add M₁› with
    zero_add := sorry,
    add_zero := sorry }

variable [Pow M₁ Nat]

protected def monoid [Monoid M₂] (f : M₁ → M₂) (hf : Injective f) : Monoid M₁ :=
  { hf.mulOneClass f, hf.semigroup f with
    npow := fun n x => x ^ n,
    npow_zero := sorry,
    npow_succ := sorry }

protected def addMonoid {M₁} [Zero M₁] [Add M₁] [SMul Nat M₁] [AddMonoid M₂] (f : M₁ → M₂) (hf : Injective f) : AddMonoid M₁ :=
  { hf.addZeroClass f, hf.addSemigroup f with
    nsmul := fun n x => n • x,
    nsmul_zero := sorry,
    nsmul_succ := sorry }

protected def addMonoidWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul Nat M₁] [NatCast M₁]
    [AddMonoidWithOne M₂] (f : M₁ → M₂) (hf : Injective f) : AddMonoidWithOne M₁ :=
  { hf.addMonoid f with
    natCast := Nat.cast,
    natCast_zero := sorry,
    natCast_succ := sorry,
    one := 1 }

protected def commMonoid [CommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) :
    CommMonoid M₁ :=
  { hf.monoid f, hf.commSemigroup f with }

protected def addCommMonoid {M₁} [Zero M₁] [Add M₁] [SMul Nat M₁] [AddCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) :
    AddCommMonoid M₁ :=
  { hf.addMonoid f, hf.addCommSemigroup f with }

variable [Inv M₁] [Div M₁] [Pow M₁ Int]

protected def divInvMonoid [DivInvMonoid M₂] (f : M₁ → M₂) (hf : Injective f) : DivInvMonoid M₁ :=
  { hf.monoid f, ‹Inv M₁›, ‹Div M₁› with
    zpow := fun n x => x ^ n,
    zpow_zero' := sorry,
    zpow_succ' := sorry,
    zpow_neg' := sorry,
    div_eq_mul_inv := sorry }

protected def subNegMonoid {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul Nat M₁] [Neg M₁] [Sub M₁]
    [SMul Int M₁] [SubNegMonoid M₂] (f : M₁ → M₂) (hf : Injective f) : SubNegMonoid M₁ :=
  { hf.addMonoid f, ‹Neg M₁›, ‹Sub M₁› with
    zsmul := fun n x => n • x,
    zsmul_zero' := sorry,
    zsmul_succ' := sorry,
    zsmul_neg' := sorry,
    sub_eq_add_neg := sorry }

protected def group [Group M₂] (f : M₁ → M₂) (hf : Injective f) : Group M₁ :=
  { hf.divInvMonoid f with
    mul_left_inv := sorry }

protected def addGroup {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul Nat M₁] [Neg M₁] [Sub M₁]
    [SMul Int M₁] [AddGroup M₂] (f : M₁ → M₂) (hf : Injective f) : AddGroup M₁ :=
  { hf.subNegMonoid f with
    add_left_neg := sorry }

protected def addGroupWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul Nat M₁] [Neg M₁] [Sub M₁]
    [SMul Int M₁] [NatCast M₁] [IntCast M₁] [AddGroupWithOne M₂] (f : M₁ → M₂) (hf : Injective f) : AddGroupWithOne M₁ :=
  { hf.addGroup f,
    hf.addMonoidWithOne f with
    intCast := Int.cast,
    intCast_ofNat := sorry,
    intCast_negSucc := sorry }

protected def commGroup [CommGroup M₂] (f : M₁ → M₂) (hf : Injective f) : CommGroup M₁ :=
  { hf.commMonoid f, hf.group f with }

protected def addCommGroup {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul Nat M₁] [Neg M₁] [Sub M₁]
    [SMul Int M₁] [AddCommGroup M₂] (f : M₁ → M₂) (hf : Injective f) : AddCommGroup M₁ :=
  { hf.addCommMonoid f, hf.addGroup f with }

end Injective

end Function


end Mathlib.Algebra.Group.InjSurj

section Mathlib.Algebra.GroupWithZero.InjSurj

variable {M₀ G₀ M₀' G₀' : Type _}

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

protected def Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀) (hf : Injective f) : MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  zero_mul a := sorry
  mul_zero a := sorry

end MulZeroClass

section MulZeroOneClass

variable [MulZeroOneClass M₀]

protected def Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀)
    (hf : Injective f) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f, hf.mulOneClass f with }

end MulZeroOneClass

section SemigroupWithZero

protected def Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f, ‹Zero M₀'›, hf.semigroup f with }

end SemigroupWithZero

section MonoidWithZero

protected def Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' Nat]
    [MonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) :
    MonoidWithZero M₀' :=
  { hf.monoid f, hf.mulZeroClass f with }

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

protected def Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' Nat] [Pow G₀' Int] (f : G₀' → G₀) (hf : Injective f) : GroupWithZero G₀' :=
  { hf.monoidWithZero f,
    hf.divInvMonoid f with
    inv_zero := sorry,
    mul_inv_cancel := sorry }

end GroupWithZero



end Mathlib.Algebra.GroupWithZero.InjSurj

section Mathlib.Algebra.Ring.InjSurj

universe u v x

variable {α : Type u} {β : Type v} {R : Type x}

protected def Function.Injective.distrib {S} [Mul R] [Add R] [Distrib S] (f : R → S)
    (hf : Injective f) :
    Distrib R where
  mul := (· * ·)
  add := (· + ·)

variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [SMul Nat β] [SMul Int β] [Pow β Nat]
  [NatCast β] [IntCast β]

protected def Function.Injective.nonUnitalNonAssocSemiring {α : Type u}
    [NonUnitalNonAssocSemiring α] (f : β → α) (hf : Injective f) : NonUnitalNonAssocSemiring β where
  toAddCommMonoid := hf.addCommMonoid f
  __ := hf.distrib f
  __ := hf.mulZeroClass f

protected def Function.Injective.nonUnitalSemiring {α : Type u} [NonUnitalSemiring α] (f : β → α)
    (hf : Injective f) :
    NonUnitalSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f
  __ := hf.semigroupWithZero f

protected def Function.Injective.nonAssocSemiring {α : Type u} [NonAssocSemiring α] [NatCast β] (f : β → α) (hf : Injective f) : NonAssocSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f
  __ := hf.mulZeroOneClass f
  __ := hf.addMonoidWithOne f

protected def Function.Injective.semiring {α : Type u} [Semiring α] [NatCast β] (f : β → α) (hf : Injective f) : Semiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f
  __ := hf.nonAssocSemiring f
  __ := hf.monoidWithZero f

protected def Function.Injective.ring [Ring α] (f : β → α) (hf : Injective f) : Ring β where
  toSemiring := hf.semiring f
  __ := hf.addGroupWithOne f
  __ := hf.addCommGroup f

end Mathlib.Algebra.Ring.InjSurj

section Mathlib.GroupTheory.GroupAction.Defs

variable {M α : Type _}

instance (priority := 910) Mul.toSMul (α : Type _) [Mul α] : SMul α α :=
  ⟨(· * ·)⟩

class MulAction (α : Type _) (β : Type _) [Monoid α] extends SMul α β where

class IsScalarTower (M N α : Type _) [SMul M N] [SMul N α] [SMul M α] : Prop

instance IsScalarTower.left [Monoid M] [MulAction M α] : IsScalarTower M M α := sorry

namespace SMul

variable {N} [SMul M α]

def comp.smul (g : N → M) (n : N) (a : α) : α :=
  g n • a

variable (α)

def comp (g : N → M) : SMul N α where smul := SMul.comp.smul g

end SMul

end Mathlib.GroupTheory.GroupAction.Defs

section Mathlib.GroupTheory.Subsemigroup.Basic

variable {M : Type _} {A : Type _}

variable [Mul M]
variable [Add A]

structure Subsemigroup (M : Type _) [Mul M] where
  carrier : Set M

structure AddSubsemigroup (M : Type _) [Add M] where
  carrier : Set M

end Mathlib.GroupTheory.Subsemigroup.Basic

section Mathlib.GroupTheory.Submonoid.Basic

variable {M : Type _} {A : Type _}

variable [MulOneClass M] {s : Set M}
variable [AddZeroClass A] {t : Set A}

structure Submonoid (M : Type _) [MulOneClass M] extends Subsemigroup M

class SubmonoidClass (S : Type _) (M : Type _) [MulOneClass M] [SetLike S M] : Prop

structure AddSubmonoid (M : Type _) [AddZeroClass M] extends AddSubsemigroup M

class AddSubmonoidClass (S : Type _) (M : Type _) [AddZeroClass M] [SetLike S M] : Prop

namespace Submonoid

instance : SetLike (Submonoid M) M where
  coe s := s.carrier

instance : SubmonoidClass (Submonoid M) M where

protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M where
  carrier := s

variable {S : Submonoid M}

instance : Top (Submonoid M) :=
  ⟨{ carrier := Set.univ }⟩

instance : InfSet (Submonoid M) :=
  ⟨fun s =>
    { carrier := Set.iInter fun t => Set.iInter fun _ : t ∈ s => ↑t }⟩

end Submonoid

namespace AddSubmonoid

instance : SetLike (AddSubmonoid A) A where
  coe s := s.carrier

instance : AddSubmonoidClass (AddSubmonoid A) A where

protected def copy (S : AddSubmonoid A) (s : Set A) (hs : s = S) : AddSubmonoid A where
  carrier := s

variable {S : AddSubmonoid A}

instance : Top (AddSubmonoid A) :=
  ⟨{ carrier := Set.univ }⟩

instance : InfSet (AddSubmonoid A) :=
  ⟨fun s =>
    { carrier := Set.iInter fun t => Set.iInter fun _ : t ∈ s => ↑t }⟩

end AddSubmonoid

end Mathlib.GroupTheory.Submonoid.Basic

section Mathlib.GroupTheory.Subsemigroup.Operations

variable {M : Type _}

namespace MulMemClass

variable {A : Type _} [Mul M] [SetLike A M] (S' : A)

instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, sorry⟩⟩

end MulMemClass

namespace AddMemClass

variable {A : Type _} [Add M] [SetLike A M] (S' : A)

instance (priority := 900) add : Add S' :=
  ⟨fun a b => ⟨a.1 + b.1, sorry⟩⟩

end AddMemClass

end Mathlib.GroupTheory.Subsemigroup.Operations

section Mathlib.GroupTheory.Submonoid.Operations

variable {M N : Type _} [MulOneClass M] [MulOneClass N] (S : Submonoid M)
variable {A B : Type _} [AddZeroClass A] [AddZeroClass B] (T : AddSubmonoid A)
namespace Submonoid

variable {F : Type _} [FunLike F M N]

def map (f : F) (S : Submonoid M) : Submonoid N where
  carrier := f '' S

end Submonoid

namespace AddSubmonoid

variable {F : Type _} [FunLike F A B]

def map (f : F) (S : AddSubmonoid A) : AddSubmonoid B where
  carrier := f '' S

end AddSubmonoid
namespace OneMemClass

variable {A M₁ : Type _} [SetLike A M₁] [One M₁] (S' : A)

instance one : One S' :=
  ⟨⟨1, sorry⟩⟩

end OneMemClass

namespace ZeroMemClass

variable {A M₁ : Type _} [SetLike A M₁] [Zero M₁] (S' : A)

instance zero : Zero S' :=
  ⟨⟨0, sorry⟩⟩

end ZeroMemClass

namespace SubmonoidClass

instance nPow {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S Nat :=
  ⟨fun a n => ⟨a.1 ^ n, sorry⟩⟩

instance (priority := 75) toMulOneClass {M : Type _} [MulOneClass M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S :=
    Subtype.coe_injective.mulOneClass (fun x : S => (x : M))

instance (priority := 75) toMonoid {M : Type _} [Monoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : Monoid S :=
  Subtype.coe_injective.monoid (fun x : S => (x : M))

end SubmonoidClass

namespace AddSubmonoidClass

instance nSMul {M} [AddMonoid M] {A : Type _} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : SMul Nat S :=
  ⟨fun n a => ⟨n • a.1, sorry⟩⟩

instance (priority := 75) toAddZeroClass {M : Type _} [AddZeroClass M] {A : Type _} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : AddZeroClass S :=
    Subtype.coe_injective.addZeroClass (fun x : S => (x : M))

instance (priority := 75) toAddMonoid {M : Type _} [AddMonoid M] {A : Type _} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : AddMonoid S :=
  Subtype.coe_injective.addMonoid (fun x : S => (x : M))

end AddSubmonoidClass

namespace Submonoid

instance toMonoid {M : Type _} [Monoid M] (S : Submonoid M) : Monoid S :=
  Subtype.coe_injective.monoid (fun x : S => (x : M))

def subtype : S →* M where
  toFun := Subtype.val
  map_one' := sorry
  map_mul' _ _ := sorry

instance smul {M' α : Type _} [MulOneClass M'] [SMul M' α] (S : Submonoid M') : SMul S α :=
  SMul.comp _ S.subtype

end Submonoid

namespace AddSubmonoid

def subtype : T →+ A where
  toFun := Subtype.val
  map_zero' := sorry
  map_add' _ _ := sorry

end AddSubmonoid

namespace MonoidHom

def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S) (h : ∀ x, f x ∈ s) :
    M →* s where
  toFun n := ⟨f n, h n⟩
  map_one' := sorry
  map_mul' x y := sorry

end MonoidHom

namespace AddMonoidHom

def codRestrict {T} [SetLike T B] [AddSubmonoidClass T B] (f : A →+ B) (t : T) (h : ∀ x, f x ∈ t) :
    A →+ t where
  toFun n := ⟨f n, h n⟩
  map_zero' := sorry
  map_add' x y := sorry

end AddMonoidHom

end Mathlib.GroupTheory.Submonoid.Operations

section Mathlib.GroupTheory.Subgroup.Basic

variable {G : Type _} [Group G]
variable {A : Type _} [AddGroup A]


instance inv {G : Type _} {S : Type _} [Inv G] [SetLike S G]
  {H : S} : Inv H :=
  ⟨fun a => ⟨a⁻¹, sorry⟩⟩

instance neg {A : Type _} {S : Type _} [Neg A] [SetLike S A]
  {H : S} : Neg H :=
  ⟨fun a => ⟨- a, sorry⟩⟩

instance div {G : Type _} {S : Type _} [DivInvMonoid G] [SetLike S G]
  {H : S} : Div H :=
  ⟨fun a b => ⟨a / b, sorry⟩⟩

instance sub {A : Type _} {S : Type _} [SubNegMonoid A] [SetLike S A]
  {H : S} : Sub H :=
  ⟨fun a b => ⟨a - b, sorry⟩⟩

instance _root_.AddSubmonoidClass.zsmul {M S} [SubNegMonoid M] [SetLike S M]
    {H : S} : SMul Int H :=
  ⟨fun n a => ⟨n • a.1, sorry⟩⟩

instance zpow {M S} [DivInvMonoid M] [SetLike S M] {H : S} : Pow H Int :=
  ⟨fun a n => ⟨a.1 ^ n, sorry⟩⟩

structure Subgroup (G : Type _) [Group G] extends Submonoid G where

structure AddSubgroup (G : Type _) [AddGroup G] extends AddSubmonoid G where

namespace Subgroup

instance : SetLike (Subgroup G) G where
  coe s := s.carrier

variable (H K : Subgroup G)

protected def copy (K : Subgroup G) (s : Set G) (hs : s = K) : Subgroup G where
  carrier := s

instance : Top (Subgroup G) :=
  ⟨{ (⊤ : Submonoid G) with }⟩

instance : InfSet (Subgroup G) :=
  ⟨fun s =>
    { (iInf fun S => iInf fun h : S ∈ s => Subgroup.toSubmonoid S).copy (Set.iInter fun S => Set.iInter fun _ : S ∈ s => ↑S) sorry with }⟩

instance : InfSet (Subgroup G) :=
  ⟨fun s =>
    { (iInf fun S => iInf fun h : S ∈ s => Subgroup.toSubmonoid S).copy (Set.iInter fun S => Set.iInter fun _ : S ∈ s => ↑S) sorry with }⟩

def map {N : Type _} [Group N] (f : G →* N) (H : Subgroup G) : Subgroup N :=
  { H.toSubmonoid.map f with
    carrier := f '' H }

end Subgroup

namespace AddSubgroup

instance : SetLike (AddSubgroup A) A where
  coe s := s.carrier

variable (H K : AddSubgroup A)

protected def copy (K : AddSubgroup A) (s : Set A) (hs : s = K) : AddSubgroup A where
  carrier := s

instance : Top (AddSubgroup A) :=
  ⟨{ (⊤ : AddSubmonoid A) with }⟩

instance : InfSet (AddSubgroup A) :=
  ⟨fun s =>
    { (iInf fun S => iInf fun h : S ∈ s => AddSubgroup.toAddSubmonoid S).copy (Set.iInter fun S => Set.iInter fun _ : S ∈ s => ↑S) sorry with }⟩

instance : InfSet (AddSubgroup A) :=
  ⟨fun s =>
    { (iInf fun S => iInf fun h : S ∈ s => AddSubgroup.toAddSubmonoid S).copy (Set.iInter fun S => Set.iInter fun _ : S ∈ s => ↑S) sorry with }⟩

def map {N : Type _} [AddGroup N] (f : A →+ N) (H : AddSubgroup A) : AddSubgroup N :=
  { H.toAddSubmonoid.map f with
    carrier := f '' H }

end AddSubgroup

end Mathlib.GroupTheory.Subgroup.Basic

section Mathlib.Algebra.Field.Defs

variable {K : Type _}

class DivisionRing (α : Type _) extends Ring α, DivInvMonoid α where
  protected mul_inv_cancel : ∀ (a : α), a ≠ 0 → a * a⁻¹ = 1
  protected inv_zero : (0 : α)⁻¹ = 0

class Semifield (K : Type _) extends Semiring K, GroupWithZero K

class Field (K : Type _) extends Ring K, DivisionRing K

instance (priority := 100) Field.toSemifield [Field K] : Semifield K := { ‹Field K› with }

end Mathlib.Algebra.Field.Defs

section Mathlib.Algebra.Ring.Equiv

variable {R S : Type _}

structure RingEquiv (R S : Type _) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S

infixl:25 " ≃+* " => RingEquiv

namespace RingEquiv

variable [Mul R] [Mul S] [Add R] [Add S]

@[symm]
protected def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }

end RingEquiv

end Mathlib.Algebra.Ring.Equiv

section Mathlib.Algebra.Field.Basic

@[reducible]
protected def Function.Injective.field {K : Type _} [Field K] {K'} [Zero K'] [Mul K'] [Add K'] [Neg K'] [Sub K']
    [One K'] [Inv K'] [Div K'] [SMul Nat K'] [SMul Int K'] [Pow K' Nat] [Pow K' Int]
    [NatCast K'] [IntCast K'] (f : K' → K) (hf : Injective f) :
    Field K' :=
  { hf.groupWithZero f,
    hf.ring f with }

protected theorem RingHom.injective {α β : Type _} [DivisionRing α] [Semiring β] (f : α →+* β) :
    Function.Injective f := sorry

end Mathlib.Algebra.Field.Basic

section Mathlib.RingTheory.Subsemiring.Basic

universe u v w

section AddSubmonoidWithOneClass

class AddSubmonoidWithOneClass (S R : Type _) [AddMonoidWithOne R]
  [SetLike S R] : Prop extends AddSubmonoidClass S R

variable {S R : Type _} [AddMonoidWithOne R] [SetLike S R] (s : S)

instance (priority := 74) AddSubmonoidWithOneClass.toAddMonoidWithOne
    [AddSubmonoidWithOneClass S R] : AddMonoidWithOne s :=
  { AddSubmonoidClass.toAddMonoid s with
    one := ⟨1, sorry⟩
    natCast := fun n => ⟨n, sorry⟩
    natCast_zero := sorry
    natCast_succ := sorry }

end AddSubmonoidWithOneClass

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

section SubsemiringClass

class SubsemiringClass (S : Type _) (R : Type u) [NonAssocSemiring R]
  [SetLike S R] : Prop extends SubmonoidClass S R, AddSubmonoidClass S R

instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type _)
    (R : Type u) [NonAssocSemiring R] [SetLike S R] [h : SubsemiringClass S R] :
    AddSubmonoidWithOneClass S R :=
  { h with }

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s :=
  Subtype.coe_injective.nonAssocSemiring (fun x : s => (x : R))

instance toSemiring {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] :
    Semiring s :=
  Subtype.coe_injective.semiring (fun x : s => (x : R))

end SubsemiringClass

end SubsemiringClass

structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R

namespace Subsemiring

instance : SetLike (Subsemiring R) R where
  coe s := s.carrier

instance : SubsemiringClass (Subsemiring R) R where

protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

instance toNonAssocSemiring : NonAssocSemiring s :=
  SubsemiringClass.toNonAssocSemiring _

instance toSemiring {R} [Semiring R] (s : Subsemiring R) : Semiring s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

def subtype : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with
    toFun := fun x : s => (x : R) }

instance : Top (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

def map [NonAssocSemiring S] (f : R →+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubmonoid.map (f : R →+ S) with carrier := f '' s }

end Subsemiring

def RingHom.rangeS [NonAssocSemiring S] (f : R →+* S) : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.range f) sorry

def RingHom.codRestrict {σS} [NonAssocSemiring S] [SetLike σS S] [SubsemiringClass σS S] (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) : R →+* s :=
  { (f : R →* S).codRestrict s h, (f : R →+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }

end Mathlib.RingTheory.Subsemiring.Basic

section Mathlib.RingTheory.Subring.Basic

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [Ring R]

section SubringClass

class SubringClass (S : Type _) (R : Type u) [Ring R] [SetLike S R] : Prop
  extends SubsemiringClass S R

instance (priority := 100) SubringClass.addSubmonoidClass (S : Type _) (R : Type u)
    [SetLike S R] [Ring R] [h : SubringClass S R] : AddSubmonoidClass S R :=
  { h with }

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

instance (priority := 75) toHasIntCast : IntCast s :=
  ⟨fun n => ⟨n, sorry⟩⟩

end SubringClass

variable [Ring S] [Ring T]

structure Subring (R : Type u) [Ring R] extends Subsemiring R, AddSubgroup R

namespace Subring

instance : SetLike (Subring R) R where
  coe s := s.carrier

protected def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with
    carrier := s }

protected def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) : Subring R :=
  { sm.copy s sorry, sa.copy s sorry with }

end Subring

namespace Subring

instance : Top (Subring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

def map {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (s : Subring R) : Subring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }

end Subring

instance : InfSet (Subring R) :=
  ⟨fun s =>
    Subring.mk' (Set.iInter fun t => Set.iInter fun _ : t ∈ s => ↑t) (iInf fun t => iInf fun _ : t ∈ s => t.toSubmonoid) (iInf fun t => iInf fun _ : t ∈ s => Subring.toAddSubgroup t)⟩

end Mathlib.RingTheory.Subring.Basic

section Mathlib.Algebra.Algebra.Basic

universe u v w

class Algebra (R : Type u) (A : Type v) [Semiring R] [Semiring A] extends SMul R A, R →+* A

def algebraMap (R : Type u) (A : Type v) [Semiring R] [Semiring A] [Algebra R A] : R →+* A :=
  Algebra.toRingHom

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type _}

section Semiring

variable [Semiring R] [Semiring S]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

instance (priority := 200) toMulAction : MulAction R A where

instance _root_.IsScalarTower.right : IsScalarTower R A A := sorry

instance id : Algebra R R where
  toFun x := x
  toSMul := Mul.toSMul _
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

instance (S : Subsemiring R) : SMul S A := Submonoid.smul ..

instance ofSubsemiring (S : Subsemiring R) : Algebra S A where
  toRingHom := (algebraMap R A).comp S.subtype
  smul := (· • ·)

end Semiring

end Algebra

end Mathlib.Algebra.Algebra.Basic

section Mathlib.Algebra.Algebra.Hom

universe u v w u₁ v₁

structure AlgHom (R : Type u) (A : Type v) (B : Type w) [Semiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

infixr:25 " →ₐ " => AlgHom _

notation:25 A " →ₐ[" R "] " B => AlgHom R A B

/-- `AlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class AlgHomClass (F : Type _) (R A B : outParam (Type _))
  [Semiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [FunLike F A B] : Prop extends RingHomClass F A B where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁}

section Semiring

variable [Semiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

variable [Semiring C] [Algebra R C] in
instance funLike : FunLike (A →ₐ[R] B) A B where
  coe f := f.toFun

instance algHomClass : AlgHomClass (A →ₐ[R] B) R A B where
  map_add f := sorry
  map_zero f := sorry
  map_mul f := sorry
  map_one f := sorry
  commutes f := sorry

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ := sorry

variable [Semiring C] [Algebra R C] in
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp φ₂ with
    commutes' := sorry }

end Semiring

end AlgHom

end Mathlib.Algebra.Algebra.Hom

-- import Mathlib.Order.SetNotation
-- import Mathlib.Data.Set.Image
-- import Mathlib.Data.SetLike.Basic
-- import Mathlib.Algebra.Ring.Hom.Basic
-- import Mathlib.Algebra.Ring.InjSurj
-- import Mathlib.GroupTheory.GroupAction.Defs
-- import Mathlib.GroupTheory.Subsemigroup.Basic
-- import Mathlib.GroupTheory.Submonoid.Basic
-- import Mathlib.GroupTheory.Subsemigroup.Operations
-- import Mathlib.GroupTheory.Submonoid.Operations
-- import Mathlib.GroupTheory.Subgroup.Basic
-- import Mathlib.Algebra.Field.Defs
-- import Mathlib.Algebra.Ring.Equiv
-- import Mathlib.Algebra.Field.Basic
-- import Mathlib.RingTheory.Subsemiring.Basic
-- import Mathlib.Algebra.Algebra.Basic
-- import Mathlib.Algebra.Algebra.Hom

section Mathlib.Algebra.Algebra.Equiv

universe u v w u₁ v₁

structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [Semiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃+* B where
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

namespace AlgEquiv

universe uR uA₁ uA₂ uA₃
variable {R : Type uR}
variable {A₁ : Type uA₁} {A₂ : Type uA₂}

section Semiring

variable [Semiring R] [Semiring A₁] [Semiring A₂]
variable [Algebra R A₁] [Algebra R A₂]
variable (e : A₁ ≃ₐ[R] A₂)

instance : EquivLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun

instance : FunLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe := DFunLike.coe

def toAlgHom : A₁ →ₐ[R] A₂ :=
  { e with
    map_one' := sorry
    map_zero' := sorry }

def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := sorry }

theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x := sorry

end Semiring

end AlgEquiv


end Mathlib.Algebra.Algebra.Equiv



section Mathlib.Algebra.Algebra.Subalgebra.Basic

universe u u' v w

/-- A subalgebra is a sub(semi)ring that includes the range of `algebraMap`. -/
structure Subalgebra (R : Type u) (A : Type v) [Semiring R] [Semiring A] [Algebra R A] : Type v
  extends Subsemiring A  where

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w}
variable [Semiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

instance : SetLike (Subalgebra R A) A where
  coe s := s.carrier

variable (S : Subalgebra R A)

instance {R A : Type _} [Semiring R] [Semiring A] [Algebra R A] : SubsemiringClass (Subalgebra R A) A where

instance (priority := 500) algebra' [Semiring R'] [SMul R' R] [Algebra R' A]
    [IsScalarTower R' R A] :
    Algebra R' S :=
  { (algebraMap R' A).codRestrict S sorry with
    smul := fun r s => ⟨r • s, sorry⟩ }

instance algebra : Algebra R S := S.algebra'

def val : S →ₐ[R] A :=
  { toFun := fun x : S => (x : A)
    map_zero' := sorry
    map_one' := sorry
    map_add' := sorry
    map_mul' := sorry
    commutes' := sorry }

end Subalgebra

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [Semiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (φ : A →ₐ[R] B)

/-- Range of an `AlgHom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with }

def codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codRestrict (f : A →+* B) S hf with commutes' := sorry }

@[reducible]
def rangeRestrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
  f.codRestrict f.range sorry

end AlgHom

namespace AlgEquiv

variable {R : Type u}
variable [Semiring R]
variable {A : Type v} {B : Type w} [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B]

def ofLeftInverse {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val }

noncomputable def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)

noncomputable def ofInjectiveField {E F : Type _} [DivisionRing E] [Semiring F]
    [Algebra R E] [Algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range := ofInjective f f.toRingHom.injective

end AlgEquiv

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v}
variable [Semiring R] [Semiring A] [Algebra R A]

def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := sorry
  map_add' _ _ := sorry
  map_mul' _ _ := sorry
  map_zero' := sorry
  commutes' _ := sorry

instance Subalgebra.instSMul [Semiring S] [Algebra R S] [SMul S T] (S' : Subalgebra R S) : SMul S' T := S'.smul

instance isScalarTower_mid {R S T : Type _} [Semiring R] [Semiring S] [AddMonoid T]
    [Algebra R S] [MulAction R T] [MulAction S T] [IsScalarTower R S T] (S' : Subalgebra R S) :
    IsScalarTower R S' T := sorry

end Subalgebra

end Mathlib.Algebra.Algebra.Subalgebra.Basic

section Mathlib.Algebra.Algebra.Tower

universe u v w

variable (R : Type u) (S : Type v) (A : Type w)

namespace IsScalarTower

variable [Semiring R] [Semiring S] [Semiring A]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [IsScalarTower R S A]

def toAlgHom : S →ₐ[R] A :=
  { algebraMap S A with commutes' := sorry }

end IsScalarTower

end Mathlib.Algebra.Algebra.Tower


section Mathlib.Algebra.Algebra.Subalgebra.Tower

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace Subalgebra

open IsScalarTower

variable {S A B} [Semiring R] [Semiring S] [Semiring A]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [IsScalarTower R S A]

def restrictScalars (U : Subalgebra S A) : Subalgebra R A :=
  { U with }

end Subalgebra

end Mathlib.Algebra.Algebra.Subalgebra.Tower

section Mathlib.Data.Polynomial.Basic

def Polynomial (R : Type _) [Semiring R] : Type _ := sorry

end Mathlib.Data.Polynomial.Basic


section Mathlib.Data.Polynomial.Splits

universe u v w

variable {K : Type v} {L : Type w}
variable [Semiring K] [Semiring L]
variable (i : K →+* L)

def Polynomial.Splits (f : Polynomial K) : Prop := sorry

end Mathlib.Data.Polynomial.Splits

section Mathlib.FieldTheory.Subfield

universe u v w

variable {K : Type u} {L : Type v}
variable [DivisionRing K] [DivisionRing L]

/-- `SubfieldClass S K` states `S` is a type of subsets `s ⊆ K` closed under field operations. -/
class SubfieldClass (S K : Type _) [DivisionRing K] [SetLike S K] : Prop extends SubringClass S K

namespace SubfieldClass

variable (S : Type _) [SetLike S K] [h : SubfieldClass S K]

instance (priority := 75) toField {K} [Field K] [SetLike S K] [SubfieldClass S K] (s : S) :
    Field s :=
  Subtype.coe_injective.field fun x : s => (x : K)

end SubfieldClass

structure Subfield (K : Type u) [Ring K] extends Subring K where

namespace Subfield

instance : SetLike (Subfield K) K where
  coe s := s.carrier

instance : SubfieldClass (Subfield K) K where

protected def copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : Subfield K :=
  { S.toSubring.copy s hs with
    carrier := s }

/-- The subfield of `K` containing all elements of `K`. -/
instance : Top (Subfield K) :=
  ⟨{ (⊤ : Subring K) with }⟩

def map (f : K →+* L) (s : Subfield K) : Subfield L :=
  { s.toSubring.map f with}

end Subfield

def RingHom.fieldRange (f : K →+* L) : Subfield L :=
  ((⊤ : Subfield K).map f).copy (Set.range f) sorry

namespace Subfield

instance : InfSet (Subfield K) :=
  ⟨fun S => { InfSet.sInf (Subfield.toSubring '' S) with }⟩

def closure (s : Set K) : Subfield K := InfSet.sInf (setOf fun S => s ⊆ S)

end Subfield

end Mathlib.FieldTheory.Subfield



section Mathlib.FieldTheory.IntermediateField

variable (K L L' : Type _) [Field K] [Field L] [Field L'] [Algebra K L]

structure IntermediateField extends Subalgebra K L where
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier

variable {K L L'}
variable (S : IntermediateField K L)

namespace IntermediateField

instance : SetLike (IntermediateField K L) L :=
  ⟨fun S => S.toSubalgebra.carrier⟩

def toSubfield : Subfield L :=
  { S.toSubalgebra with }

instance : SubfieldClass (IntermediateField K L) L where

instance toAlgebra : Algebra S L :=
  inferInstanceAs (Algebra S.toSubsemiring L)

instance algebra' {R' K L : Type _} [Field K] [Field L] [Algebra K L] (S : IntermediateField K L)
    [Semiring R'] [SMul R' K] [Algebra R' L] [IsScalarTower R' K L] : Algebra R' S :=
  inferInstanceAs (Algebra R' S.toSubalgebra)

instance {E} [Field E] [Algebra L E] : Algebra S E := Algebra.ofSubsemiring S.toSubsemiring

instance isScalarTower {R} [Semiring R] [SMul R K] [SMul R L] [SMul R S] [IsScalarTower R K L] :
    IsScalarTower R K S := sorry

end IntermediateField

namespace AlgHom

variable [Algebra K L'] (f : L →ₐ[K] L')

def fieldRange : IntermediateField K L' :=
  { f.range, (f : L →+* L').fieldRange with
    inv_mem' := sorry }

end AlgHom

namespace IntermediateField

def inclusion {E F : IntermediateField K L} (hEF : E ≤ F) : E →ₐ[K] F :=
  Subalgebra.inclusion hEF

section RestrictScalars

variable (K)
variable [Algebra L' L]

variable [Algebra K L'] [IsScalarTower K L' L] in
def restrictScalars (E : IntermediateField L' L) : IntermediateField K L :=
  { E.toSubfield, E.toSubalgebra.restrictScalars K with
    carrier := E.carrier
    inv_mem' := sorry }

@[simp]
theorem coe_restrictScalars {E : IntermediateField L' L} :
    (restrictScalars K E : Set L) = (E : Set L) :=
  rfl

end RestrictScalars

end IntermediateField

end Mathlib.FieldTheory.IntermediateField

section Mathlib.FieldTheory.Adjoin

namespace IntermediateField

section AdjoinDef

variable (F : Type _) {E : Type _} [Field E] (S : Set E)

variable [Field F] [Algebra F E] in
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.range (algebraMap F E) ∪ S) with
    inv_mem' := sorry }

variable [Field F] [Algebra F E] in
theorem subset_adjoin : S ⊆ adjoin F S := sorry

instance (F : Subfield E) : Algebra F E := inferInstanceAs (Algebra F.toSubsemiring E)

theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T ⊆ F) : T ⊆ adjoin F S :=
  sorry

variable [Field F] [Algebra F E] in
theorem adjoin_subset_adjoin_iff {F' : Type _} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) ⊆ adjoin F' S' ↔
      Set.range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' := sorry

end AdjoinDef

end IntermediateField

end Mathlib.FieldTheory.Adjoin

section Mathlib.FieldTheory.Extension

namespace IntermediateField

variable {F E K : Type _} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

instance (L : IntermediateField F E) : IsScalarTower F L E := sorry

instance (L : IntermediateField F E) : Algebra F (adjoin L S) :=
  (IntermediateField.adjoin { x // x ∈ L } S).algebra'

private theorem exists_algHom_adjoin_of_splits'' {L : IntermediateField F E}
    (f : L →ₐ[F] K) :
    ∃ φ : adjoin L S →ₐ[F] K, φ.comp (IsScalarTower.toAlgHom F L _) = f := by
  sorry

variable {L : Type _} [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]
  (f : L →ₐ[F] K)

-- This only required 16,000 heartbeats prior to #3807, and now takes ~210,000.
set_option maxHeartbeats 16000
theorem exists_algHom_adjoin_of_splits''' :
    ∃ φ : adjoin L S →ₐ[F] K, φ.comp (IsScalarTower.toAlgHom F L _) = f := by
  let L' := (IsScalarTower.toAlgHom F L E).fieldRange
  let f' : L' →ₐ[F] K := f.comp (AlgEquiv.ofInjectiveField _).symm.toAlgHom
  have := exists_algHom_adjoin_of_splits'' f' (S := S)
  · obtain ⟨φ, hφ⟩ := this
    refine ⟨φ.comp <|
      inclusion (?_ : (adjoin L S).restrictScalars F ≤ (adjoin L' S).restrictScalars F), ?_⟩
    · simp only [← SetLike.coe_subset_coe, coe_restrictScalars, adjoin_subset_adjoin_iff]
      exact ⟨subset_adjoin_of_subset_left S (F := L'.toSubfield) le_rfl, subset_adjoin _ _⟩
    · ext x
      exact
        Eq.trans
          (congrFun (congrArg (fun g : L' →ₐ[F] K => (g : L' → K)) hφ)
            (DFunLike.coe (AlgEquiv.ofInjectiveField _) x))
          (congrArg f
            (AlgEquiv.symm_apply_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) x))

end IntermediateField

end Mathlib.FieldTheory.Extension
