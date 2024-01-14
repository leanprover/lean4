-- Minimisation of a timeout triggered by leanprover/lean4#3124
-- in Mathlib.Computability.PartrecCode

set_option autoImplicit true

section Std.Data.Nat.Basic

def sqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (n / 2)
where
  iter (n guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      iter n next
    else
      guess
  termination_by guess

end Std.Data.Nat.Basic

section Mathlib.Logic.Equiv.Defs

structure Equiv (α : Sort _) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α

infixl:25 " ≃ " => Equiv

namespace Equiv

protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

def sigmaEquivProd (α β : Type _) : (Σ _ : α, β) ≃ α × β :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩⟩

end Equiv

end Mathlib.Logic.Equiv.Defs

section Mathlib.Data.Nat.Pairing

namespace Nat

def pair (a b : Nat) : Nat :=
  if a < b then b * b + a else a * a + a + b

def unpair (n : Nat) : Nat × Nat :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

theorem unpair_right_le (n : Nat) : (unpair n).2 ≤ n := sorry

end Nat

end Mathlib.Data.Nat.Pairing

section Mathlib.Logic.Encodable.Basic

open Nat

class Encodable (α : Type _) where
  encode : α → Nat
  decode : Nat → Option α
  encodek : ∀ a, decode (encode a) = some a

namespace Encodable

def ofLeftInjection [Encodable α] (f : β → α) (finv : α → Option β)
    (linv : ∀ b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => sorry⟩

def ofLeftInverse [Encodable α] (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) :
    Encodable β :=
  ofLeftInjection f (some ∘ finv) sorry

def ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β :=
  ofLeftInverse e.toFun e.invFun sorry

instance _root_.Nat.encodable : Encodable Nat :=
  ⟨id, some, fun _ => rfl⟩

instance _root_.Option.encodable {α : Type _} [h : Encodable α] : Encodable (Option α) :=
  ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode m).map some, sorry⟩

section Sigma

variable {γ : α → Type _} [Encodable α] [∀ a, Encodable (γ a)]

def encodeSigma : Sigma γ → Nat
  | ⟨a, b⟩ => pair (encode a) (encode b)

def decodeSigma (n : Nat) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
  (decode n₁).bind fun a => (decode n₂).map <| Sigma.mk a

instance _root_.Sigma.encodable : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, sorry⟩

end Sigma

instance Prod.encodable [Encodable α] [Encodable β] : Encodable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm

end Encodable

end Mathlib.Logic.Encodable.Basic

section Mathlib.Logic.Denumerable

class Denumerable (α : Type _) extends Encodable α where

namespace Denumerable

def mk' {α} (e : α ≃ Nat) : Denumerable α where
  encode := e.toFun
  decode := some ∘ e.invFun
  encodek _ := sorry

instance nat : Denumerable Nat := ⟨⟩

end Denumerable

end Mathlib.Logic.Denumerable

section Mathlib.Logic.Equiv.List

open Nat List

namespace Encodable

variable [Encodable α]

def encodeList : List α → Nat
  | [] => 0
  | a :: l => succ (pair (encode a) (encodeList l))

def decodeList : Nat → Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_le h
      (· :: ·) <$> decode (α := α) v₁ <*> decodeList v₂

instance _root_.List.encodable : Encodable (List α) :=
  ⟨encodeList, decodeList, sorry⟩

end Encodable

end Mathlib.Logic.Equiv.List

section Mathlib.Computability.Primrec

open Denumerable Encodable Function

namespace Nat

@[simp, reducible]
def unpaired {α} (f : Nat → Nat → α) (n : Nat) : α :=
  f n.unpair.1 n.unpair.2

protected inductive Primrec : (Nat → Nat) → Prop
  | zero : Nat.Primrec fun _ => 0
  | protected succ : Nat.Primrec succ
  | left : Nat.Primrec fun n => n.unpair.1
  | right : Nat.Primrec fun n => n.unpair.2
  | pair {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => pair (f n) (g n)
  | comp {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => f (g n)
  | prec {f g} :
      Nat.Primrec f →
        Nat.Primrec g →
          Nat.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

end Nat

class Primcodable (α : Type _) extends Encodable α where
  prim : Nat.Primrec fun n => Encodable.encode (decode n)

namespace Primcodable

instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α := ⟨sorry⟩

instance option {α : Type _} [h : Primcodable α] : Primcodable (Option α) := ⟨sorry⟩

end Primcodable

def Primrec {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.Primrec fun n => encode ((@decode α _ n).map f)

namespace Primrec

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

protected theorem encode : Primrec (@encode α _) := sorry

theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
  sorry

end Primrec

namespace Primcodable

open Nat.Primrec

instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
  ⟨sorry⟩

end Primcodable

namespace Primrec

variable {α : Type _} {σ : Type _} [Primcodable α] [Primcodable σ]

open Nat.Primrec

theorem fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β) := sorry

theorem snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β) := sorry

end Primrec

def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Primrec fun p : α × β => f p.1 p.2

section Comp

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem Primrec₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) := sorry

end Comp

namespace Primrec

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) := sorry

end Primrec

section

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

variable (H : Nat.Primrec fun n => Encodable.encode (@decode (List β) _ n))

open Primrec

private def prim : Primcodable (List β) := ⟨H⟩

end

namespace Primcodable

variable {α : Type _} {β : Type _}

variable [Primcodable α] [Primcodable β]

open Primrec

instance list : Primcodable (List α) := ⟨sorry⟩

end Primcodable

namespace Primrec

variable {α : Type _}

variable [Primcodable α]

theorem list_get? : Primrec₂ (@List.get? α) := sorry

end Primrec

end Mathlib.Computability.Primrec

section Mathlib.Computability.PartrecCode

open Encodable Denumerable Primrec

namespace Nat.Partrec

inductive Code : Type
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind' : Code → Code

end Nat.Partrec

namespace Nat.Partrec.Code

def encodeCode : Code → Nat
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 4
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 4
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 4
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 4

def ofNatCode : Nat → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | _ => zero -- garbage value!

instance instDenumerable : Denumerable Code :=
  mk' ⟨encodeCode, ofNatCode⟩

open Primrec

private def lup (L : List (List (Option Nat))) (p : Nat × Code) (n : Nat) := do
  let l ← L.get? (encode p)
  let o ← l.get? n
  o

-- This used to work in under 20000, but need over 6 million after leanprover/lean4#3124
set_option maxHeartbeats 40000 in
private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_get?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_get?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)
