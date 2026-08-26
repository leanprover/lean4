import Lean
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.Types

open Lean Meta
open Compiler.LCNF (toLCNFType toMonoType)

def toMonoLCNFType (type : Expr) : MetaM Expr := do
  toMonoType (← toLCNFType type)

def checkMonoType! (type₁ type₂ : Expr) : MetaM Unit := do
  let monoType ← toMonoLCNFType type₁
  if monoType != type₂ then
    throwError f!"mono type for {type₁} is {monoType}, expected {type₂}"
  let monoMonoType ← toMonoType monoType
  if monoMonoType != monoType then
    throwError f!"toMonoType is not idempotent: toMonoType of {monoType} is {monoMonoType}"

-- Nat

#eval checkMonoType!
  (.const ``Nat [])
  (.const ``Nat [])

-- Decidable

#eval checkMonoType!
  (.app (.const ``Decidable []) (.const ``True []))
  (.const ``Bool [])

-- Prop

#eval checkMonoType!
  (.sort .zero)
  (.const ``lcErased [])

-- Type

#eval checkMonoType!
  (.sort (.succ .zero))
  (.const ``lcErased [])

-- Sort u

#eval checkMonoType!
  (.sort (.param `u))
  (.const ``lcErased [])

-- List Nat

#eval checkMonoType!
  (.app (.const ``List [.succ .zero]) (.const ``Nat []))
  (.app (.const ``List []) (.const ``Nat []))

-- List Type

#eval checkMonoType!
  (.app (.const ``List [.succ (.succ .zero)]) (.sort (.succ .zero)))
  (.app (.const ``List []) (.const ``lcErased []))

-- Inductive type with trivial structure

inductive TrivialInductive : Type where
  | constructor (a : Nat) : TrivialInductive

#eval checkMonoType!
  (.const ``TrivialInductive [])
  (.const ``Nat [])

-- Inductive type with trivial structure and irrelevant fields

inductive TrivialInductivePropFields : Type where
  | constructor (p₁ : Prop) (a : Nat) (p₂ : Prop) : TrivialInductivePropFields

#eval checkMonoType!
  (.const ``TrivialInductivePropFields [])
  (.const ``Nat [])

-- Structure type with trivial structure

structure TrivialStructure : Type where
  a : Nat

#eval checkMonoType!
  (.const ``TrivialStructure [])
  (.const ``Nat [])

-- Structure type with trivial structure and irrelevant fields

structure TrivialStructurePropFields : Type where
  p₁ : Prop
  a : Nat
  p₂ : Prop

#eval checkMonoType!
  (.const ``TrivialStructurePropFields [])
  (.const ``Nat [])

-- Nat → Nat

#eval checkMonoType!
  (.forallE `a (.const ``Nat []) (.const ``Nat []) .default)
  (.forallE `a (.const ``Nat []) (.const ``Nat []) .default)

-- Nat → List Nat

#eval checkMonoType!
  (.forallE `a (.const ``Nat []) (.app (.const ``List [.succ .zero]) (.const ``Nat [])) .default)
  (.forallE `a (.const ``Nat []) (.app (.const ``List []) (.const ``Nat [])) .default)

-- Nat → Prop

#eval checkMonoType!
  (.forallE `a (.const ``Nat []) (.sort .zero) .default)
  (.const ``lcErased [])

-- Nat → Type

#eval checkMonoType!
  (.forallE `a (.const ``Nat []) (.sort (.succ .zero)) .default)
  (.const ``lcErased [])

-- Nat → Bool → Type

#eval checkMonoType!
  (.forallE `a
            (.const ``Nat [])
            (.forallE `a (.const ``Bool []) (.sort (.succ .zero)) .default)
            .default)
  (.const ``lcErased [])

-- (α : Type) → List α

#eval checkMonoType!
  (.forallE `α (.sort (.succ .zero)) (.app (.const ``List [.succ .zero]) (.bvar 0)) .default)
  (.forallE `α (.const ``lcErased []) (.app (.const ``List []) (.const ``lcAny [])) .default)

-- List Nat → List Bool

#eval checkMonoType!
  (.forallE `a
           (.app (.const ``List [.succ .zero]) (.const ``Nat []))
           (.app (.const ``List [.succ .zero]) (.const ``Bool []))
           .default)
  (.forallE `a
           (.app (.const ``List []) (.const ``Nat []))
           (.app (.const ``List []) (.const ``Bool []))
           .default)

-- List Nat → List Prop

#eval checkMonoType!
  (.forallE `a
           (.app (.const ``List [.succ .zero]) (.const ``Nat []))
           (.app (.const ``List [.succ .zero]) (.sort .zero))
           .default)
  (.forallE `a
           (.app (.const ``List []) (.const ``Nat []))
           (.app (.const ``List []) (.const ``lcErased []))
           .default)

-- (α : Type) → α → α

#eval checkMonoType!
  (.forallE `α
            (.sort (.succ .zero))
            (.forallE `a (.bvar 0) (.bvar 1) .default)
            .default)
  (.forallE `α
            (.const ``lcErased [])
            (.forallE `a (.const ``lcAny []) (.const ``lcAny []) .default)
            .default)

-- Nat → (α : Type) → α → Bool

#eval checkMonoType!
  (.forallE `a
            (.const ``Nat [])
            (.forallE `α
                      (.sort (.succ .zero))
                      (.forallE `a (.bvar 0) (.const ``Bool []) .default)
                      .default)
            .default)
  (.forallE `a
            (.const ``Nat [])
            (.forallE `α
                      (.const ``lcErased [])
                      (.forallE `a (.const ``lcAny []) (.const ``Bool []) .default)
                      .default)
            .default)

-- Nat → Bool → Type

#eval checkMonoType!
  (.forallE `a
            (.const ``Nat [])
            (.forallE `b (.const ``Bool []) (.sort (.succ .zero)) .default)
            .default)
  (.const ``lcErased [])

-- Nat → Bool → (Nat → Type)

#eval checkMonoType!
  (.forallE `a
            (.const ``Nat [])
            (.forallE `b (.const ``Bool []) (.sort (.succ .zero)) .default)
            .default)
  (.const ``lcErased [])

-- Nat → (Nat → Type) → Bool

#eval checkMonoType!
  (.forallE `a
            (.const ``Nat [])
            (.forallE `b
                      (.forallE `c (.const ``lcErased []) (.sort (.succ .zero)) .default)
                      (.const ``Bool [])
                      .default)
            .default)
  (.forallE `a
            (.const ``Nat [])
            (.forallE `b
                      (.const ``lcErased [])
                      (.const ``Bool [])
                      .default)
            .default)

-- (α : Sort u) → (β : α → Sort v) → (a : α) → ((x : α) → β x) → β a

#eval checkMonoType!
  (.forallE
    `α
    (.sort (.param `u))
    (.forallE
      `β
      (.forallE `f1 (.bvar 0) (.sort (.param `v)) .default)
      (.forallE
        `a
        (.bvar 1)
        (.forallE
          `f2
          (.forallE `x (.bvar 2) (.app (.bvar 2) (.bvar 0)) .default)
          (.app (.bvar 2) (.bvar 1))
          .default)
        .default)
      .default)
    .default)
  (.forallE
    `α
    (.const ``lcErased [])
    (.forallE
      `β
      (.const ``lcErased [])
      (.forallE
        `a
        (.const ``lcAny [])
        (.forallE
          `f2
          (.forallE `x (.const ``lcAny []) (.const ``lcAny []) .default)
          (.const ``lcAny [])
          .default)
        .default)
      .default)
    .default)
