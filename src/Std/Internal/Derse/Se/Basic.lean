module

prelude
-- TODO: minize import
public import Init

public section

namespace Std.Internal.Derse


open Lean

-- TODO: universe polymorphism needs to be thought about more

class Serializer (σ : Type u) (m : outParam (Type u → Type v)) (ρ : outParam (Type u))
    (ε : outParam (Type w)) [MonadStateOf σ m] [MonadExceptOf σ m] where
  serializeBool (bool : Bool) : m ρ
  serializeUInt8 (num : UInt8) : m ρ
  serializeUInt16 (num : UInt16) : m ρ
  serializeUInt32 (num : UInt32) : m ρ
  serializeUInt64 (num : UInt64) : m ρ
  serializeInt8 (num : Int8) : m ρ
  serializeInt16 (num : Int16) : m ρ
  serializeInt32 (num : Int32) : m ρ
  serializeInt64 (num : Int64) : m ρ
  serializeNat (num : Nat) : m ρ
  serializeInt (num : Int) : m ρ
  serializeFloat (num : Float) : m ρ
  serializeFloat32 (num : Float32) : m ρ
  serializeChar (char : Char) : m ρ
  serializeName (name : Name) : m ρ
  serializeString (string : String) : m ρ
  serializeBytes (bytes : ByteArray) : m ρ
  serializeNone : m ρ
  -- TODO: α should take a `Serialize` constraint here and similarly below
  -- TODO: fix this with wrapper methods
  serializeSome {α : Type u} (val : α) (ser : α → m ρ) : m ρ
  serializeUnit : m ρ
  serializeUnitStructure (name : Name) : m ρ
  serializeUnitAlt (typeName : Name) (altIdx : UInt64) (altName : Name) : m ρ
  -- TODO: here as well
  serializeSingleFieldStruct {α : Type u} (typeName : Name) (val : α) (ser : α → m ρ) : m ρ
  -- TODO: here as well
  serializeSingleFieldAlt {α : Type u} (typeName : Name) (altIdx : UInt64) (altName : Name)
    (val : α) (ser : α → m ρ) : m ρ
  -- TODO: here as well, might need to be more well thought out in general
  serializeSeq {α β : Type u} {γ : Type u} (iter : Std.Iter (α := β) α)
    (init : γ) (ser : γ → α → m γ) (fin : γ → m ρ) : m ρ
  -- TODO: here as well, might need to be more well thought out in general
  serializeTuple {α β : Type u} {γ : Type u} (length : Nat) (iter : Std.Iter (α := β) α)
    (init : γ) (ser : γ → α → m γ) (fin : γ → m ρ) : m ρ
  -- TODO: here as well, might need to be more well thought out in general
  serializeMap {α₁ α₂ β : Type u} {γ : Type u} (iter : Std.Iter (α := β) (α₁ × α₂))
    (init : γ) (ser : γ → α₁ → α₂ → m γ) (fin : γ → m ρ) : m ρ
  -- TODO: here as well, might need to be more well thought out in general
  serializeAnonAlt {γ : Type u} (typeName : Name) (altIdx : UInt64) (altName : Name) (len : UInt64)
    (init : γ) (ser : {α : Type u} → (α → m ρ) → m γ) (fin : γ → m ρ) : m ρ
  -- TODO: here as well, might need to be more well thought out in general
  serializeNamedAlt {γ : Type u} (typeName : Name) (altIdx : UInt64) (altName : Name) (len : UInt64)
    (init : γ) (ser : {α : Type u} → (α → m ρ) → (fieldIdx : UInt64) → (fieldName : Name) → m γ) (fin : γ → m ρ) : m ρ
  -- TODO: here as well, might need to be more well thought out in general
  serializeStruct {γ : Type u} (typeName : Name) (len : UInt64) (init : γ)
    (ser : {α : Type u} → (α → m ρ) → (fieldIdx : UInt64) → (fieldName : Name) → m γ) (fin : γ → m ρ) : m ρ

class Serialize (α : Sort o) where
  serialize {σ : Type u} {m : outParam (Type u → Type v)} {ρ : outParam (Type u)}
    {ε : outParam (Type w)} [MonadStateOf σ m] [MonadExceptOf σ m] [Serializer σ m ρ ε]
    (value : α) : m ρ

end Std.Internal.Derse
