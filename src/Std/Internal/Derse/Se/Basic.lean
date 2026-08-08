module

prelude
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers
public import Init.Data.ByteArray.Basic
public import Init.Data.SInt.Basic
public import Init.Data.Float
public import Init.Data.Vector.Basic
public import Init.Data.Vector.Monadic

public section

namespace Std.Internal.Derse


open Lean

-- TODO: universe polymorphism needs to be thought about more

class Serializer (σ : outParam (Type u)) (m : Type u → Type v) (ρ : outParam (Type u))
    (ε : outParam (Type w)) [Monad m] [MonadStateOf σ m] [MonadExceptOf ε m] where
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
  serializeSomeWith {α : Type u} (val : α) (ser : α → m ρ) : m ρ
  serializeUnit : m ρ
  serializeUnitStructure (typeName : String) : m ρ
  serializeUnitAlt (typeName : String) (altIdx : UInt64) (altName : String) : m ρ
  serializeNewtypeAltWith {α : Type u} (typeName : String) (altIdx : UInt64) (altName : String)
    (val : α) (ser : α → m ρ) : m ρ

  SeqState : Type u
  serializeSeqBegin (size? : Option Nat) : m SeqState
  serializeSeqElemWith {α : Type u} (state : SeqState) (val : α) (ser : α → m ρ) : m SeqState
  serializeSeqEnd (state : SeqState) : m ρ

  TupleState : Type u
  serializeTupleBegin (size : Nat) : m TupleState
  serializeTupleElemWith {α : Type u} (state : TupleState) (val : α) (ser : α → m ρ) : m TupleState
  serializeTupleEnd (state : TupleState) : m ρ

  MapState : Type u
  serializeMapBegin (size? : Option Nat) : m MapState
  serializeMapKeyWith {α : Type u} (state : MapState) (key : α) (ser : α → m ρ) : m MapState
  serializeMapValWith {α : Type u} (state : MapState) (val : α) (ser : α → m ρ) : m MapState
  serializeMapEnd (state : MapState) : m ρ

  StructState : Type u
  serializeStructBegin (typeName : String) (size : Nat) : m StructState
  serializeStructFieldWith {α : Type u} (state : StructState) (fieldIdx : UInt64)
    (fieldName : String) (val : α) (ser : α → m ρ) : m StructState
  serializeStructEnd (state : StructState) : m ρ

  AnonAltState : Type u
  serializeAnonAltBegin (typeName : String) (altIdx : UInt64) (altName : String) (size : Nat) :
    m AnonAltState
  serializeAnonAltFieldWith {α : Type u} (state : AnonAltState) (fieldIdx : UInt64) (val : α)
    (ser : α → m ρ) : m AnonAltState
  serializeAnonAltEnd (state : AnonAltState) : m ρ

  NamedAltState : Type u
  serializeNamedAltBegin (typeName : String) (altIdx : UInt64) (altName : String) (size : Nat) :
    m NamedAltState
  serializeNamedAltFieldWith {α : Type u} (state : NamedAltState) (fieldIdx : UInt64)
    (fieldName : String) (val : α) (ser : α → m ρ) : m NamedAltState
  serializeNamedAltEnd (state : NamedAltState) : m ρ

class Serialize (α : Sort o) where
  serialize {σ : Type u} {m : Type u → Type v} {ρ : Type u} {ε : Type w} [Monad m]
    [MonadStateOf σ m] [MonadExceptOf ε m] [Serializer σ m ρ ε] (value : α) : m ρ

/--
Lets `partial` serialization functions, such as the ones `deriving Serialize` generates for
recursive types, discharge the inhabitation requirement on their return type `m ρ`.
-/
instance {σ : Type u} {m : Type u → Type v} {ρ : Type u} {ε : Type w} [Monad m]
    [MonadStateOf σ m] [MonadExceptOf ε m] [Serializer σ m ρ ε] : Nonempty (m ρ) :=
  ⟨Serializer.serializeUnit⟩

namespace Serializer

section States

variable (σ : Type u) (m : Type u → Type v) (ρ : Type u) (ε : Type w) [Monad m]
  [MonadStateOf σ m] [MonadExceptOf ε m] [Serializer σ m ρ ε]

abbrev seqState : Type u := SeqState (σ := σ) (m := m) (ρ := ρ) (ε := ε)

abbrev tupleState : Type u := TupleState (σ := σ) (m := m) (ρ := ρ) (ε := ε)

abbrev mapState : Type u := MapState (σ := σ) (m := m) (ρ := ρ) (ε := ε)

abbrev structState : Type u := StructState (σ := σ) (m := m) (ρ := ρ) (ε := ε)

abbrev anonAltState : Type u := AnonAltState (σ := σ) (m := m) (ρ := ρ) (ε := ε)

abbrev namedAltState : Type u := NamedAltState (σ := σ) (m := m) (ρ := ρ) (ε := ε)

end States

variable {σ : Type u} {m : Type u → Type v} {ρ : Type u} {ε : Type w} [Monad m]
  [MonadStateOf σ m] [MonadExceptOf ε m] [Serializer σ m ρ ε] {α : Type u} [Serialize α]

@[inline]
def serializeSome (val : α) : m ρ :=
  serializeSomeWith val Serialize.serialize

@[inline]
def serializeOption (val? : Option α) : m ρ :=
  match val? with
  | none => serializeNone (σ := σ) (m := m) (ρ := ρ) (ε := ε)
  | some val => serializeSome val

@[inline]
def serializeNewtypeAlt (typeName : String) (altIdx : UInt64) (altName : String) (val : α) : m ρ :=
  serializeNewtypeAltWith typeName altIdx altName val Serialize.serialize

@[inline]
def serializeSeqElem (state : seqState σ m ρ ε) (val : α) : m (seqState σ m ρ ε) :=
  serializeSeqElemWith state val Serialize.serialize

@[inline]
def serializeTupleElem (state : tupleState σ m ρ ε) (val : α) : m (tupleState σ m ρ ε) :=
  serializeTupleElemWith state val Serialize.serialize

@[inline]
def serializeMapKey (state : mapState σ m ρ ε) (key : α) : m (mapState σ m ρ ε) :=
  serializeMapKeyWith state key Serialize.serialize

@[inline]
def serializeMapVal (state : mapState σ m ρ ε) (val : α) : m (mapState σ m ρ ε) :=
  serializeMapValWith state val Serialize.serialize

@[inline]
def serializeStructField (state : structState σ m ρ ε) (fieldIdx : UInt64) (fieldName : String) (val : α) :
    m (structState σ m ρ ε) :=
  serializeStructFieldWith state fieldIdx fieldName val Serialize.serialize

@[inline]
def serializeAnonAltField (state : anonAltState σ m ρ ε) (fieldIdx : UInt64) (val : α) : m (anonAltState σ m ρ ε) :=
  serializeAnonAltFieldWith state fieldIdx val Serialize.serialize

@[inline]
def serializeNamedAltField (state : namedAltState σ m ρ ε) (fieldIdx : UInt64) (fieldName : String)
    (val : α) : m (namedAltState σ m ρ ε) :=
  serializeNamedAltFieldWith state fieldIdx fieldName val Serialize.serialize

@[inline]
def serializeSeq {β : Type u} [Std.Iterator β Id α]
    [Std.IteratorLoop β Id m] (iter : Std.Iter (α := β) α) (size? : Option Nat := none) :
    m ρ := do
  let state ← serializeSeqBegin (σ := σ) (m := m) (ρ := ρ) (ε := ε) size?
  let state ← iter.foldM (init := state) serializeSeqElem
  serializeSeqEnd state

@[inline]
def serializeDMap {α₁ β : Type u} {α₂ : α₁ → Type u} [Serialize α₁] [∀ x, Serialize (α₂ x)]
    [Std.Iterator β Id ((x : α₁) × (α₂ x))] [Std.IteratorLoop β Id m]
    (iter : Std.Iter (α := β) ((x : α₁) × (α₂ x))) (size? : Option Nat := none) : m ρ := do
  let state ← serializeMapBegin (σ := σ) (m := m) (ρ := ρ) (ε := ε) size?
  let state ← iter.foldM (init := state) fun state ⟨key, val⟩ => do
    let state ← serializeMapKey state key
    serializeMapVal state val
  serializeMapEnd state

@[inline]
def serializeMap {α₁ α₂ β : Type u} [Serialize α₁] [Serialize α₂]
    [Std.Iterator β Id (α₁ × α₂)] [Std.IteratorLoop β Id m]
    (iter : Std.Iter (α := β) (α₁ × α₂)) (size? : Option Nat := none) : m ρ := do
  let state ← serializeMapBegin (σ := σ) (m := m) (ρ := ρ) (ε := ε) size?
  let state ← iter.foldM (init := state) fun state (key, val) => do
    let state ← serializeMapKey state key
    serializeMapVal state val
  serializeMapEnd state

@[inline]
def serializeProd [Serialize α] [Serialize β] (xs : α × β) : m ρ := do
  let state ← serializeTupleBegin 2
  let state ← serializeTupleElem state xs.1
  let state ← serializeTupleElem state xs.2
  serializeTupleEnd state

@[inline]
def serializeSigma {α : Type u} {β : α → Type u} [Serialize α] [∀ x, Serialize (β x)]
    (xs : (x : α) × (β x)) : m ρ := do
  let state ← serializeTupleBegin 2
  let state ← serializeTupleElem state xs.1
  let state ← serializeTupleElem state xs.2
  serializeTupleEnd state

@[inline]
def serializeVector {α : Type u} [Serialize α] (xs : Vector α n) : m ρ := do
  let state ← serializeTupleBegin xs.size
  let state ← xs.foldlM (b := state) fun state val =>
    serializeTupleElem state val
  serializeTupleEnd state

end Serializer

end Std.Internal.Derse
