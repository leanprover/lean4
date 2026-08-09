module
prelude
public import Std.Internal.Derse.Se.Basic
public import Std.Internal.Derse.Se.Serialize

namespace Std.Internal.Derse

section Writer

public class Writer (ω : Type) (m : outParam (Type → Type)) where
  write : ω → String → m Unit
  flush : ω → m Unit

instance : Writer IO.FS.Handle IO where
  write handle string := handle.putStr string
  flush handle := handle.flush

structure StringBuffer (σ : Type) where
  buf : ST.Ref σ String

def StringBuffer.new : ST σ (StringBuffer σ) := do
  return { buf := ← ST.mkRef "" }

instance : Writer (StringBuffer σ) (ST σ) where
  write buf string := buf.buf.modify fun s => s ++ string
  flush _ := return ()

end Writer

public structure JsonSerializer (ω : Type) (φ : Type) where
  writer : ω
  formatter : φ

public abbrev JsonT (ω φ : Type) (m : Type → Type) := StateT (JsonSerializer ω φ) m

@[inline]
public def JsonT.run [Functor m] (ser : JsonSerializer ω φ)
    (x : JsonT ω φ m α) : m α :=
  StateT.run' x ser

public class Formatter (φ : Type) where
  writeNull [Writer ω m] [Monad m] : JsonT ω φ m Unit
  writeBool [Writer ω m] [Monad m] (val : Bool) : JsonT ω φ m Unit
  writeUInt8 [Writer ω m] [Monad m] (val : UInt8) : JsonT ω φ m Unit
  writeUInt16 [Writer ω m] [Monad m] (val : UInt16) : JsonT ω φ m Unit
  writeUInt32 [Writer ω m] [Monad m] (val : UInt32) : JsonT ω φ m Unit
  /--
  Separate from `writeNat` because JSON consumers generally cannot represent 64 bit integers
  exactly, so a formatter may want to encode them as strings.
  -/
  writeUInt64 [Writer ω m] [Monad m] (val : UInt64) : JsonT ω φ m Unit
  writeInt8 [Writer ω m] [Monad m] (val : Int8) : JsonT ω φ m Unit
  writeInt16 [Writer ω m] [Monad m] (val : Int16) : JsonT ω φ m Unit
  writeInt32 [Writer ω m] [Monad m] (val : Int32) : JsonT ω φ m Unit
  /-- See `writeUInt64`. -/
  writeInt64 [Writer ω m] [Monad m] (val : Int64) : JsonT ω φ m Unit
  writeNat [Writer ω m] [Monad m] (val : Nat) : JsonT ω φ m Unit
  writeInt [Writer ω m] [Monad m] (val : Int) : JsonT ω φ m Unit
  writeFloat32 [Writer ω m] [Monad m] (val : Float32) : JsonT ω φ m Unit
  writeFloat [Writer ω m] [Monad m] (val : Float) : JsonT ω φ m Unit
  writeString [Writer ω m] [Monad m] (val : String) : JsonT ω φ m Unit
  beginArray [Writer ω m] [Monad m] : JsonT ω φ m Unit
  endArray [Writer ω m] [Monad m] : JsonT ω φ m Unit
  beginArrayValue [Writer ω m] [Monad m] (first : Bool) : JsonT ω φ m Unit
  endArrayValue [Writer ω m] [Monad m] : JsonT ω φ m Unit
  beginObject [Writer ω m] [Monad m] : JsonT ω φ m Unit
  endObject [Writer ω m] [Monad m] : JsonT ω φ m Unit
  beginObjectKey [Writer ω m] [Monad m] (first : Bool) : JsonT ω φ m Unit
  endObjectKey [Writer ω m] [Monad m] : JsonT ω φ m Unit
  beginObjectValue [Writer ω m] [Monad m] : JsonT ω φ m Unit
  endObjectValue [Writer ω m] [Monad m] : JsonT ω φ m Unit

-- TODO
instance : MonadExceptOf Empty (JsonT ω φ m) where
  throw := nofun
  tryCatch mx _ := mx

structure Aux where
  first : Bool

instance [Writer ω m] [Formatter φ] [Monad m] :
    Serializer (JsonSerializer ω φ) (JsonT ω φ m) Unit Empty where
  serializeBool b := Formatter.writeBool b
  serializeUInt8 v := Formatter.writeUInt8 v
  serializeUInt16 v := Formatter.writeUInt16 v
  serializeUInt32 v := Formatter.writeUInt32 v
  serializeUInt64 v := Formatter.writeUInt64 v
  serializeInt8 v := Formatter.writeInt8 v
  serializeInt16 v := Formatter.writeInt16 v
  serializeInt32 v := Formatter.writeInt32 v
  serializeInt64 v := Formatter.writeInt64 v
  serializeNat v := Formatter.writeNat v
  serializeInt v := Formatter.writeInt v
  serializeFloat v := Formatter.writeFloat v
  serializeFloat32 v := Formatter.writeFloat32 v
  serializeChar v := Formatter.writeString v.toString
  serializeName v := Formatter.writeString v.toString
  serializeString v := Formatter.writeString v
  serializeBytes v := do
    Formatter.beginArray
    let mut first := true
    for elem in v do
      Formatter.beginArrayValue first
      Formatter.writeUInt8 elem
      Formatter.endArrayValue
      first := false
    Formatter.endArray
  serializeNone := Formatter.writeNull
  serializeSomeWith v ser := ser v
  serializeUnit := do Formatter.beginObject; Formatter.endObject
  serializeUnitStructure _ := do Formatter.beginObject; Formatter.endObject
  serializeUnitAlt _ _ altName := Formatter.writeString altName

  SeqState := Aux
  serializeSeqBegin _ := do
    Formatter.beginArray
    return Aux.mk true
  serializeSeqElemWith aux val ser := do
    Formatter.beginArrayValue aux.first
    ser val
    Formatter.endArrayValue
    return { first := false }
  serializeSeqEnd _ := Formatter.endArray

  -- TODO: dedup code?
  TupleState := Aux
  serializeTupleBegin _ := do
    Formatter.beginArray
    return Aux.mk true
  serializeTupleElemWith aux val ser := do
    Formatter.beginArrayValue aux.first
    ser val
    Formatter.endArrayValue
    return { first := false }
  serializeTupleEnd _ := Formatter.endArray

  MapState := Aux
  serializeMapBegin _ := do
    Formatter.beginObject
    return Aux.mk true
  serializeMapKeyWith aux val ser := do
    Formatter.beginObjectKey aux.first
    -- TODO: We need to employ a custom auxiliary serializer here
    ser val
    Formatter.endObjectKey
    return { first := false }
  serializeMapValWith _ val ser := do
    Formatter.beginObjectValue
    ser val
    Formatter.endObjectValue
    return { first := false }
  serializeMapEnd _ := Formatter.endObject

  StructState := Aux
  serializeStructBegin _ _ := do
    Formatter.beginObject
    return Aux.mk true
  serializeStructFieldWith aux _ fieldName val ser := do
    Formatter.beginObjectKey aux.first
    Formatter.writeString fieldName
    Formatter.endObjectKey
    Formatter.beginObjectValue
    ser val
    Formatter.endObjectValue
    return { first := false }
  serializeStructEnd _ := Formatter.endObject

  AnonAltState := Aux
  serializeAnonAltBegin _ _ altName _ := do
    Formatter.beginObject
    Formatter.beginObjectKey true
    Formatter.writeString altName
    Formatter.endObjectKey
    Formatter.beginObjectValue
    Formatter.beginArray
    return Aux.mk true
  serializeAnonAltFieldWith aux _ val ser := do
    Formatter.beginArrayValue aux.first
    ser val
    Formatter.endArrayValue
    return { first := false }
  serializeAnonAltEnd _ := do
    Formatter.endArray
    Formatter.endObjectValue
    Formatter.endObject

  NamedAltState := Aux
  serializeNamedAltBegin _ _ altName _ := do
    Formatter.beginObject
    Formatter.beginObjectKey true
    Formatter.writeString altName
    Formatter.endObjectKey
    Formatter.beginObjectValue
    Formatter.beginObject
    return Aux.mk true
  serializeNamedAltFieldWith aux _ fieldName val ser := do
    Formatter.beginObjectKey aux.first
    Formatter.writeString fieldName
    Formatter.endObjectKey
    Formatter.beginObjectValue
    ser val
    Formatter.endObjectValue
    return { first := false }
  serializeNamedAltEnd _ := do
    Formatter.endObject
    Formatter.endObject

@[inline]
public def JsonT.write [Writer ω m] [Monad m] (s : String) : JsonT ω φ m Unit := do
  liftM <| Writer.write (← get).writer s

/--
A `Formatter` that emits JSON without any insignificant whitespace.

The instance lives in `Lean.Data.Json.Derse` because it reuses the string escaping and number
rendering from `Lean.Json`; it moves here once that infrastructure is available in `Std`.
-/
public structure CompactFormatter where

/-
TODO
public structure PrettyFormatter where

instance : Formatter PrettyFormatter where
-/

namespace Json

-- TODO : default arguments for formatter

public def toString [Serialize α] [Formatter φ] (xs : α) (fmt : φ) : String := runST fun _ => do
  let buf ← StringBuffer.new
  let ser := JsonSerializer.mk buf fmt
  let ser ← JsonT.run ser do
    Serialize.serialize xs
    get
  ser.writer.buf.get

public def toHandle [Serialize α] [Formatter φ] (xs : α) (fmt : φ) (file : IO.FS.Handle) :
    IO Unit := do
  let ser := JsonSerializer.mk file fmt 
  JsonT.run ser do
    Serialize.serialize xs

end Json

end Std.Internal.Derse
