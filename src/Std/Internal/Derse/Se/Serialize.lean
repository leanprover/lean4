module

prelude
public import Init.Data.String.Slice
public import Std.Internal.Derse.Se.Basic
public import Std.Data.Iterators.Producers.Array
public import Std.Data.HashSet.Basic
public import Std.Data.HashSet.Iterator
public import Std.Data.TreeSet.Basic
public import Std.Data.TreeSet.Iterator

public section

namespace Std.Internal.Derse

open Lean

instance : Serialize Bool where
  serialize b := Serializer.serializeBool b

instance : Serialize UInt8 where
  serialize v := Serializer.serializeUInt8 v

instance : Serialize UInt16 where
  serialize v := Serializer.serializeUInt16 v

instance : Serialize UInt32 where
  serialize v := Serializer.serializeUInt32 v

instance : Serialize UInt64 where
  serialize v := Serializer.serializeUInt64 v

instance : Serialize USize where
  serialize v := Serializer.serializeUInt64 v.toUInt64

instance : Serialize Int8 where
  serialize v := Serializer.serializeInt8 v

instance : Serialize Int16 where
  serialize v := Serializer.serializeInt16 v

instance : Serialize Int32 where
  serialize v := Serializer.serializeInt32 v

instance : Serialize Int64 where
  serialize v := Serializer.serializeInt64 v

instance : Serialize ISize where
  serialize v := Serializer.serializeInt64 v.toInt64

instance : Serialize Nat where
  serialize v := Serializer.serializeNat v

instance : Serialize Int where
  serialize v := Serializer.serializeInt v

instance : Serialize Float where
  serialize v := Serializer.serializeFloat v

instance : Serialize Float32 where
  serialize v := Serializer.serializeFloat32 v

instance : Serialize Char where
  serialize v := Serializer.serializeChar v

instance : Serialize Name where
  serialize v := Serializer.serializeName v

instance : Serialize String where
  serialize v := Serializer.serializeString v

-- TODO: maybe Serializer.serializeString should take a slice instead?
instance : Serialize String.Slice where
  serialize v := Serializer.serializeString v.copy

instance : Serialize ByteArray where
  serialize v := Serializer.serializeBytes v

instance : Serialize Unit where
  serialize _ := Serializer.serializeUnit

instance : Serialize PUnit where
  serialize _ := Serializer.serializeUnit

instance : Serialize Empty where
  serialize := nofun

instance [Serialize α] : Serialize (Option α) where
  serialize o := Serializer.serializeOption o

instance [Std.Iterator β Id α] [∀ m, Std.IteratorLoop β Id m] [Serialize α] :
    Serialize (Std.Iter (α := β) α) where
  serialize iter := Serializer.serializeSeq iter

instance [Serialize α] : Serialize (List α) where
  serialize xs := Serializer.serializeSeq xs.iter

instance [Serialize α] : Serialize (Array α) where
  serialize xs := Serializer.serializeSeq xs.iter

instance [Serialize α] [BEq α] [Hashable α] : Serialize (HashSet α) where
  serialize xs := Serializer.serializeSeq xs.iter

instance [Serialize α] : Serialize (TreeSet α cmp) where
  serialize xs := Serializer.serializeSeq xs.iter

instance [Serialize α] [BEq α] [Hashable α] : Serialize (HashSet α) where
  serialize xs := Serializer.serializeSeq xs.iter

instance [Serialize α] : Serialize (TreeSet α cmp) where
  serialize xs := Serializer.serializeSeq xs.iter

instance [Serialize α] [Serialize β] [BEq α] [Hashable α] : Serialize (HashMap α β) where
  serialize xs := Serializer.serializeMap xs.iter

instance [Serialize α] [Serialize β] : Serialize (TreeMap α β cmp) where
  serialize xs := Serializer.serializeMap xs.iter

instance [Serialize α] [∀ k, Serialize (β k)] [BEq α] [Hashable α] : Serialize (DHashMap α β) where
  serialize xs := Serializer.serializeDMap xs.iter

instance [Serialize α] [∀ k, Serialize (β k)] : Serialize (DTreeMap α β cmp) where
  serialize xs := Serializer.serializeDMap xs.iter

instance [Serialize α] [Serialize β] : Serialize (α × β) where
  serialize xs := Serializer.serializeProd xs

instance {β : α → Type u} [Serialize α] [∀ x, Serialize (β x)] : Serialize ((x : α) × β x) where
  serialize xs := Serializer.serializeSigma xs

instance [Serialize α] : Serialize (Vector α n) where
  serialize xs := Serializer.serializeVector xs

end Std.Internal.Derse
