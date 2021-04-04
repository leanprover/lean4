/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.Name

namespace Lean

inductive DataValue where
  | ofString (v : String)
  | ofBool   (v : Bool)
  | ofName   (v : Name)
  | ofNat    (v : Nat)
  | ofInt    (v : Int)
  deriving Inhabited, BEq

@[export lean_mk_bool_data_value] def mkBoolDataValueEx (b : Bool) : DataValue := DataValue.ofBool b
@[export lean_data_value_bool] def DataValue.getBoolEx : DataValue → Bool
  | DataValue.ofBool b => b
  | _                  => false

def DataValue.sameCtor : DataValue → DataValue → Bool
  | DataValue.ofString _, DataValue.ofString _ => true
  | DataValue.ofBool _,   DataValue.ofBool _   => true
  | DataValue.ofName _,   DataValue.ofName _   => true
  | DataValue.ofNat _,    DataValue.ofNat _    => true
  | DataValue.ofInt _,    DataValue.ofInt _    => true
  | _,                    _                    => false

@[export lean_data_value_to_string]
def DataValue.str : DataValue → String
  | DataValue.ofString v => v
  | DataValue.ofBool v   => toString v
  | DataValue.ofName v   => toString v
  | DataValue.ofNat v    => toString v
  | DataValue.ofInt v    => toString v

instance : ToString DataValue := ⟨DataValue.str⟩

instance : Coe String DataValue := ⟨DataValue.ofString⟩
instance : Coe Bool DataValue   := ⟨DataValue.ofBool⟩
instance : Coe Name DataValue   := ⟨DataValue.ofName⟩
instance : Coe Nat DataValue    := ⟨DataValue.ofNat⟩
instance : Coe Int DataValue    := ⟨DataValue.ofInt⟩

/- Remark: we do not use RBMap here because we need to manipulate KVMap objects in
   C++ and RBMap is implemented in Lean. So, we use just a List until we can
   generate C++ code from Lean code. -/
structure KVMap where
  entries : List (Name × DataValue) := []
  deriving Inhabited

namespace KVMap
instance : ToString KVMap := ⟨fun m => toString m.entries⟩

def empty : KVMap :=
  {}

def isEmpty : KVMap → Bool
  | ⟨m⟩ => m.isEmpty

def size (m : KVMap) : Nat :=
  m.entries.length

def findCore : List (Name × DataValue) → Name → Option DataValue
  | [],       k' => none
  | (k,v)::m, k' => if k == k' then some v else findCore m k'

def find : KVMap → Name → Option DataValue
  | ⟨m⟩, k => findCore m k

def findD (m : KVMap) (k : Name) (d₀ : DataValue) : DataValue :=
  (m.find k).getD d₀

def insertCore : List (Name × DataValue) → Name → DataValue → List (Name × DataValue)
  | [],       k', v' => [(k',v')]
  | (k,v)::m, k', v' => if k == k' then (k, v') :: m else (k, v) :: insertCore m k' v'

def insert : KVMap → Name → DataValue → KVMap
  | ⟨m⟩, k, v => ⟨insertCore m k v⟩

def contains (m : KVMap) (n : Name) : Bool :=
  (m.find n).isSome

def getString (m : KVMap) (k : Name) (defVal := "") : String :=
  match m.find k with
  | some (DataValue.ofString v) => v
  | _                           => defVal

def getNat (m : KVMap) (k : Name) (defVal := 0) : Nat :=
  match m.find k with
  | some (DataValue.ofNat v) => v
  | _                        => defVal

def getInt (m : KVMap) (k : Name) (defVal : Int := 0) : Int :=
  match m.find k with
  | some (DataValue.ofInt v) => v
  | _                        => defVal

def getBool (m : KVMap) (k : Name) (defVal := false) : Bool :=
  match m.find k with
  | some (DataValue.ofBool v) => v
  | _                         => defVal

def getName (m : KVMap) (k : Name) (defVal := Name.anonymous) : Name :=
  match m.find k with
  | some (DataValue.ofName v) => v
  | _                         => defVal

def setString (m : KVMap) (k : Name) (v : String) : KVMap :=
  m.insert k (DataValue.ofString v)

def setNat (m : KVMap) (k : Name) (v : Nat) : KVMap :=
  m.insert k (DataValue.ofNat v)

def setInt (m : KVMap) (k : Name) (v : Int) : KVMap :=
  m.insert k (DataValue.ofInt v)

def setBool (m : KVMap) (k : Name) (v : Bool) : KVMap :=
  m.insert k (DataValue.ofBool v)

def setName (m : KVMap) (k : Name) (v : Name) : KVMap :=
  m.insert k (DataValue.ofName v)

@[inline] protected def forIn.{w, w'} {δ : Type w} {m : Type w → Type w'} [Monad m]
  (kv : KVMap) (init : δ) (f : Name × DataValue → δ → m (ForInStep δ)) : m δ :=
  kv.entries.forIn init f

instance : ForIn m KVMap (Name × DataValue) where
  forIn := KVMap.forIn

def subsetAux : List (Name × DataValue) → KVMap → Bool
  | [],          m₂ => true
  | (k, v₁)::m₁, m₂ =>
    match m₂.find k with
    | some v₂ => v₁ == v₂ && subsetAux m₁ m₂
    | none    => false

def subset : KVMap → KVMap → Bool
  | ⟨m₁⟩, m₂ => subsetAux m₁ m₂

def eqv (m₁ m₂ : KVMap) : Bool :=
  subset m₁ m₂ && subset m₂ m₁

instance : BEq KVMap where
  beq := eqv

class Value (α : Type) where
  toDataValue  : α → DataValue
  ofDataValue? : DataValue → Option α

@[inline] def get? {α : Type} [s : Value α] (m : KVMap) (k : Name) : Option α :=
  m.find k |>.bind Value.ofDataValue?

@[inline] def get {α : Type} [s : Value α] (m : KVMap) (k : Name) (defVal : α) : α :=
  m.get? k |>.getD defVal

@[inline] def set {α : Type} [s : Value α] (m : KVMap) (k : Name) (v : α) : KVMap :=
  m.insert k (Value.toDataValue v)

instance : Value DataValue where
  toDataValue  := id
  ofDataValue? := some

instance : Value Bool where
  toDataValue  := DataValue.ofBool
  ofDataValue?
    | DataValue.ofBool b => some b
    | _                  => none

instance : Value Nat where
  toDataValue  := DataValue.ofNat
  ofDataValue?
    | DataValue.ofNat n => some n
    | _                 => none

instance : Value Int where
  toDataValue  := DataValue.ofInt
  ofDataValue?
    | DataValue.ofInt i => some i
    | _                 => none

instance : Value Name where
  toDataValue  := DataValue.ofName
  ofDataValue?
    | DataValue.ofName n => some n
    | _                  => none

instance : Value String where
  toDataValue  := DataValue.ofString
  ofDataValue?
    | DataValue.ofString n => some n
    | _                    => none

end Lean.KVMap
