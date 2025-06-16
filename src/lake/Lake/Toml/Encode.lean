/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Toml.Data
import Lake.Util.FilePath

/-!
# TOML Encoders

This module contains definitions to assist in encoding Lean types
into TOML data values.
-/

namespace Lake

open System Lean Toml

class ToToml (α : Type u) where
  toToml : α → Value

export ToToml (toToml)

instance : ToToml Value := ⟨id⟩
instance : ToToml String := ⟨.string .missing⟩
instance : ToToml FilePath := ⟨(toToml <| mkRelPathString ·)⟩
instance : ToToml Name := ⟨(toToml ·.toString)⟩
instance : ToToml Int := ⟨.integer .missing⟩
instance : ToToml Nat := ⟨fun n => .integer .missing (.ofNat n)⟩
instance : ToToml Float := ⟨.float .missing⟩
instance : ToToml Bool := ⟨.boolean .missing⟩
instance [ToToml α] : ToToml (Array α) := ⟨(.array .missing <| ·.map toToml)⟩
instance : ToToml (Array Value) := ⟨(.array .missing <| ·)⟩
instance : ToToml Table := ⟨.table .missing⟩

class ToToml? (α : Type u) where
  toToml? : α → Option Value

export ToToml? (toToml?)

instance(priority := high) [ToToml α] : ToToml? α where
  toToml? v := some (toToml v)

def Toml.encodeArray? [ToToml? α] (as : Array α) : Option (Array Value) :=
  as.foldl (init := some #[]) fun vs? a => do
    let vs ← vs?
    let v ← toToml? a
    return vs.push v

instance [ToToml? α] : ToToml? (Array α) where
  toToml? as := toToml <$> Toml.encodeArray? as

instance [ToToml? α] : ToToml? (Option α) := ⟨(·.bind toToml?)⟩
instance [ToToml α] : ToToml? (Option α) := ⟨(·.map toToml)⟩

namespace Toml

/-- Insert a value into a table unless it represents a nullish value. -/
class SmartInsert (α : Type u) where
  smartInsert (k : Name) : α → Table → Table

instance (priority := low) [ToToml? α] : SmartInsert α where
  smartInsert k v t := t.insertSome k (toToml? v)

instance : SmartInsert Table where
  smartInsert k v t := t.insertUnless v.isEmpty k (toToml v)

instance [ToToml (Array α)] : SmartInsert (Array α) where
  smartInsert k v t := t.insertUnless v.isEmpty k (toToml v)

instance : SmartInsert String where
  smartInsert k v t := t.insertUnless v.isEmpty k (toToml v)

namespace Table

/-- Inserts the encoded value into the table. -/
@[inline] nonrec def insert [enc : ToToml α] (k : Name) (v : α) (t : Table) : Table :=
  t.insert k (enc.toToml v)

/-- If the value is not `none`, inserts the encoded value into the table. -/
@[inline] nonrec def insertSome [enc : ToToml α] (k : Name) (v? : Option α) (t : Table) : Table :=
  t.insertSome k (v?.map enc.toToml)

instance [ToToml α] : SmartInsert (Option α) := ⟨Table.insertSome⟩

/-- Insert a value into the table unless it represents a nullish value. -/
@[inline] nonrec def smartInsert [SmartInsert α] (k : Name) (v : α) (t : Table) : Table :=
  SmartInsert.smartInsert k v t

/-- Insert a value into the table if `p` is `true`. -/
@[inline] nonrec def insertIf [enc : ToToml α] (p : Bool) (k : Name) (v : α) (t : Table) : Table :=
  t.insertIf p k (enc.toToml v)

/-- Insert a value into the table if `p` is `false`. -/
@[inline] nonrec def insertUnless [enc : ToToml α] (p : Bool) (k : Name) (v : α) (t : Table) : Table :=
  t.insertUnless p k (enc.toToml v)

/-- Inserts the value into the table if it is not equal to `default`. -/
@[inline] def insertD [enc : ToToml α] [BEq α] (k : Name) (v : α) (default : α) (t : Table) : Table :=
  t.insertUnless (v == default) k (enc.toToml v)
