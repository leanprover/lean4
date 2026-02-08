/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.FilePath
public import Lake.Toml.Data.Value

/-!
# TOML Encoders

This module contains definitions to assist in encoding Lean types
into TOML data values.
-/

namespace Lake

open System Lean Toml

public class ToToml (α : Type u) where
  toToml : α → Value

export ToToml (toToml)

public instance : ToToml Value := ⟨id⟩
public instance : ToToml String := ⟨.string .missing⟩
public instance : ToToml FilePath := ⟨(toToml <| mkRelPathString ·)⟩
public instance : ToToml Name := ⟨(toToml ·.toString)⟩
public instance : ToToml Int := ⟨.integer .missing⟩
public instance : ToToml Nat := ⟨fun n => .integer .missing (.ofNat n)⟩
public instance : ToToml Float := ⟨.float .missing⟩
public instance : ToToml Bool := ⟨.boolean .missing⟩
public instance [ToToml α] : ToToml (Array α) := ⟨(.array .missing <| ·.map toToml)⟩
public instance : ToToml (Array Value) := ⟨(.array .missing <| ·)⟩
public instance : ToToml Table := ⟨.table .missing⟩

public class ToToml? (α : Type u) where
  toToml? : α → Option Value

export ToToml? (toToml?)

public instance(priority := high) [ToToml α] : ToToml? α where
  toToml? v := some (toToml v)

public def Toml.encodeArray? [ToToml? α] (as : Array α) : Option (Array Value) :=
  as.foldl (init := some #[]) fun vs? a => do
    let vs ← vs?
    let v ← toToml? a
    return vs.push v

public instance [ToToml? α] : ToToml? (Array α) where
  toToml? as := toToml <$> Toml.encodeArray? as

public instance [ToToml? α] : ToToml? (Option α) := ⟨(·.bind toToml?)⟩
public instance [ToToml α] : ToToml? (Option α) := ⟨(·.map toToml)⟩

namespace Toml

public class SmartInsert (α : Type u) where
  /-- Insert a value into a table unless it represents a nullish value. -/
  smartInsert (k : Name) : α → Table → Table

public instance (priority := low) [ToToml? α] : SmartInsert α where
  smartInsert k v t := t.insertSome k (toToml? v)

public instance : SmartInsert Table where
  smartInsert k v t := t.insertUnless v.isEmpty k (toToml v)

public instance [ToToml (Array α)] : SmartInsert (Array α) where
  smartInsert k v t := t.insertUnless v.isEmpty k (toToml v)

public instance : SmartInsert String where
  smartInsert k v t := t.insertUnless v.isEmpty k (toToml v)

namespace Table

/-- Inserts the encoded value into the table. -/
@[inline] public nonrec def insert
  [enc : ToToml α] (k : Name) (v : α) (t : Table) : Table
:= t.insert k (enc.toToml v)

/-- If the value is not `none`, inserts the encoded value into the table. -/
@[macro_inline, expose] public nonrec def insertSome
  [enc : ToToml α] (k : Name) (v? : Option α) (t : Table)
: Table := t.insertSome k (v?.map enc.toToml)

public instance [ToToml α] : SmartInsert (Option α) := ⟨Table.insertSome⟩

/-- Insert a value into the table unless it represents a nullish value. -/
@[inline] public nonrec def smartInsert
  [SmartInsert α] (k : Name) (v : α) (t : Table)
: Table := SmartInsert.smartInsert k v t

/-- Insert a value into the table if `p` is `true`. -/
@[macro_inline, expose] public nonrec def insertIf
  [enc : ToToml α] (p : Bool) (k : Name) (v : α) (t : Table)
: Table := t.insertIf p k (enc.toToml v)

/-- Insert a value into the table if `p` is `false`. -/
@[macro_inline, expose] public nonrec def insertUnless
  [enc : ToToml α] (p : Bool) (k : Name) (v : α) (t : Table)
: Table := t.insertUnless p k (enc.toToml v)

/-- Inserts the value into the table if it is not equal to `default`. -/
@[inline] public def insertD
  [enc : ToToml α] [BEq α] (k : Name) (v : α) (default : α) (t : Table)
: Table := t.insertUnless (v == default) k (enc.toToml v)
