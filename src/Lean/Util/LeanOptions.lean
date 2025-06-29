/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Data.Json

namespace Lean

/-- Restriction of `DataValue` that covers exactly those cases that Lean is able to handle when passed via the `-D` flag. -/
inductive LeanOptionValue where
  | ofString (s : String)
  | ofBool   (b : Bool)
  | ofNat    (n : Nat)
  deriving Inhabited, Repr

def LeanOptionValue.ofDataValue? : DataValue → Option LeanOptionValue
  | .ofString s => some (.ofString s)
  | .ofBool b   => some (.ofBool b)
  | .ofNat n    => some (.ofNat n)
  | _           => none

def LeanOptionValue.toDataValue : LeanOptionValue → DataValue
  | .ofString s => .ofString s
  | .ofBool b   => .ofBool b
  | .ofNat n    => .ofNat n

instance : KVMap.Value LeanOptionValue where
  toDataValue  := LeanOptionValue.toDataValue
  ofDataValue? := LeanOptionValue.ofDataValue?

instance : Coe String LeanOptionValue where
  coe := LeanOptionValue.ofString

instance : Coe Bool LeanOptionValue where
  coe := LeanOptionValue.ofBool

instance : Coe Nat LeanOptionValue where
  coe := LeanOptionValue.ofNat

instance : FromJson LeanOptionValue where
  fromJson?
    | (s : String) => Except.ok s
    | (b : Bool)   => Except.ok b
    | (n : Nat)    => Except.ok n
    | _ => Except.error "invalid LeanOptionValue type"

instance : ToJson LeanOptionValue where
  toJson
    | (s : String) => s
    | (b : Bool)   => b
    | (n : Nat)    => n

/-- Formats the lean option value as a CLI flag argument. -/
def LeanOptionValue.asCliFlagValue : (v : LeanOptionValue) → String
  | (s : String) => s!"\"{s}\""
  | (b : Bool)   => toString b
  | (n : Nat)    => toString n

/-- An option that is used by Lean as if it was passed using `-D`. -/
structure LeanOption where
  /-- The option's name. -/
  name  : Lean.Name
  /-- The option's value. -/
  value : Lean.LeanOptionValue
  deriving Inhabited, Repr

/-- Formats the lean option as a CLI argument using the `-D` flag. -/
def LeanOption.asCliArg (o : LeanOption) : String :=
  s!"-D{o.name}={o.value.asCliFlagValue}"

/-- Options that are used by Lean as if they were passed using `-D`. -/
structure LeanOptions where
  values : NameMap LeanOptionValue
  deriving Inhabited, Repr

instance : EmptyCollection LeanOptions := ⟨⟨∅⟩⟩

def LeanOptions.ofArray (opts : Array LeanOption) : LeanOptions :=
  ⟨opts.foldl (fun m {name, value} => m.insert name value) {}⟩

/-- Add the options from `new`, overriding those in `self`. -/
protected def LeanOptions.append (self new : LeanOptions) : LeanOptions :=
  ⟨self.values.mergeBy (fun _ _ b => b) new.values⟩

instance : Append LeanOptions := ⟨LeanOptions.append⟩

/-- Add the options from `new`, overriding those in `self`. -/
def LeanOptions.appendArray (self : LeanOptions) (new : Array LeanOption) : LeanOptions :=
  ⟨new.foldl (fun m {name, value} => m.insert name value) self.values⟩

instance : HAppend LeanOptions (Array LeanOption) LeanOptions := ⟨LeanOptions.appendArray⟩

def LeanOptions.toOptions (leanOptions : LeanOptions) : Options := Id.run do
  let mut options := KVMap.empty
  for ⟨name, optionValue⟩ in leanOptions.values do
    options := options.insert name optionValue.toDataValue
  return options

def LeanOptions.fromOptions? (options : Options) : Option LeanOptions := do
  let mut values := RBMap.empty
  for ⟨name, dataValue⟩ in options do
    let optionValue ← LeanOptionValue.ofDataValue? dataValue
    values := values.insert name optionValue
  return ⟨values⟩

instance : FromJson LeanOptions where
  fromJson? j := LeanOptions.mk <$> fromJson? j

instance : ToJson LeanOptions where
  toJson options := toJson options.values

end Lean
