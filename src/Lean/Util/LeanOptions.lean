/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
import Lean.Util.Paths

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

/-- Options that are used by Lean as if they were passed using `-D`. -/
structure LeanOptions where
  values : RBMap Name LeanOptionValue Name.cmp
  deriving Inhabited, Repr

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
  fromJson?
    | Json.obj obj => do
      let values ← obj.foldM (init := RBMap.empty) fun acc k v => do
        let optionValue ← fromJson? v
        return acc.insert k.toName optionValue
      return ⟨values⟩
    | _ => Except.error "invalid LeanOptions type"

instance : ToJson LeanOptions where
  toJson options :=
    Json.obj <| options.values.fold (init := RBNode.leaf) fun acc k v =>
      acc.insert (cmp := compare) k.toString (toJson v)

end Lean
