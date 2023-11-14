import Lean.Util.Paths

namespace Lean

/-- Restriction of `DataValue` that covers exactly those cases that Lean is able to handle when passed via the `-D` flag. -/
inductive ServerOptionValue where
  | ofString (s : String)
  | ofBool   (b : Bool)
  | ofNat    (n : Nat)
  deriving Inhabited, Repr

def ServerOptionValue.ofDataValue? : DataValue → Option ServerOptionValue
  | .ofString s => some (.ofString s)
  | .ofBool b   => some (.ofBool b)
  | .ofNat n    => some (.ofNat n)
  | _           => none

def ServerOptionValue.toDataValue : ServerOptionValue → DataValue
  | .ofString s => .ofString s
  | .ofBool b   => .ofBool b
  | .ofNat n    => .ofNat n

instance : KVMap.Value ServerOptionValue where
  toDataValue  := ServerOptionValue.toDataValue
  ofDataValue? := ServerOptionValue.ofDataValue?

instance : Coe String ServerOptionValue where
  coe := ServerOptionValue.ofString

instance : Coe Bool ServerOptionValue where
  coe := ServerOptionValue.ofBool

instance : Coe Nat ServerOptionValue where
  coe := ServerOptionValue.ofNat

instance : FromJson ServerOptionValue where
  fromJson?
    | (s : String) => Except.ok s
    | (b : Bool)   => Except.ok b
    | (n : Nat)    => Except.ok n
    | _ => Except.error "invalid ServerOptionValue type"

instance : ToJson ServerOptionValue where
  toJson
    | (s : String) => s
    | (b : Bool)   => b
    | (n : Nat)    => n

/-- Formats the server option value as a CLI flag argument. -/
def ServerOptionValue.asCliFlagValue : (v : ServerOptionValue) → String
  | (s : String) => s!"\"{s}\""
  | (b : Bool)   => toString b
  | (n : Nat)    => toString n

/-- Options that are used by the server as if they were passed using `-D`. -/
structure ServerOptions where
  values : RBMap Name ServerOptionValue Name.cmp
  deriving Inhabited, Repr

def ServerOptions.toOptions (serverOptions : ServerOptions) : Options := Id.run do
  let mut options := KVMap.empty
  for ⟨name, optionValue⟩ in serverOptions.values do
    options := options.insert name optionValue.toDataValue
  return options

def ServerOptions.fromOptions? (options : Options) : Option ServerOptions := do
  let mut values := RBMap.empty
  for ⟨name, dataValue⟩ in options do
    let optionValue ← ServerOptionValue.ofDataValue? dataValue
    values := values.insert name optionValue
  return ⟨values⟩

instance : FromJson ServerOptions where
  fromJson?
    | Json.obj obj => do
      let values ← obj.foldM (init := RBMap.empty) fun acc k v => do
        let optionValue ← fromJson? v
        return acc.insert k.toName optionValue
      return ⟨values⟩
    | _ => Except.error "invalid ServerOptions type"

instance : ToJson ServerOptions where
  toJson options :=
    Json.obj <| options.values.fold (init := RBNode.leaf) fun acc k v =>
      acc.insert (cmp := compare) k.toString (toJson v)

end Lean
