/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.ScopedEnvExtension
import Lean.DocString

/-!
# "Label" attributes

Allow creating attributes using `register_label_attr`,
and retrieving the array of `Name`s of declarations which have been tagged with such an attribute.

These differ slightly from the built-in "tag attributes" which can be initialized with the syntax:
```
initialize someName : TagAttribute ← registerTagAttribute `tagName "description"
```
in that a "tag attribute" can only be put on a declaration at the moment it is declared,
and can not be modified by scoping commands.

The "label attributes" constructed here support adding (or locally removing) the attribute
either at the moment of declaration, or later.

-/

namespace Lean

/-- An environment extension that just tracks an array of names. -/
abbrev LabelExtension := SimpleScopedEnvExtension Name (Array Name)

/-- The collection of all current `LabelExtension`s, indexed by name. -/
abbrev LabelExtensionMap := Std.HashMap Name LabelExtension

/-- Store the current `LabelExtension`s. -/
builtin_initialize labelExtensionMapRef : IO.Ref LabelExtensionMap ← IO.mkRef {}

/-- Helper function for `registerLabelAttr`. -/
def mkLabelExt (name : Name := by exact decl_name%) : IO LabelExtension :=
  registerSimpleScopedEnvExtension {
    name     := name
    initial  := #[]
    addEntry := fun d e => if d.contains e then d else d.push e
  }

/-- Helper function for `registerLabelAttr`. -/
def mkLabelAttr (attrName : Name) (attrDescr : String) (ext : LabelExtension)
  (ref : Name := by exact decl_name%) : IO Unit :=
registerBuiltinAttribute {
  ref   := ref
  name  := attrName
  descr := attrDescr
  applicationTime := AttributeApplicationTime.afterCompilation
  add   := fun declName _ kind =>
    ext.add declName kind
  erase := fun declName => do
    let s := ext.getState (← getEnv)
    modifyEnv fun env => ext.modifyState env fun _ => s.erase declName
}

/--
Construct a new "label attribute",
which does nothing except keep track of the names of the declarations with that attribute.

Users will generally use the `register_label_attr` macro defined below.
-/
def registerLabelAttr (attrName : Name) (attrDescr : String)
    (ref : Name := by exact decl_name%) : IO LabelExtension := do
  let ext ← mkLabelExt ref
  mkLabelAttr attrName attrDescr ext ref
  labelExtensionMapRef.modify fun map => map.insert attrName ext
  return ext

/--
Initialize a new "label" attribute.
Declarations tagged with the attribute can be retrieved using `Lean.labelled`.
-/
macro (name := _root_.Lean.Parser.Command.registerLabelAttr)
  doc:(docComment)? "register_label_attr " id:ident : command => do
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString) |>.getD ("labelled declarations for " ++ id.getId.toString)).removeLeadingSpaces)
  `($[$doc:docComment]? initialize ext : Lean.LabelExtension ←
      registerLabelAttr $(quote id.getId) $descr $(quote id.getId)
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str : attr)

/-- When `attrName` is an attribute created using `register_labelled_attr`,
return the names of all declarations labelled using that attribute. -/
def labelled (attrName : Name) : CoreM (Array Name) := do
  match (← labelExtensionMapRef.get)[attrName]? with
  | none => throwError "No extension named {attrName}"
  | some ext => pure <| ext.getState (← getEnv)

end Lean
