/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Data.Options
universes u v

namespace Std
namespace Format
open Lean

def getWidth (o : Options) : Nat    := o.get `format.width  defWidth
def getIndent (o : Options) : Nat   := o.get `format.indent defIndent
def getUnicode (o : Options) : Bool := o.get `format.unicode defUnicode

builtin_initialize
  registerOption `format.indent { defValue := defIndent, group := "format", descr := "indentation" }
  registerOption `format.unicode { defValue := defUnicode, group := "format", descr := "unicode characters" }
  registerOption `format.width { defValue := defWidth, group := "format", descr := "line width" }

def pretty' (f : Format) (o : Options := {}) : String :=
  pretty f (getWidth o)

protected def repr : Format → Format
  | nil => "Format.nil"
  | line => "Format.line"
  | text s => paren $ "Format.text" ++ line ++ repr s
  | nest n f => paren $ "Format.nest" ++ line ++ repr n ++ line ++ Format.repr f
  | append f₁ f₂ => paren $ "Format.append " ++ line ++ Format.repr f₁ ++ line ++ Format.repr f₂
  | group f FlattenBehavior.allOrNone => paren $ "Format.group" ++ line ++ Format.repr f
  | group f FlattenBehavior.fill => paren $ "Format.fill" ++ line ++ Format.repr f

instance : Repr Format where
  repr := Format.pretty ∘ Format.repr

end Format
end Std

namespace Lean
open Std

export Std
  (Format ToFormat fmt Format.nest Format.nil Format.joinSep Format.line
   Format.sbracket Format.bracket Format.group Format.pretty Format.fill Format.paren Format.join)
export Std.ToFormat (format)

instance : ToFormat Name where
  format n := n.toString

instance : ToFormat DataValue where
  format
    | DataValue.ofString v => format (repr v)
    | DataValue.ofBool v   => format v
    | DataValue.ofName v   => "`" ++ format v
    | DataValue.ofNat v    => format v
    | DataValue.ofInt v    => format v

instance : ToFormat (Name × DataValue) where
  format
    | (n, v) => format n ++ " := " ++ format v


open Std.Format

def formatKVMap (m : KVMap) : Format :=
  sbracket (Format.joinSep m.entries ", ")

instance : ToFormat KVMap := ⟨formatKVMap⟩

end Lean
