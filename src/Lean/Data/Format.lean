/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Data.Options
universe u v

namespace Std
namespace Format
open Lean

def getWidth (o : Options) : Nat    := o.get `format.width  defWidth
def getIndent (o : Options) : Nat   := o.get `format.indent defIndent
def getUnicode (o : Options) : Bool := o.get `format.unicode defUnicode

register_builtin_option format.width : Nat := {
  defValue := defWidth
  descr := "indentation"
}

register_builtin_option format.unicode : Bool := {
  defValue := defUnicode
  descr    := "unicode characters"
}

register_builtin_option format.indent : Nat := {
  defValue := defIndent
  descr    := "indentation"
}

def pretty' (f : Format) (o : Options := {}) : String :=
  pretty f (format.width.get o)

end Format
end Std

namespace Lean
open Std

export Std
  (Format ToFormat Format.nest Format.nil Format.joinSep Format.line
   Format.sbracket Format.bracket Format.group Format.tag Format.pretty
   Format.fill Format.paren Format.join Format.align)
export ToFormat (format)

instance : ToFormat Name where
  format n := n.toString

instance : ToFormat DataValue where
  format
    | DataValue.ofString v => format (repr v)
    | DataValue.ofBool v   => format v
    | DataValue.ofName v   => "`" ++ format v
    | DataValue.ofNat v    => format v
    | DataValue.ofInt v    => format v
    | DataValue.ofSyntax v => format v

instance : ToFormat (Name × DataValue) where
  format
    | (n, v) => format n ++ " := " ++ format v


open Std.Format

def formatKVMap (m : KVMap) : Format :=
  sbracket (Format.joinSep m.entries ", ")

instance : ToFormat KVMap := ⟨formatKVMap⟩

end Lean
