/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Data.Name

namespace String

private def mangleAux : Nat → String.Iterator → String → String
  | 0,   _,  r => r
  | i+1, it, r =>
    let c := it.curr
    if c.isAlpha || c.isDigit then
      mangleAux i it.next (r.push c)
    else if c = '_' then
      mangleAux i it.next (r ++ "__")
    else if c.toNat < 0x100 then
      let n := c.toNat
      let r := r ++ "_x"
      let r := r.push <| Nat.digitChar (n / 0x10)
      let r := r.push <| Nat.digitChar (n % 0x10)
      mangleAux i it.next r
    else if c.toNat < 0x10000 then
      let n := c.toNat
      let r := r ++ "_u"
      let r := r.push <| Nat.digitChar (n / 0x1000)
      let n := n % 0x1000
      let r := r.push <| Nat.digitChar (n / 0x100)
      let n := n % 0x100
      let r := r.push <| Nat.digitChar (n / 0x10)
      let r := r.push <| Nat.digitChar (n % 0x10)
      mangleAux i it.next r
    else
      let n := c.toNat
      let r := r ++ "_U"
      let ds := Nat.toDigits 16 n
      let r := Nat.repeat (·.push '0') (8 - ds.length) r
      let r := ds.foldl (fun r c => r.push c) r
      mangleAux i it.next r

def mangle (s : String) : String :=
  mangleAux s.length s.mkIterator ""

end String

namespace Lean

private def Name.mangleAux : Name → String
  | Name.anonymous => ""
  | Name.str p s =>
    let m := String.mangle s
    match p with
    | Name.anonymous => m
    | p              => mangleAux p ++ "_" ++ m
  | Name.num p n => mangleAux p ++ "_" ++ toString n ++ "_"

@[export lean_name_mangle]
def Name.mangle (n : Name) (pre : String := "l_") : String :=
  pre ++ Name.mangleAux n

@[export lean_mk_module_initialization_function_name]
def mkModuleInitializationFunctionName (moduleName : Name) : String :=
  "initialize_" ++ moduleName.mangle ""

end Lean
