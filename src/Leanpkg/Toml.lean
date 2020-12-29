/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
import Lean.Parser

namespace Toml

inductive Value : Type where
  | str : String → Value
  | nat : Nat → Value
  | bool : Bool → Value
  | table : List (String × Value) → Value
  deriving Inhabited

def Value.lookup : Value → String → Option Value
  | Value.table cs, k => cs.lookup k
  | _, _ => none

-- TODO: custom whitespace and other inaccuracies
declare_syntax_cat val
syntax "True" : val
syntax "False" : val
syntax str : val
syntax num : val
syntax bareKey := ident  -- TODO
syntax key := bareKey <|> str
declare_syntax_cat keyCat @[keyCatParser] def key' := key  -- HACK: for the antiquotation
syntax keyVal := key " = " val
syntax table := "[" key "]" keyVal*
syntax inlineTable := "{" keyVal,* "}"
syntax inlineTable : val
syntax file := table*
declare_syntax_cat fileCat @[fileCatParser] def file' := file  -- HACK: for the antiquotation

open Lean

partial def ofSyntax : Syntax → Value
  | `(val|True) => Value.bool true
  | `(val|False) => Value.bool false
  | `(val|$s:strLit) => Value.str <| s.isStrLit?.get!
  | `(val|$n:numLit) => Value.nat <| n.isNatLit?.get!
  | `(val|{$[$keys:key = $values],*}) => toTable keys (values.map ofSyntax)
  | `(fileCat|$[[$keys] $kvss*]*) => toTable keys <| kvss.map fun kvs => ofSyntax <| Lean.Unhygienic.run `(val|{$kvs,*})
  | stx => unreachable!
  where
    toKey : Syntax → String
      | `(keyCat|$key:ident)  => key.getId.toString
      | `(keyCat|$key:strLit) => key.isStrLit?.get!
      | _                     => unreachable!
    toTable (keys : Array Syntax) (vals : Array Value) : Value :=
      Value.table <| Array.toList <| keys.zipWith vals fun k v => (toKey k, v)

open Lean.Parser

def parse (input : String) : IO Value := do
  -- HACKHACKHACK
  let env ← importModules [{ module := `Leanpkg.Toml }] {}
  let fileParser ← compileParserDescr (parserExtension.getState env).categories file { env := env, opts := {} }
  let c := mkParserContext (mkInputContext input "") { env := env, options := {} }
  let s := mkParserState input
  let s := whitespace c s
  let s := fileParser.fn c s
  if s.hasError then
    throw <| IO.userError (s.toErrorMsg c)
  else if input.atEnd s.pos then
    ofSyntax s.stxStack.back
  else
    throw <| IO.userError ((s.mkError "end of input").toErrorMsg c)

end Toml
