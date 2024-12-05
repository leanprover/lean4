/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Data.ToString.Basic

namespace Lake

/-- Lake configuration language identifier. -/
inductive ConfigLang
| lean | toml
deriving Repr, DecidableEq

/-- Lake's default configuration language. -/
abbrev ConfigLang.default : ConfigLang := .toml

instance : Inhabited ConfigLang := ⟨.default⟩

def ConfigLang.ofString? : String → Option ConfigLang
| "lean" => some .lean
| "toml" => some .toml
| _ => none

def ConfigLang.fileExtension : ConfigLang → String
| .lean => "lean"
| .toml => "toml"

instance : ToString ConfigLang := ⟨ConfigLang.fileExtension⟩
