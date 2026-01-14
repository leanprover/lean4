/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.ToString.Basic

namespace Lake

/-- Lake configuration language identifier. -/
public inductive ConfigLang
| lean | toml
deriving Repr, DecidableEq

/-- Lake's default configuration language. -/
public abbrev ConfigLang.default : ConfigLang := .toml

public instance : Inhabited ConfigLang := ⟨.default⟩

public def ConfigLang.ofString? : String → Option ConfigLang
| "lean" => some .lean
| "toml" => some .toml
| _ => none

public def ConfigLang.fileExtension : ConfigLang → String
| .lean => "lean"
| .toml => "toml"

public instance : ToString ConfigLang := ⟨ConfigLang.fileExtension⟩
