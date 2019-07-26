/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name

namespace Lean

inductive ModuleName
| explicit (name : Name)
| relative (rel : Nat) (name : Name)

namespace ModuleName

instance : Inhabited ModuleName := ⟨ModuleName.explicit Name.anonymous⟩

instance : HasCoe Name ModuleName := ⟨explicit⟩

def quickLt : ModuleName → ModuleName → Bool
| (explicit n₁)    (explicit n₂)    := Name.quickLt n₁ n₂
| (explicit _)     (relative _ _)   := true
| (relative _ _)   (explicit _)     := false
| (relative r₁ n₁) (relative r₂ n₂) := r₁ < r₂ || (r₁ == r₂ && Name.quickLt n₁ n₂)

instance : HasToString ModuleName :=
⟨fun n => match n with
 | explicit n   => toString n
 | relative r n => "".pushn '.' r ++ toString n⟩

end ModuleName

end Lean
