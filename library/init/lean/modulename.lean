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

end ModuleName

end Lean
