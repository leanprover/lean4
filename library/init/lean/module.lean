/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.declaration
import init.data.bytearray

namespace Lean

constant ExtensionEntryPointed : PointedType := default _
def ExtensionEntry : Type := ExtensionEntryPointed.type
instance extEntryInh : Inhabited ExtensionEntry := ⟨ExtensionEntryPointed.val⟩

structure ModuleData :=
(imports    : Array Name)
(consts     : Array ConstantInfo)
(entries    : Array (Name × Array ExtensionEntry))
(serialized : ByteArray) -- legacy

end Lean
