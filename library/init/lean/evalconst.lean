/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.io
import init.data.array
import init.lean.name

namespace Lean

/- We mark this primitive as `unsafe` because it assumes the table is
   being accessed by a single thread. -/
@[extern 2 "lean_modify_constant_table"]
unsafe constant modifyConstTable (f : Array (Name × NonScalar) → Array (Name × NonScalar)) : IO Unit := default _

/- We mark this primitive as `unsafe` because it assumes the table is
   being accessed by a single thread. -/
@[extern 1 "lean_get_constant_table"]
unsafe constant getConstTable : IO (Array (Name × NonScalar)) := default _

/- We mark this primitive as `unsafe` because it assumes the table is
   being accessed by a single thread. We meet this requirement by invoking
   it after we have initialized all modules.
   See `src/init/init.cpp` -/
@[export lean.sort_const_table_core]
unsafe def sortConstTable : IO Unit :=
modifyConstTable (fun cs => cs.qsort (fun e₁ e₂ => Name.quickLt e₁.1 e₂.1))

/- We make this primitive as `unsafe` because it uses `unsafeCast`, and
   the program may crash if the type provided by the user is incorrect.
   It also assumes there are no threads trying to update the table concurrently. -/
unsafe def evalConst (α : Type) [Inhabited α] (c : Name) : IO α :=
do cs ← getConstTable;
   match cs.binSearch (c, default _) (fun e₁ e₂ => Name.quickLt e₁.1 e₂.1) with
   | some (_, v) := pure (unsafeCast v)
   | none        := throw (IO.userError ("unknow constant '" ++ toString c ++ "'"))

end Lean
