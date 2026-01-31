/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Environment
import all Lean.Environment

namespace Lean

public unsafe def bundleOLeans (imp : Import) (dest : System.FilePath) : IO Unit := do
  let (_, s) ← importModulesCore #[imp] .private |>.run
  let modules := s.moduleNames.filterMap (s.moduleNameMap[·]?)
  -- erase region information
  let modules := modules.map fun m => { m with
    parts := m.parts.map fun (data, (_ : Option CompactedRegion)) => (data, none)
    irData? := m.irData?.map fun (data, (_ : Option CompactedRegion)) => (data, none) }
  -- TODO: generalize `saveModuleData`
  saveModuleData (α := OLeanBundle) dest (imp.module ++ `bundle) (unsafeCast modules)
