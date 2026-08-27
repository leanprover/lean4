/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public meta import Lean.LibrarySuggestions.SineQuaNon

/-!
# Default library suggestions engine

This module sets the default library suggestions engine to "Sine Qua Non",
along with the theorems from the current file.
.
Any module that imports this (directly or transitively) will have library suggestions enabled.
-/

namespace Lean.LibrarySuggestions

-- Set the default library suggestions engine to
-- a combination of "Sine Qua Non" and the theorems from the current file.
-- For now we just intersperse the results, but in future we should re-rank them.
-- Note: We filter out grind-annotated modules from sineQuaNonSelector when caller is "grind".
set_library_suggestions open Lean.LibrarySuggestions in sineQuaNonSelector.filterGrindAnnotated.intersperse currentFile

end Lean.LibrarySuggestions
