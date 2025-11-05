/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Lean.LibrarySuggestions.SineQuaNon

/-!
# Default library suggestions engine

This module sets the default library suggestions engine to Sine Qua Non.
Any module that imports this (directly or transitively) will have library suggestions enabled.
-/

namespace Lean.LibrarySuggestions

open Lean LibrarySuggestions SineQuaNon

-- Set the default library suggestions engine to Sine Qua Non
set_library_suggestions Lean.LibrarySuggestions.sineQuaNonSelector

end Lean.LibrarySuggestions
