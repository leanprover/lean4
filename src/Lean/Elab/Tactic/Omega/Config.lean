/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic.Omega

/--
Allow elaboration of `OmegaConfig` arguments to tactics.
-/
declare_config_elab elabOmegaConfig Lean.Meta.Omega.OmegaConfig

end Lean.Elab.Tactic.Omega
