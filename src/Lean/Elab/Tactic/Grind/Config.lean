/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.CoreM
meta import Lean.Elab.Tactic.ConfigSetter
public section
namespace Lean.Elab.Tactic.Grind

/-- Sets a field of the `grind` configuration object. -/
declare_config_getter setConfigField Grind.Config

end Lean.Elab.Tactic.Grind
