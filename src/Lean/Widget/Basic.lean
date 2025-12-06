/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
module

prelude
public import Lean.Elab.InfoTree
public import Lean.Server.InfoUtils

public section

namespace Lean.Widget

open Elab Server

deriving instance TypeName for InfoWithCtx
deriving instance TypeName for LocalContext
deriving instance TypeName for Elab.ContextInfo
deriving instance TypeName for Elab.TermInfo

end Lean.Widget
