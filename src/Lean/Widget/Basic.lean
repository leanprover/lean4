/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
prelude
import Lean.Elab.InfoTree
import Lean.Message
import Lean.Server.Rpc.Basic
import Lean.Server.InfoUtils
import Lean.Widget.Types

namespace Lean.Widget

open Elab Server

deriving instance TypeName for InfoWithCtx
deriving instance TypeName for LocalContext
deriving instance TypeName for Elab.ContextInfo
deriving instance TypeName for Elab.TermInfo

end Lean.Widget
