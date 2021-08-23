/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data
import Lean.Compiler
import Lean.Environment
import Lean.Modifiers
import Lean.ProjFns
import Lean.Runtime
import Lean.ResolveName
import Lean.Attributes
import Lean.Parser
import Lean.ReducibilityAttrs
import Lean.Elab
import Lean.Class
import Lean.LocalContext
import Lean.MetavarContext
import Lean.AuxRecursor
import Lean.Meta
import Lean.Util
import Lean.Eval
import Lean.Structure
import Lean.PrettyPrinter
import Lean.CoreM
import Lean.InternalExceptionId
import Lean.Server
import Lean.ScopedEnvExtension
import Lean.DocString
import Lean.DeclarationRange
import Lean.LazyInitExtension
import Lean.Widget
