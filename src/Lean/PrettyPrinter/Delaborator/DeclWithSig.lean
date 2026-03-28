/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura, Gabriel Ebner, Mario Carneiro
-/
module

prelude
public import Lean.Parser.Types
import Lean.Parser.Command

namespace Lean.PrettyPrinter.Delaborator

open Parser Command Term

@[run_builtin_parser_attribute_hooks]
-- use `termParser` instead of `declId` so we can reuse `delabConst`
public def declSigWithId : Parser := leading_parser termParser maxPrec >> declSig
