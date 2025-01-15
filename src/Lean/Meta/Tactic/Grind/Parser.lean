/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Parser.Command

namespace Lean.Parser.Command
/-!
Builtin parsers for `grind` related commands
-/
@[builtin_command_parser] def grindPattern := leading_parser
  "grind_pattern " >>  ident >> darrow >> sepBy1 termParser ","
end Lean.Parser.Command
