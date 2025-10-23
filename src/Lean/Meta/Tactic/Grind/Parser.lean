/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Parser.Command
public section
namespace Lean.Parser.Command
/-!
Builtin parsers for `grind` related commands
-/
@[builtin_command_parser] def grindPattern := leading_parser
  Term.attrKind >> "grind_pattern " >>  ident >> darrow >> sepBy1 termParser ","

@[builtin_command_parser] def initGrindNorm := leading_parser
  "init_grind_norm " >> many ident >> "| " >> many ident

end Lean.Parser.Command
