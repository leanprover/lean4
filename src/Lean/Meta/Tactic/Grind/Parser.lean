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

namespace GrindCnstr

def isValue := leading_parser nonReservedSymbol "is_value " >> ident >> optional ";"
def isStrictValue := leading_parser nonReservedSymbol "is_strict_value " >> ident >> optional ";"
def isGround := leading_parser nonReservedSymbol "is_ground " >> ident >> optional ";"
def sizeLt := leading_parser nonReservedSymbol "size " >> ident >> " < " >> numLit >> optional ";"
def depthLt := leading_parser nonReservedSymbol "depth " >> ident >> " < " >> numLit >> optional ";"
def genLt := leading_parser nonReservedSymbol "gen" >> " < " >> numLit >> optional ";"
def maxInsts := leading_parser nonReservedSymbol "max_insts" >> " < " >> numLit >> optional ";"
def guard := leading_parser nonReservedSymbol "guard " >> checkColGe "irrelevant" >> termParser >> optional ";"
def check := leading_parser nonReservedSymbol "check " >> checkColGe "irrelevant" >> termParser >> optional ";"
def notDefEq := leading_parser atomic (ident >> " =/= ") >> checkColGe "irrelevant" >> termParser >> optional ";"
def defEq := leading_parser atomic (ident >> " =?= ") >> checkColGe "irrelevant" >> termParser >> optional ";"

end GrindCnstr

open GrindCnstr in
def grindPatternCnstr : Parser :=
  isValue <|> isStrictValue <|> isGround <|> sizeLt <|> depthLt <|> genLt <|> maxInsts
  <|> guard <|> check <|> notDefEq <|> defEq

def grindPatternCnstrs : Parser := leading_parser "where " >> many1Indent (ppLine >> grindPatternCnstr)

/-!
Builtin parsers for `grind` related commands
-/
@[builtin_command_parser] def grindPattern := leading_parser
  Term.attrKind >> "grind_pattern " >>  ident >> darrow >> sepBy1 termParser "," >> optional grindPatternCnstrs

@[builtin_command_parser] def initGrindNorm := leading_parser
  "init_grind_norm " >> many ident >> "| " >> many ident

end Lean.Parser.Command
