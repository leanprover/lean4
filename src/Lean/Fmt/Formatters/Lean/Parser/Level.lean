/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Level
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Level.paren]
public def fmtLevelParen : Fmt := fun
  | `(Parser.Level.paren| (%$lbTk $level )%$rbTk ) => do
    let lbTk ← fmt lbTk
    let level ← fmt level
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk level rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Level.max]
public def fmtLevelMax : Fmt := fun
  | `(Parser.Level.max| max%$maxTk $levels:level*) => do fmtAppLike <| #[maxTk] ++ levels
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Level.imax]
public def fmtLevelIMax : Fmt := fun
  | `(Parser.Level.imax| imax%$imaxTk $levels:level*) => do fmtAppLike <| #[imaxTk] ++ levels
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Level.hole]
public def fmtLevelHole : Fmt := fmtAtomic

@[builtin_infix_fmt Lean.Parser.Level.addLit]
public def fmtAddLit : Lean.Fmt.InfixOperation := { sparse := false }
