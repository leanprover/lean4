/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.ToString
public import Lean.Fmt.Core.Basic
public import Init.Data.Format.Syntax
public import Lean.Fmt.Core.Formatter

namespace Lean.Fmt

public inductive InternalError where
  | partialFormatter
  | cancelled
deriving Inhabited

public inductive InputError where
  | parseError (msg : String := s!"Cannot format file with parse errors.")
  | earlyTerminationCommand
    (stx : Syntax)
    (msg : String := s!"Cannot format file with early termination commands (e.g. `#exit`).")
  | importError (stx : Syntax) (msg : String := s!"Cannot format file with import errors.")
deriving Inhabited

public instance : ToString InputError where
  toString
    | .parseError (msg := msg) ..
    | .earlyTerminationCommand (msg := msg) ..
    | .importError (msg := msg) .. =>
      msg

public def InputError.ref? : InputError → Option Syntax
  | .parseError .. => none
  | .earlyTerminationCommand (stx := stx) .. | .importError (stx := stx) .. => stx

public inductive ElaborationError where
  | malformedInputSyntax
    (stx : Syntax) (reason : String)
    (msg : String := s!"Input syntax to the formatter is malformed: {reason}.")
  | ambiguousChoiceNode
    (stx : Syntax)
    (msg : String :=
      s!"A choice node was not disambiguated by the elaborator:\
        \n{toString stx}")
deriving Inhabited

public instance : ToString ElaborationError where
  toString
    | .malformedInputSyntax (msg := msg) .. | .ambiguousChoiceNode (msg := msg) .. => msg

public def ElaborationError.ref : ElaborationError → Syntax
  | .malformedInputSyntax (stx := stx) .. | .ambiguousChoiceNode (stx := stx) .. => stx

public inductive FmtError where
  | formattingFailure
    (stx : Syntax)
    (msg : String :=
      "Formatting of the document produced by the current set of `[fmt]` \
        annotations has failed. This issue is commonly caused by `Doc.failure` or attempting to \
        flatten a document with hard newlines.")
  | reparseFailure
    (stx : Syntax)
    (msg : String :=
      "The parser cannot parse the rendering of this command again. This issue \
        is commonly caused by the formatter stripping semicolons that were used to prevent \
        accidentally parsing too far.")
  | taintedFormatting
    (stx : Syntax)
    (msg : String :=
      "Formatting of the document produced by the current set of `[fmt]` \
        annotations contains a part that always exceeds the maximum column width within which \
        the formatter attempts to find optimal configurations (200). This issue is commonly caused \
        by syntax in the document that is not formatted (e.g. because there is no `[fmt]` \
        attribute \
        for it) and is also very long in the input document. To format the parts of the document \
        that are formatteable, either break up the document that is not formatted or write a \
        formatter for it.")
deriving Inhabited

public instance : ToString FmtError where
  toString
    | .formattingFailure (msg := msg) ..
    | .reparseFailure (msg := msg) ..
    | .taintedFormatting (msg := msg) .. =>
      msg

public def FmtError.ref : FmtError → Syntax
  | .formattingFailure (stx := stx) ..
  | .reparseFailure (stx := stx) ..
  | .taintedFormatting (stx := stx) .. =>
    stx

public inductive Error where
  | internal (err : InternalError)
  | input (err : InputError)
  | elaboration (err : ElaborationError)
  | fmt (err : FmtError)
deriving Inhabited

public def Error.partialFormatter : Error := .internal .partialFormatter

public instance : ToString Error where
  toString
    | .internal _ => "Internal error."
    | .input err | .elaboration err | .fmt err => toString err

public def Error.ref? : Error → Option Syntax
  | .internal _ => none
  | .input err => err.ref?
  | .elaboration err | .fmt err => err.ref

public def Error.ofFormattingError (stx : Syntax) : FormattingError → Error
  | .failure => .fmt <| .formattingFailure stx
  | .tainted => .fmt <| .taintedFormatting stx
