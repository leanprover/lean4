/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.DocString.Extension
public import Lean.DocString.Markdown
public import Lean.DocString.Links
public import Lean.Parser.Tactic.Doc
public import Lean.Parser.Term.Doc
public import Lean.ResolveName

public section

set_option linter.missingDocs true

-- This module contains the main query interface for docstrings, which assembles user-visible
-- docstrings.
-- The module `Lean.DocString.Extension` contains the underlying data.

namespace Lean
open Lean.Parser.Tactic.Doc
open Lean.Parser.Term.Doc

/--
Finds the docstring for a name, taking tactic alternate forms and documentation extensions into
account.

Use `Lean.findSimpleDocString?` to look up the raw docstring without resolving alternate forms or
including extensions.
-/
def findDocString? (env : Environment) (declName : Name) (includeBuiltin := true)
    (options : Options := {}) (currNamespace : Name := .anonymous) (openDecls : List OpenDecl := []) :
    IO (Option String) := do
  let declName := alternativeOfTactic env declName |>.getD declName
  let exts := getTacticExtensionString env declName
  let spellings := getRecommendedSpellingString env declName
  let str := (← findSimpleDocString? env declName (includeBuiltin := includeBuiltin)
      (options := options) (currNamespace := currNamespace) (openDecls := openDecls)).map
    (· ++ exts ++ spellings)
  str.mapM (rewriteManualLinks ·)

/--
Finds the docstring for a name, taking the current namespace and open declarations from the ambient
monad. Tactic alternate forms and documentation extensions are taken into account.

Docstrings are rendered with the default options.
-/
def findMarkdownDocString? [Monad m] [MonadEnv m] [MonadResolveName m] [MonadLiftT IO m]
    (declName : Name) (includeBuiltin := true) : m (Option String) := do
  findDocString? (← getEnv) declName (includeBuiltin := includeBuiltin)
    (currNamespace := ← getCurrNamespace) (openDecls := ← getOpenDecls)
