/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner
-/
module

prelude
public import Lean.Parser.Term

public section

namespace Lean.Elab.Command
/--
A `Scope` records the part of the `CommandElabM` state that respects scoping,
such as the data for `universe`, `open`, and `variable` declarations, the current namespace,
and currently enabled options.
The `CommandElabM` state contains a stack of scopes, and only the top `Scope`
on the stack is read from or modified. There is always at least one `Scope` on the stack,
even outside any `section` or `namespace`, and each new pushed `Scope`
starts as a modified copy of the previous top scope.
-/
structure Scope where
  /--
  The component of the `namespace` or `section` that this scope is associated to.
  For example, `section a.b.c` and `namespace a.b.c` each create three scopes with headers
  named `a`, `b`, and `c`.
  This is used for checking the `end` command. The "base scope" has `""` as its header.
  -/
  header        : String
  /--
  The current state of all set options at this point in the scope. Note that this is the
  full current set of options and does *not* simply contain the options set
  while this scope has been active.
  -/
  opts          : Options := {}
  /-- The current namespace. The top-level namespace is represented by `Name.anonymous`. -/
  currNamespace : Name := Name.anonymous
  /-- All currently `open`ed namespaces and names. -/
  openDecls     : List OpenDecl := []
  /-- The current list of names for universe level variables to use for new declarations. This is managed by the `universe` command. -/
  levelNames    : List Name := []
  /--
  The current list of binders to use for new declarations.
  This is managed by the `variable` command.
  Each binder is represented in `Syntax` form, and it is re-elaborated
  within each command that uses this information.

  This is also used by commands, such as `#check`, to create an initial local context,
  even if they do not work with binders per se.
  -/
  varDecls      : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  /--
  Globally unique internal identifiers for the `varDecls`.
  There is one identifier per variable introduced by the binders
  (recall that a binder such as `(a b c : Ty)` can produce more than one variable),
  and each identifier is the user-provided variable name with a macro scope.
  This is used by `TermElabM` in `Lean.Elab.Term.Context` to help with processing macros
  that capture these variables.
  -/
  varUIds       : Array Name := #[]
  /-- `include`d section variable names (from `varUIds`) -/
  includedVars  : List Name := []
  /-- `omit`ted section variable names (from `varUIds`) -/
  omittedVars  : List Name := []
  /--
  If true (default: false), all declarations that fail to compile
  automatically receive the `noncomputable` modifier.
  A scope with this flag set is created by `noncomputable section`.

  Recall that a new scope inherits all values from its parent scope,
  so all sections and namespaces nested within a `noncomputable` section also have this flag set.
  -/
  isNoncomputable : Bool := false
  /-- True if a `public section` is in scope. -/
  isPublic : Bool := false
  /--
  True if (applicable) declarations should automatically be marked as `meta`. No surface syntax
  currently.
  -/
  isMeta : Bool := false
  /--
  Attributes that should be applied to all matching declaration in the section. Inherited from
  parent scopes.
  -/
  attrs : List (TSyntax ``Parser.Term.attrInstance) := []
  deriving Inhabited
