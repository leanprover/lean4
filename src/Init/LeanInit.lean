/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich
-/
prelude
import Init.Data.Option.BasicAux
import Init.Data.String.Basic
import Init.Data.Array.Basic
import Init.Data.UInt
import Init.Data.Hashable
import Init.Control.Reader
import Init.Control.EState
import Init.Control.StateRef
import Init.Control.Option

namespace Lean
/-
Basic Lean types used to implement builtin commands and extensions.
Note that this file is part of the Lean `Init` library instead of
`Lean` actual implementation.
The idea is to allow users to implement simple parsers, macros and tactics
without importing the whole `Lean` module.
It also allow us to use extensions to develop the `Init` library.
-/

/- Valid identifier names -/
def isGreek (c : Char) : Bool :=
  0x391 ≤ c.val && c.val ≤ 0x3dd

def isLetterLike (c : Char) : Bool :=
  (0x3b1  ≤ c.val && c.val ≤ 0x3c9 && c.val ≠ 0x3bb) ||                  -- Lower greek, but lambda
  (0x391  ≤ c.val && c.val ≤ 0x3A9 && c.val ≠ 0x3A0 && c.val ≠ 0x3A3) || -- Upper greek, but Pi and Sigma
  (0x3ca  ≤ c.val && c.val ≤ 0x3fb) ||                                   -- Coptic letters
  (0x1f00 ≤ c.val && c.val ≤ 0x1ffe) ||                                  -- Polytonic Greek Extended Character Set
  (0x2100 ≤ c.val && c.val ≤ 0x214f) ||                                  -- Letter like block
  (0x1d49c ≤ c.val && c.val ≤ 0x1d59f)                                   -- Latin letters, Script, Double-struck, Fractur

def isSubScriptAlnum (c : Char) : Bool :=
  (0x2080 ≤ c.val && c.val ≤ 0x2089) || -- numeric subscripts
  (0x2090 ≤ c.val && c.val ≤ 0x209c) ||
  (0x1d62 ≤ c.val && c.val ≤ 0x1d6a)

def isIdFirst (c : Char) : Bool :=
  c.isAlpha || c = '_' || isLetterLike c

def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c = '_' || c = '\'' || c == '!' || c == '?' || isLetterLike c || isSubScriptAlnum c

def idBeginEscape := '«'
def idEndEscape   := '»'
def isIdBeginEscape (c : Char) : Bool := c = idBeginEscape
def isIdEndEscape (c : Char) : Bool := c = idEndEscape

/- Hierarchical names -/
inductive Name
  | anonymous : Name
  | str : Name → String → USize → Name
  | num : Name → Nat → USize → Name

instance : Inhabited Name := ⟨Name.anonymous⟩

protected def Name.hash : Name → USize
  | Name.anonymous => 1723
  | Name.str p s h => h
  | Name.num p v h => h

instance : Hashable Name := ⟨Name.hash⟩

@[export lean_name_mk_string]
def mkNameStr (p : Name) (s : String) : Name :=
  Name.str p s $ mixHash (hash p) (hash s)

@[export lean_name_mk_numeral]
def mkNameNum (p : Name) (v : Nat) : Name :=
  Name.num p v $ mixHash (hash p) (hash v)

def mkNameSimple (s : String) : Name :=
  mkNameStr Name.anonymous s

namespace Name

@[extern "lean_name_eq"]
protected def beq : (@& Name) → (@& Name) → Bool
  | anonymous,   anonymous   => true
  | str p₁ s₁ _, str p₂ s₂ _ => s₁ == s₂ && Name.beq p₁ p₂
  | num p₁ n₁ _, num p₂ n₂ _ => n₁ == n₂ && Name.beq p₁ p₂
  | _,           _           => false

instance : BEq Name := ⟨Name.beq⟩

def toStringWithSep (sep : String) : Name → String
  | anonymous         => "[anonymous]"
  | str anonymous s _ => s
  | num anonymous v _ => toString v
  | str n s _         => toStringWithSep sep n ++ sep ++ s
  | num n v _         => toStringWithSep sep n ++ sep ++ repr v

protected def toString : Name → String :=
toStringWithSep "."

instance : ToString Name := ⟨Name.toString⟩

protected def append : Name → Name → Name
  | n, anonymous => n
  | n, str p s _ => mkNameStr (Name.append n p) s
  | n, num p d _ => mkNameNum (Name.append n p) d

instance : Append Name := ⟨Name.append⟩

def capitalize : Name → Name
  | Name.str p s _ => mkNameStr p s.capitalize
  | n              => n

def appendAfter : Name → String → Name
  | str p s _, suffix => mkNameStr p (s ++ suffix)
  | n,         suffix => mkNameStr n suffix

def appendIndexAfter : Name → Nat → Name
  | str p s _, idx => mkNameStr p (s ++ "_" ++ toString idx)
  | n,         idx => mkNameStr n ("_" ++ toString idx)

def appendBefore : Name → String → Name
  | anonymous, pre => mkNameStr anonymous pre
  | str p s _, pre => mkNameStr p (pre ++ s)
  | num p n _, pre => mkNameNum (mkNameStr p pre) n

end Name

structure NameGenerator :=
  (namePrefix : Name := `_uniq)
  (idx        : Nat  := 1)

namespace NameGenerator

instance : Inhabited NameGenerator := ⟨{}⟩

@[inline] def curr (g : NameGenerator) : Name :=
  mkNameNum g.namePrefix g.idx

@[inline] def next (g : NameGenerator) : NameGenerator :=
  { g with idx := g.idx + 1 }

@[inline] def mkChild (g : NameGenerator) : NameGenerator × NameGenerator :=
  ({ namePrefix := mkNameNum g.namePrefix g.idx, idx := 1 },
   { g with idx := g.idx + 1 })

end NameGenerator

class MonadNameGenerator (m : Type → Type) :=
  (getNGen : m NameGenerator)
  (setNGen : NameGenerator → m Unit)

export MonadNameGenerator (getNGen setNGen)

def mkFreshId {m : Type → Type} [Monad m] [MonadNameGenerator m] : m Name := do
  let ngen ← getNGen
  let r := ngen.curr
  setNGen ngen.next
  pure r

instance monadNameGeneratorLift (m n : Type → Type) [MonadNameGenerator m] [MonadLift m n] : MonadNameGenerator n := {
  getNGen := liftM (getNGen : m _),
  setNGen := fun ngen => liftM (setNGen ngen : m _)
}

/-
  Small DSL for describing parsers. We implement an interpreter for it
  at `Parser.lean` -/
inductive ParserDescr
  | andthen           : ParserDescr → ParserDescr → ParserDescr
  | orelse            : ParserDescr → ParserDescr → ParserDescr
  | optional          : ParserDescr → ParserDescr
  | lookahead         : ParserDescr → ParserDescr
  | «try»             : ParserDescr → ParserDescr
  | many              : ParserDescr → ParserDescr
  | many1             : ParserDescr → ParserDescr
  | sepBy             : ParserDescr → ParserDescr → ParserDescr
  | sepBy1            : ParserDescr → ParserDescr → ParserDescr
  | node              : Name → Nat → ParserDescr → ParserDescr
  | trailingNode      : Name → Nat → ParserDescr → ParserDescr
  | symbol            : String → ParserDescr
  | nonReservedSymbol : String → Bool → ParserDescr
  | noWs              : ParserDescr
  | numLit            : ParserDescr
  | strLit            : ParserDescr
  | charLit           : ParserDescr
  | nameLit           : ParserDescr
  | interpolatedStr   : ParserDescr → ParserDescr -- interpolated string
  | ident             : ParserDescr
  | cat               : Name → Nat → ParserDescr
  | parser            : Name → ParserDescr
  | notFollowedBy     : ParserDescr → ParserDescr

instance : Inhabited ParserDescr := ⟨ParserDescr.symbol ""⟩
abbrev TrailingParserDescr := ParserDescr

/- Syntax -/

/--
  Source information of syntax atoms. All information is generally set for unquoted syntax and unset for syntax in
  syntax quotations, but syntax transformations might want to invalidate only one side to make the pretty printer
  reformat it. In the special case of the delaborator, we also use purely synthetic position information without
  whitespace information. -/
structure SourceInfo :=
  /- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
     it is not at all clear what the preceding token was, especially with backtracking. -/
  (leading  : Option Substring  := none)
  (pos      : Option String.Pos := none)
  (trailing : Option Substring  := none)

instance : Inhabited SourceInfo := ⟨{}⟩

abbrev SyntaxNodeKind := Name

/- Syntax AST -/

inductive Syntax
  | missing : Syntax
  | node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom   (info : SourceInfo) (val : String) : Syntax
  | ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Name × List String)) : Syntax

instance : Inhabited Syntax := ⟨Syntax.missing⟩

/- Builtin kinds -/
def choiceKind : SyntaxNodeKind := `choice
def nullKind : SyntaxNodeKind := `null
def identKind : SyntaxNodeKind := `ident
def strLitKind : SyntaxNodeKind := `strLit
def charLitKind : SyntaxNodeKind := `charLit
def numLitKind : SyntaxNodeKind := `numLit
def nameLitKind : SyntaxNodeKind := `nameLit
def fieldIdxKind : SyntaxNodeKind := `fieldIdx
def interpolatedStrLitKind : SyntaxNodeKind := `interpolatedStrLitKind
def interpolatedStrKind : SyntaxNodeKind := `interpolatedStrKind

namespace Syntax

def getKind (stx : Syntax) : SyntaxNodeKind :=
  match stx with
  | Syntax.node k args   => k
  -- We use these "pseudo kinds" for antiquotation kinds.
  -- For example, an antiquotation `$id:ident` (using Lean.Parser.Term.ident)
  -- is compiled to ``if stx.isOfKind `ident ...``
  | Syntax.missing       => `missing
  | Syntax.atom _ v      => mkNameSimple v
  | Syntax.ident _ _ _ _ => identKind

def setKind (stx : Syntax) (k : SyntaxNodeKind) : Syntax :=
  match stx with
  | Syntax.node _ args => Syntax.node k args
  | _                  => stx

def isOfKind (stx : Syntax) (k : SyntaxNodeKind) : Bool :=
  stx.getKind == k

def getArg (stx : Syntax) (i : Nat) : Syntax :=
  match stx with
  | Syntax.node _ args => args.get! i
  | _                  => Syntax.missing -- panic! "Syntax.getArg: not a node"

-- Add `stx[i]` as sugar for `stx.getArg i`
@[inline] def getOp (self : Syntax) (idx : Nat) : Syntax :=
  self.getArg idx

def getArgs (stx : Syntax) : Array Syntax :=
  match stx with
  | Syntax.node _ args => args
  | _                  => #[] -- panic! "Syntax.getArgs: not a node"

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo : Syntax → Option SourceInfo
  | atom info _      => info
  | ident info _ _ _ => info
  | node _ args      => args.findSome? getHeadInfo
  | _                => none

end Syntax

/- Syntax objects for a Lean module. -/
structure Module :=
  (header   : Syntax)
  (commands : Array Syntax)

/-
Runtime support for making quotation terms auto-hygienic, by mangling identifiers
introduced by them with a "macro scope" supplied by the context. Details to appear in a
paper soon.
-/

abbrev MacroScope := Nat
/-- Macro scope used internally. It is not available for our frontend. -/
def reservedMacroScope := 0
/-- First macro scope available for our frontend -/
def firstFrontendMacroScope := reservedMacroScope + 1

/-- A monad that supports syntax quotations. Syntax quotations (in term
    position) are monadic values that when executed retrieve the current "macro
    scope" from the monad and apply it to every identifier they introduce
    (independent of whether this identifier turns out to be a reference to an
    existing declaration, or an actually fresh binding during further
    elaboration). -/
class MonadQuotation (m : Type → Type) :=
  -- Get the fresh scope of the current macro invocation
  (getCurrMacroScope : m MacroScope)
  (getMainModule     : m Name)
  /- Execute action in a new macro invocation context. This transformer should be
     used at all places that morally qualify as the beginning of a "macro call",
     e.g. `elabCommand` and `elabTerm` in the case of the elaborator. However, it
     can also be used internally inside a "macro" if identifiers introduced by
     e.g. different recursive calls should be independent and not collide. While
     returning an intermediate syntax tree that will recursively be expanded by
     the elaborator can be used for the same effect, doing direct recursion inside
     the macro guarded by this transformer is often easier because one is not
     restricted to passing a single syntax tree. Modelling this helper as a
     transformer and not just a monadic action ensures that the current macro
     scope before the recursive call is restored after it, as expected. -/
  (withFreshMacroScope {α : Type} : m α → m α)

export MonadQuotation (getCurrMacroScope getMainModule withFreshMacroScope)

/-
We represent a name with macro scopes as
```
<actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
```
Example: suppose the module name is `Init.Data.List.Basic`, and name is `foo.bla`, and macroscopes [2, 5]
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```

We may have to combine scopes from different files/modules.
The main modules being processed is always the right most one.
This situation may happen when we execute a macro generated in
an imported file in the current file.
```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```

The delimiter `_hyg` is used just to improve the `hasMacroScopes` performance.
-/

def Name.hasMacroScopes : Name → Bool
  | str _ s _   => s == "_hyg"
  | num p _   _ => hasMacroScopes p
  | _           => false

private def eraseMacroScopesAux : Name → Name
  | Name.str p s _   => if s == "_@" then p else eraseMacroScopesAux p
  | Name.num p _ _   => eraseMacroScopesAux p
  | Name.anonymous   => unreachable!

@[export lean_erase_macro_scopes]
def Name.eraseMacroScopes (n : Name) : Name :=
  if n.hasMacroScopes then eraseMacroScopesAux n else n

private def simpMacroScopesAux : Name → Name
  | Name.num p i _ => mkNameNum (simpMacroScopesAux p) i
  | n              => eraseMacroScopesAux n

/- Helper function we use to create binder names that do not need to be unique. -/
@[export lean_simp_macro_scopes]
def Name.simpMacroScopes (n : Name) : Name :=
  if n.hasMacroScopes then simpMacroScopesAux n else n

structure MacroScopesView :=
  (name       : Name)
  (imported   : Name)
  (mainModule : Name)
  (scopes     : List MacroScope)

instance : Inhabited MacroScopesView := ⟨⟨arbitrary _, arbitrary _, arbitrary _, arbitrary _⟩⟩

def MacroScopesView.review (view : MacroScopesView) : Name :=
  if view.scopes.isEmpty then
    view.name
  else
    let base := (mkNameStr ((mkNameStr view.name "_@") ++ view.imported ++ view.mainModule) "_hyg")
    view.scopes.foldl mkNameNum base

private def assembleParts : List Name → Name → Name
  | [],                     acc => acc
  | (Name.str _ s _) :: ps, acc => assembleParts ps (mkNameStr acc s)
  | (Name.num _ n _) :: ps, acc => assembleParts ps (mkNameNum acc n)
  | _,                      _   => unreachable!

private def extractImported (scps : List MacroScope) (mainModule : Name) : Name → List Name → MacroScopesView
  | n@(Name.str p str _), parts =>
    if str == "_@" then
      { name := p, mainModule := mainModule, imported := assembleParts parts Name.anonymous, scopes := scps }
    else
      extractImported scps mainModule p (n :: parts)
  | n@(Name.num p str _), parts => extractImported scps mainModule p (n :: parts)
  | _,                    _     => unreachable!

private def extractMainModule (scps : List MacroScope) : Name → List Name → MacroScopesView
  | n@(Name.str p str _), parts =>
    if str == "_@" then
      { name := p, mainModule := assembleParts parts Name.anonymous, imported := Name.anonymous, scopes := scps }
    else
      extractMainModule scps p (n :: parts)
  | n@(Name.num p num _), acc => extractImported scps (assembleParts acc Name.anonymous) n []
  | _,                    _   => unreachable!

private def extractMacroScopesAux : Name → List MacroScope → MacroScopesView
  | Name.num p scp _, acc => extractMacroScopesAux p (scp::acc)
  | Name.str p str _, acc => extractMainModule acc p [] -- str must be "_hyg"
  | _,                _   => unreachable!

/--
  Revert all `addMacroScope` calls. `v = extractMacroScopes n → n = v.review`.
  This operation is useful for analyzing/transforming the original identifiers, then adding back
  the scopes (via `MacroScopesView.review`). -/
def extractMacroScopes (n : Name) : MacroScopesView :=
  if n.hasMacroScopes then
    extractMacroScopesAux n []
  else
    { name := n, scopes := [], imported := Name.anonymous, mainModule := Name.anonymous }

def addMacroScope (mainModule : Name) (n : Name) (scp : MacroScope) : Name :=
  if n.hasMacroScopes then
    let view := extractMacroScopes n
    if view.mainModule == mainModule then
      mkNameNum n scp
    else
      { view with imported := view.scopes.foldl mkNameNum (view.imported ++ view.mainModule), mainModule := mainModule, scopes := [scp] }.review
  else
    mkNameNum (mkNameStr (mkNameStr n "_@" ++ mainModule) "_hyg") scp

@[inline] def MonadQuotation.addMacroScope {m : Type → Type} [MonadQuotation m] [Monad m] (n : Name) : m Name := do
  let mainModule ← getMainModule
  let scp ← getCurrMacroScope
  pure $ Lean.addMacroScope mainModule n scp

def defaultMaxRecDepth := 512

def maxRecDepthErrorMessage : String :=
  "maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)"

namespace Macro

/- References -/
constant MacroEnvPointed : PointedType.{0}
def MacroEnv : Type := MacroEnvPointed.type
instance : Inhabited MacroEnv := ⟨MacroEnvPointed.val⟩

structure Context :=
  (macroEnv       : MacroEnv)
  (mainModule     : Name)
  (currMacroScope : MacroScope)
  (currRecDepth   : Nat := 0)
  (maxRecDepth    : Nat := defaultMaxRecDepth)

inductive Exception
  | error             : Syntax → String → Exception
  | unsupportedSyntax : Exception

end Macro

abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception MacroScope)

abbrev Macro := Syntax → MacroM Syntax

namespace Macro

def addMacroScope (n : Name) : MacroM Name := do
  let ctx ← read
  pure $ Lean.addMacroScope ctx.mainModule n ctx.currMacroScope

def throwUnsupported {α} : MacroM α :=
  throw Exception.unsupportedSyntax

def throwError {α} (ref : Syntax) (msg : String) : MacroM α :=
  throw $ Exception.error ref msg

@[inline] protected def withFreshMacroScope {α} (x : MacroM α) : MacroM α := do
  let fresh ← modifyGet (fun s => (s, s+1))
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

@[inline] def withIncRecDepth {α} (ref : Syntax) (x : MacroM α) : MacroM α := do
  let ctx ← read
  if ctx.currRecDepth == ctx.maxRecDepth then throw $ Exception.error ref maxRecDepthErrorMessage
  withReader (fun ctx => { ctx with currRecDepth := ctx.currRecDepth + 1 }) x

instance : MonadQuotation MacroM := {
  getCurrMacroScope   := fun ctx => pure ctx.currMacroScope,
  getMainModule       := fun ctx => pure ctx.mainModule,
  withFreshMacroScope := Macro.withFreshMacroScope
}

instance {m n : Type → Type} [MonadQuotation m] [MonadLift m n] [MonadFunctorT m n] : MonadQuotation n := {
  getCurrMacroScope   := liftM (m := m) getCurrMacroScope,
  getMainModule       := liftM (m := m) getMainModule,
  withFreshMacroScope := monadMap (m := m) withFreshMacroScope
}

unsafe def mkMacroEnvImp (expandMacro? : Syntax → MacroM (Option Syntax)) : MacroEnv :=
  unsafeCast expandMacro?

@[implementedBy mkMacroEnvImp]
constant mkMacroEnv (expandMacro? : Syntax → MacroM (Option Syntax)) : MacroEnv

def expandMacroNotAvailable? (stx : Syntax) : MacroM (Option Syntax) :=
  throwError stx "expandMacro has not been set"

def mkMacroEnvSimple : MacroEnv :=
  mkMacroEnv expandMacroNotAvailable?

unsafe def expandMacro?Imp (stx : Syntax) : MacroM (Option Syntax) := do
  let ctx ← read
  let f : Syntax → MacroM (Option Syntax) := unsafeCast (ctx.macroEnv)
  f stx

/-- `expandMacro? stx` return `some stxNew` if `stx` is a macro, and `stxNew` is its expansion. -/
@[implementedBy expandMacro?Imp] constant expandMacro? : Syntax → MacroM (Option Syntax)

end Macro

export Macro (expandMacro?)

/-- Expand all macros in the given syntax -/
partial def expandMacros : Syntax → MacroM Syntax
  | stx@(Syntax.node k args) => do
    match (← expandMacro? stx) with
    | some stxNew => expandMacros stxNew
    | none        => do
      let args ← Macro.withIncRecDepth stx $ args.mapM expandMacros
      pure $ Syntax.node k args
  | stx => pure stx

/- Helper functions for processing Syntax programmatically -/

/--
  Create an identifier using `SourceInfo` from `src`.
  To refer to a specific constant, use `mkCIdentFrom` instead. -/
def mkIdentFrom (src : Syntax) (val : Name) : Syntax :=
  let info := src.getHeadInfo.getD {}
  Syntax.ident info (toString val).toSubstring val []

/--
  Create an identifier referring to a constant `c` using `SourceInfo` from `src`.
  This variant of `mkIdentFrom` makes sure that the identifier cannot accidentally
  be captured. -/
def mkCIdentFrom (src : Syntax) (c : Name) : Syntax :=
  let info := src.getHeadInfo.getD {}
  -- Remark: We use the reserved macro scope to make sure there are no accidental collision with our frontend
  let id   := addMacroScope `_internal c reservedMacroScope
  Syntax.ident info (toString id).toSubstring id [(c, [])]

def mkCIdent (c : Name) : Syntax :=
  mkCIdentFrom Syntax.missing c

def mkAtomFrom (src : Syntax) (val : String) : Syntax :=
  let info := src.getHeadInfo.getD {}
  Syntax.atom info val

def Syntax.identToAtom (stx : Syntax) : Syntax :=
  match stx with
  | Syntax.ident info _ val _ => Syntax.atom info (toString val.eraseMacroScopes)
  | _                         => stx

@[export lean_mk_syntax_ident]
def mkIdent (val : Name) : Syntax :=
  Syntax.ident {} (toString val).toSubstring val []

@[inline] def mkNullNode (args : Array Syntax := #[]) : Syntax :=
  Syntax.node nullKind args

def mkSepArray (as : Array Syntax) (sep : Syntax) : Array Syntax := do
  let i := 0
  let r := #[]
  for a in as do
    if i > 0 then
      r := r.push sep $.push a
    else
      r := r.push a
    i := i + 1
  return r

def mkSepStx (a : Array Syntax) (sep : Syntax) : Syntax :=
  mkNullNode $ mkSepArray a sep

def mkOptionalNode (arg : Option Syntax) : Syntax :=
  match arg with
  | some arg => Syntax.node nullKind #[arg]
  | none     => Syntax.node nullKind #[]

/-- Create syntax representing a Lean term application -/
def mkAppStx (fn : Syntax) (args : Array Syntax) : Syntax :=
  Syntax.node `Lean.Parser.Term.app #[fn, mkNullNode args]

def mkHole (ref : Syntax) : Syntax :=
  Syntax.node `Lean.Parser.Term.hole #[mkAtomFrom ref "_"]

def mkCAppStx (fn : Name) (args : Array Syntax) : Syntax :=
  mkAppStx (mkCIdent fn) args

def mkStxLit (kind : SyntaxNodeKind) (val : String) (info : SourceInfo := {}) : Syntax :=
  let atom : Syntax := Syntax.atom info val
  Syntax.node kind #[atom]

def mkStxStrLit (val : String) (info : SourceInfo := {}) : Syntax :=
  mkStxLit strLitKind (repr val) info

def mkStxNumLit (val : String) (info : SourceInfo := {}) : Syntax :=
  mkStxLit numLitKind val info

namespace Syntax

/- Recall that we don't have special Syntax constructors for storing numeric and string atoms.
   The idea is to have an extensible approach where embedded DSLs may have new kind of atoms and/or
   different ways of representing them. So, our atoms contain just the parsed string.
   The main Lean parser uses the kind `numLitKind` for storing natural numbers that can be encoded
   in binary, octal, decimal and hexadecimal format. `isNatLit` implements a "decoder"
   for Syntax objects representing these numerals. -/

private partial def decodeBinLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else
    let c := s.get i
    if c == '0' then decodeBinLitAux s (s.next i) (2*val)
    else if c == '1' then decodeBinLitAux s (s.next i) (2*val + 1)
    else none

private partial def decodeOctalLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else
    let c := s.get i
    if '0' ≤ c && c ≤ '7' then decodeOctalLitAux s (s.next i) (8*val + c.toNat - '0'.toNat)
    else none

private def decodeHexDigit (s : String) (i : String.Pos) : Option (Nat × String.Pos) :=
  let c := s.get i
  let i := s.next i
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat, i)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat, i)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat, i)
  else none

private partial def decodeHexLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else match decodeHexDigit s i with
    | some (d, i) => decodeHexLitAux s i (16*val + d)
    | none        => none

private partial def decodeDecimalLitAux (s : String) (i : String.Pos) (val : Nat) : Option Nat :=
  if s.atEnd i then some val
  else
    let c := s.get i
    if '0' ≤ c && c ≤ '9' then decodeDecimalLitAux s (s.next i) (10*val + c.toNat - '0'.toNat)
    else none

def decodeNatLitVal (s : String) : Option Nat :=
  let len := s.length
  if len == 0 then none
  else
    let c := s.get 0
    if c == '0' then
      if len == 1 then some 0
      else
        let c := s.get 1
        if c == 'x' || c == 'X' then decodeHexLitAux s 2 0
        else if c == 'b' || c == 'B' then decodeBinLitAux s 2 0
        else if c == 'o' || c == 'O' then decodeOctalLitAux s 2 0
        else if c.isDigit then decodeDecimalLitAux s 0 0
        else none
    else if c.isDigit then decodeDecimalLitAux s 0 0
    else none

def isLit? (litKind : SyntaxNodeKind) (stx : Syntax) : Option String :=
  match stx with
  | Syntax.node k args =>
    if k == litKind && args.size == 1 then
      match args.get! 0 with
      | (Syntax.atom _ val) => some val
      | _ => none
    else
      none
  | _ => none

def isNatLitAux (litKind : SyntaxNodeKind) (stx : Syntax) : Option Nat :=
  match isLit? litKind stx with
  | some val => decodeNatLitVal val
  | _        => none

def isNatLit? (s : Syntax) : Option Nat :=
  isNatLitAux numLitKind s

def isFieldIdx? (s : Syntax) : Option Nat :=
  isNatLitAux fieldIdxKind s

def isIdOrAtom? : Syntax → Option String
  | Syntax.atom _ val           => some val
  | Syntax.ident _ rawVal _ _   => some rawVal.toString
  | _ => none

def toNat (stx : Syntax) : Nat :=
  match stx.isNatLit? with
  | some val => val
  | none     => 0

def decodeQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) := do
  let c := s.get i
  let i := s.next i
  if c == '\\' then pure ('\\', i)
  else if c = '\"' then pure ('\"', i)
  else if c = '\'' then pure ('\'', i)
  else if c = 'r'  then pure ('\r', i)
  else if c = 'n'  then pure ('\n', i)
  else if c = 't'  then pure ('\t', i)
  else if c = 'x'  then
    let (d₁, i) ← decodeHexDigit s i
    let (d₂, i) ← decodeHexDigit s i
    pure (Char.ofNat (16*d₁ + d₂), i)
  else if c = 'u'  then do
    let (d₁, i) ← decodeHexDigit s i
    let (d₂, i) ← decodeHexDigit s i
    let (d₃, i) ← decodeHexDigit s i
    let (d₄, i) ← decodeHexDigit s i
    pure (Char.ofNat (16*(16*(16*d₁ + d₂) + d₃) + d₄), i)
  else
    none

partial def decodeStrLitAux (s : String) (i : String.Pos) (acc : String) : Option String := do
  let c := s.get i
  let i := s.next i
  if c == '\"' then
    pure acc
  else if s.atEnd i then
    none
  else if c == '\\' then do
    let (c, i) ← decodeQuotedChar s i
    decodeStrLitAux s i (acc.push c)
  else
    decodeStrLitAux s i (acc.push c)

def decodeStrLit (s : String) : Option String :=
  decodeStrLitAux s 1 ""

def isStrLit? (stx : Syntax) : Option String :=
  match isLit? strLitKind stx with
  | some val => decodeStrLit val
  | _        => none

def decodeCharLit (s : String) : Option Char :=
  let c := s.get 1
  if c == '\\' then do
    let (c, _) ← decodeQuotedChar s 2
    pure c
  else
    pure c

def isCharLit? (stx : Syntax) : Option Char :=
  match isLit? charLitKind stx with
  | some val => decodeCharLit val
  | _        => none

private partial def decodeNameLitAux (s : String) (i : Nat) (r : Name) : Option Name := do
  let continue? (i : Nat) (r : Name) : Option Name :=
    if s.get i == '.' then
       decodeNameLitAux s (s.next i) r
    else if s.atEnd i then
       pure r
    else
       none
  let curr := s.get i
  if isIdBeginEscape curr then
    let startPart := s.next i
    let stopPart  := s.nextUntil isIdEndEscape startPart
    if !isIdEndEscape (s.get stopPart) then none
    else continue? (s.next stopPart) (mkNameStr r (s.extract startPart stopPart))
  else if isIdFirst curr then
    let startPart := i
    let stopPart  := s.nextWhile isIdRest startPart
    continue? stopPart (mkNameStr r (s.extract startPart stopPart))
  else
    none

def decodeNameLit (s : String) : Option Name :=
  if s.get 0 == '`' then
    decodeNameLitAux s 1 Name.anonymous
  else
    none

def isNameLit? (stx : Syntax) : Option Name :=
  match isLit? nameLitKind stx with
  | some val => decodeNameLit val
  | _        => none

def hasArgs : Syntax → Bool
  | Syntax.node _ args => args.size > 0
  | _                  => false

def identToStrLit (stx : Syntax) : Syntax :=
  match stx with
  | Syntax.ident info _ val _ => mkStxStrLit (toString val) info
  | _                         => stx

def strLitToAtom (stx : Syntax) : Syntax :=
  match stx.isStrLit? with
  | none     => stx
  | some val => Syntax.atom stx.getHeadInfo.get! val

def isAtom : Syntax → Bool
  | atom _ _ => true
  | _        => false

def isToken (token : String) : Syntax → Bool
  | atom _ val => val.trim == token.trim
  | _          => false

def isIdent : Syntax → Bool
  | ident _ _ _ _ => true
  | _             => false

def getId : Syntax → Name
  | ident _ _ val _ => val
  | _               => Name.anonymous

def isNone (stx : Syntax) : Bool :=
  match stx with
  | Syntax.node k args => k == nullKind && args.size == 0
  | _                  => false

def getOptional? (stx : Syntax) : Option Syntax :=
  match stx with
  | Syntax.node k args => if k == nullKind && args.size == 1 then some (args.get! 0) else none
  | _                  => none

def getOptionalIdent? (stx : Syntax) : Option Name :=
  match stx.getOptional? with
  | some stx => some stx.getId
  | none     => none

partial def findAux (p : Syntax → Bool) : Syntax → Option Syntax
  | stx@(Syntax.node _ args) => if p stx then some stx else args.findSome? (findAux p)
  | stx                      => if p stx then some stx else none

def find? (stx : Syntax) (p : Syntax → Bool) : Option Syntax :=
  findAux p stx

end Syntax

/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class Quote (α : Type) :=
  (quote : α → Syntax)

export Quote (quote)

instance : Quote Syntax := ⟨id⟩
instance : Quote String := ⟨mkStxStrLit⟩
instance : Quote Nat := ⟨fun n => mkStxNumLit $ toString n⟩
instance : Quote Substring := ⟨fun s => mkCAppStx `String.toSubstring #[quote s.toString]⟩

private def quoteName : Name → Syntax
  | Name.anonymous => mkCIdent `Lean.Name.anonymous
  | Name.str n s _ => mkCAppStx `Lean.mkNameStr #[quoteName n, quote s]
  | Name.num n i _ => mkCAppStx `Lean.mkNameNum #[quoteName n, quote i]

instance : Quote Name := ⟨quoteName⟩

instance {α β : Type} [Quote α] [Quote β] : Quote (α × β) :=
  ⟨fun ⟨a, b⟩ => mkCAppStx `Prod.mk #[quote a, quote b]⟩

private def quoteList {α : Type} [Quote α] : List α → Syntax
  | []      => mkCIdent `List.nil
  | (x::xs) => mkCAppStx `List.cons #[quote x, quoteList xs]

instance {α : Type} [Quote α] : Quote (List α) := ⟨quoteList⟩

instance {α : Type} [Quote α] : Quote (Array α) :=
  ⟨fun xs => mkCAppStx `List.toArray #[quote xs.toList]⟩

private def quoteOption {α : Type} [Quote α] : Option α → Syntax
  | none     => mkIdent `Option.none
  | (some x) => mkCAppStx `Option.some #[quote x]

instance Option.hasQuote {α : Type} [Quote α] : Quote (Option α) := ⟨quoteOption⟩

end Lean

namespace Array

abbrev getSepElems := @getEvenElems

open Lean

private partial def filterSepElemsMAux {m : Type → Type} [Monad m] (a : Array Syntax) (p : Syntax → m Bool) (i : Nat) (acc : Array Syntax) : m (Array Syntax) := do
  if h : i < a.size then
    let stx := a.get ⟨i, h⟩
    if (← p stx) then
      if acc.isEmpty then
        filterSepElemsMAux a p (i+2) (acc.push stx)
      else if hz : i ≠ 0 then
        have i.pred < i from Nat.predLt hz
        let sepStx := a.get ⟨i.pred, Nat.ltTrans this h⟩
        filterSepElemsMAux a p (i+2) ((acc.push sepStx).push stx)
      else
        filterSepElemsMAux a p (i+2) (acc.push stx)
    else
      filterSepElemsMAux a p (i+2) acc
  else
    pure acc

def filterSepElemsM {m : Type → Type} [Monad m] (a : Array Syntax) (p : Syntax → m Bool) : m (Array Syntax) :=
  filterSepElemsMAux a p 0 #[]

def filterSepElems (a : Array Syntax) (p : Syntax → Bool) : Array Syntax :=
  Id.run $ a.filterSepElemsM p

private partial def mapSepElemsMAux {m : Type → Type} [Monad m] (a : Array Syntax) (f : Syntax → m Syntax) (i : Nat) (acc : Array Syntax) : m (Array Syntax) := do
  if h : i < a.size then
    let stx := a.get ⟨i, h⟩
    if i % 2 == 0 then do
      stx ← f stx
      mapSepElemsMAux a f (i+1) (acc.push stx)
    else
      mapSepElemsMAux a f (i+1) (acc.push stx)
  else
    pure acc

def mapSepElemsM {m : Type → Type} [Monad m] (a : Array Syntax) (f : Syntax → m Syntax) : m (Array Syntax) :=
  mapSepElemsMAux a f 0 #[]

def mapSepElems (a : Array Syntax) (f : Syntax → Syntax) : Array Syntax :=
  Id.run $ a.mapSepElemsM f

end Array

/--
  Gadget for automatic parameter support. This is similar to the `optParam` gadget, but it uses
  the given tactic.
  Like `optParam`, this gadget only affects elaboration.
  For example, the tactic will *not* be invoked during type class resolution. -/
abbrev autoParam.{u} (α : Sort u) (tactic : Lean.Syntax) : Sort u := α

/- Helper functions for manipulating interpolated strings -/
namespace Lean.Syntax

private def decodeInterpStrQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) :=
  match decodeQuotedChar s i with
  | some r => some r
  | none   =>
    let c := s.get i
    let i := s.next i
    if c == '{' then pure ('{', i)
    else none

private partial def decodeInterpStrLit (s : String) : Option String :=
  let rec loop (i : String.Pos) (acc : String) :=
    let c := s.get i
    let i := s.next i
    if c == '\"' || c == '{' then
      pure acc
    else if s.atEnd i then
      none
    else if c == '\\' then do
      let (c, i) ← decodeInterpStrQuotedChar s i
      loop i (acc.push c)
    else
      loop i (acc.push c)
  loop 1 ""

partial def isInterpolatedStrLit? (stx : Syntax) : Option String :=
  match isLit? interpolatedStrLitKind stx with
  | none     => none
  | some val => decodeInterpStrLit val

def expandInterpolatedStrChunks (chunks : Array Syntax) (mkAppend : Syntax → Syntax → MacroM Syntax) (mkElem : Syntax → MacroM Syntax) : MacroM Syntax := do
  let i      := 0
  let result := Syntax.missing
  for elem in chunks do
    let elem ← match elem.isInterpolatedStrLit? with
      | none     => mkElem elem
      | some str => mkElem (mkStxStrLit str)
    if i == 0 then
      result := elem
    else
      result ← mkAppend result elem
    i := i+1
  return result

def getSepArgs (stx : Syntax) : Array Syntax :=
  stx.getArgs.getSepElems

end Lean.Syntax
