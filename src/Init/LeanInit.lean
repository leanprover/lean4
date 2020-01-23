/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich
-/
prelude
import Init.Data.String.Basic
import Init.Data.Array.Basic
import Init.Data.UInt
import Init.Data.Hashable
import Init.Control.Reader
import Init.Control.Except

namespace Lean
/-
Basic Lean types used to implement builtin commands and extensions.
Note that this file is part of the Lean `Init` library instead of
`Lean` actual implementation.
The idea is to allow users to implement simple parsers, macros and tactics
without importing the whole `Lean` module.
It also allow us to use extensions to develop the `Init` library.
-/

/- Hierarchical names -/
inductive Name
| anonymous : Name
| str : Name → String → USize → Name
| num : Name → Nat → USize → Name

instance Name.inhabited : Inhabited Name :=
⟨Name.anonymous⟩

protected def Name.hash : Name → USize
| Name.anonymous => 1723
| Name.str p s h => h
| Name.num p v h => h

instance Name.hashable : Hashable Name := ⟨Name.hash⟩

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
protected def Name.beq : (@& Name) → (@& Name) → Bool
| anonymous,   anonymous   => true
| str p₁ s₁ _, str p₂ s₂ _ => s₁ == s₂ && Name.beq p₁ p₂
| num p₁ n₁ _, num p₂ n₂ _ => n₁ == n₂ && Name.beq p₁ p₂
| _,           _           => false

instance : HasBeq Name := ⟨Name.beq⟩

def toStringWithSep (sep : String) : Name → String
| anonymous         => "[anonymous]"
| str anonymous s _ => s
| num anonymous v _ => toString v
| str n s _         => toStringWithSep n ++ sep ++ s
| num n v _         => toStringWithSep n ++ sep ++ repr v

protected def toString : Name → String :=
toStringWithSep "."

instance : HasToString Name :=
⟨Name.toString⟩

protected def append : Name → Name → Name
| n, anonymous => n
| n, str p s _ => mkNameStr (append n p) s
| n, num p d _ => mkNameNum (append n p) d

instance : HasAppend Name :=
⟨Name.append⟩

end Name

structure NameGenerator :=
(namePrefix : Name := `_uniq)
(idx        : Nat  := 1)

namespace NameGenerator

instance : Inhabited NameGenerator := ⟨{}⟩

@[inline] def curr (g : NameGenerator) : Name :=
mkNameNum g.namePrefix g.idx

@[inline] def next (g : NameGenerator) : NameGenerator :=
{ idx := g.idx + 1, .. g }

@[inline] def mkChild (g : NameGenerator) : NameGenerator × NameGenerator :=
({ namePrefix := mkNameNum g.namePrefix g.idx, idx := 1 },
 { idx := g.idx + 1, .. g })

end NameGenerator

inductive ParserKind
| leading | trailing

/-
  Small DSL for describing parsers. We implement an interpreter for it
  at `Parser.lean` -/
inductive ParserDescrCore : ParserKind → Type
| andthen {k : ParserKind}       : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| orelse  {k : ParserKind}       : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| optional {k : ParserKind}      : ParserDescrCore k → ParserDescrCore k
| lookahead {k : ParserKind}     : ParserDescrCore k → ParserDescrCore k
| try {k : ParserKind}           : ParserDescrCore k → ParserDescrCore k
| many {k : ParserKind}          : ParserDescrCore k → ParserDescrCore k
| many1 {k : ParserKind}         : ParserDescrCore k → ParserDescrCore k
| sepBy {k : ParserKind}         : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| sepBy1 {k : ParserKind}        : ParserDescrCore k → ParserDescrCore k → ParserDescrCore k
| node {k : ParserKind}          : Name → ParserDescrCore k → ParserDescrCore k
| symbol {k : ParserKind}        : String → Option Nat → ParserDescrCore k
| nonReservedSymbol              : String → Bool → ParserDescrCore ParserKind.leading
| num {k : ParserKind}           : ParserDescrCore k
| str {k : ParserKind}           : ParserDescrCore k
| char {k : ParserKind}          : ParserDescrCore k
| ident {k : ParserKind}         : ParserDescrCore k
| pushLeading                    : ParserDescrCore ParserKind.trailing
| parser {k : ParserKind}        : Name → Nat → ParserDescrCore k

instance ParserDescrCore.inhabited {k} : Inhabited (ParserDescrCore k) := ⟨ParserDescrCore.symbol "" none⟩

abbrev ParserDescr := ParserDescrCore ParserKind.leading
abbrev TrailingParserDescr := ParserDescrCore ParserKind.trailing

@[matchPattern] abbrev ParserDescr.andthen := @ParserDescrCore.andthen
@[matchPattern] abbrev ParserDescr.orelse := @ParserDescrCore.orelse
@[matchPattern] abbrev ParserDescr.optional := @ParserDescrCore.optional
@[matchPattern] abbrev ParserDescr.lookahead := @ParserDescrCore.lookahead
@[matchPattern] abbrev ParserDescr.try := @ParserDescrCore.try
@[matchPattern] abbrev ParserDescr.many := @ParserDescrCore.many
@[matchPattern] abbrev ParserDescr.many1 := @ParserDescrCore.many1
@[matchPattern] abbrev ParserDescr.sepBy := @ParserDescrCore.sepBy
@[matchPattern] abbrev ParserDescr.sepBy1 := @ParserDescrCore.sepBy1
@[matchPattern] abbrev ParserDescr.node := @ParserDescrCore.node
@[matchPattern] abbrev ParserDescr.symbol := @ParserDescrCore.symbol
@[matchPattern] abbrev ParserDescr.num := @ParserDescrCore.num
@[matchPattern] abbrev ParserDescr.str := @ParserDescrCore.str
@[matchPattern] abbrev ParserDescr.char := @ParserDescrCore.char
@[matchPattern] abbrev ParserDescr.ident := @ParserDescrCore.ident
@[matchPattern] abbrev ParserDescr.nonReservedSymbol := @ParserDescrCore.nonReservedSymbol
@[matchPattern] abbrev ParserDescr.pushLeading := @ParserDescrCore.pushLeading
@[matchPattern] abbrev ParserDescr.parser := @ParserDescrCore.parser

/- Syntax -/

structure SourceInfo :=
/- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
   it is not at all clear what the preceding token was, especially with backtracking. -/
(leading  : Substring)
(pos      : String.Pos)
(trailing : Substring)

abbrev SyntaxNodeKind := Name

/- Syntax AST -/

inductive Syntax
| missing {} : Syntax
| node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
| atom   {} (info : Option SourceInfo) (val : String) : Syntax
| ident  {} (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Name × List String)) : Syntax

instance Syntax.inhabited : Inhabited Syntax :=
⟨Syntax.missing⟩

namespace Syntax

def getKind (stx : Syntax) : SyntaxNodeKind :=
match stx with
| Syntax.node k args   => k
-- We use these "pseudo kinds" for antiquotation kinds.
-- For example, an antiquotation `$id:ident` (using Lean.Parser.Term.ident)
-- is compiled to ``if stx.isOfKind `ident ...``
| Syntax.missing       => `missing
| Syntax.atom _ v      => mkNameSimple v
| Syntax.ident _ _ _ _ => `ident

def isOfKind : Syntax → SyntaxNodeKind → Bool
| stx, k => stx.getKind == k

def getArg (stx : Syntax) (i : Nat) : Syntax :=
match stx with
| Syntax.node _ args => args.get! i
| _                  => arbitrary _

def getArgs (stx : Syntax) : Array Syntax :=
match stx with
| Syntax.node _ args => args
| _                  => #[]

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo : Syntax → Option SourceInfo
| atom info _      => info
| ident info _ _ _ => info
| node _ args      => args.find? getHeadInfo
| _                => none

end Syntax

/-
Runtime support for making quotation terms auto-hygienic, by mangling identifiers
introduced by them with a "macro scope" supplied by the context. Details to appear in a
paper soon.
-/

abbrev MacroScope := Nat

/-- A monad that supports syntax quotations. Syntax quotations (in term
    position) are monadic values that when executed retrieve the current "macro
    scope" from the monad and apply it to every identifier they introduce
    (independent of whether this identifier turns out to be a reference to an
    existing declaration, or an actually fresh binding during further
    elaboration). -/
class MonadQuotation (m : Type → Type) :=
-- Get the fresh scope of the current macro invocation
(getCurrMacroScope {} : m MacroScope)
(getMainModule {}     : m Name)
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
export MonadQuotation

/-
We represent a name with macro scopes as
```
<actual name>._@.<main_module>._hyg.<scopes>
```
Example: suppose the main module name is `Init.Data.List.Basic`, and name is `foo.bla`, and macroscopes [2, 5]
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```

We use two delimiters for improving `hasMacroScopes` performance.
-/

private def mkMacroScopeName (mainModule : Name) (n : Name) : Name :=
mkNameStr (mkNameStr n "_@" ++ mainModule) "_hyg"

def addMacroScope (mainModule : Name) (n : Name) (scp : MacroScope) : Name :=
mkNameNum (mkMacroScopeName mainModule n) scp

def addMacroScopes (mainModule : Name) (n : Name) (scps : List MacroScope) : Name :=
match scps with
| [] => n
| _  => scps.foldl mkNameNum (mkMacroScopeName mainModule n)

def Name.hasMacroScopes : Name → Bool
| Name.str _ str _ => str == "_hyg"
| Name.num p _   _ => Name.hasMacroScopes p
| _                => false

structure ExtractMacroScopesResult :=
(name       : Name)
(mainModule : Name)
(scopes     : List MacroScope)

instance ExtractMacroScopesResult.inhabited : Inhabited ExtractMacroScopesResult :=
⟨⟨arbitrary _, arbitrary _, arbitrary _⟩⟩

private def assembleExtractedName : List Name → Name → Name
| [],                     acc => acc
| (Name.str _ s _) :: ps, acc => assembleExtractedName ps (mkNameStr acc s)
| (Name.num _ n _) :: ps, acc => assembleExtractedName ps (mkNameNum acc n)
| _,                      _   => unreachable!

private def extractMainModule (scps : List MacroScope) : Name → List Name → ExtractMacroScopesResult
| n@(Name.str p str _), acc =>
  if str == "_@" then
    { name := p, mainModule := assembleExtractedName acc Name.anonymous, scopes := scps }
  else
    extractMainModule p (n :: acc)
| n@(Name.num p num _), acc => extractMainModule p (n :: acc)
| _,                    _   => unreachable!

private def extractMacroScopesAux : Name → List MacroScope → ExtractMacroScopesResult
| Name.num p scp _, acc => extractMacroScopesAux p (scp::acc)
| Name.str p str _, acc => extractMainModule acc.reverse p [] -- str must be "_hyg"
| _,                _   => unreachable!

/--
  Revert all `addMacroScope` calls. `⟨mainModule, n', scps⟩ = extractMacroScopes n → n = addMacroScopes mainModule n' scps`.
  This operation is useful for analyzing/transforming the original identifiers, then adding back
  the scopes (via `addMacroScopes`). -/
def extractMacroScopes (n : Name) : ExtractMacroScopesResult :=
if n.hasMacroScopes then
  extractMacroScopesAux n []
else
  { name := n, scopes := [], mainModule := Name.anonymous }

private def eraseMacroScopesAux : Name → Name
| Name.str p str _ => if str == "_@" then p else eraseMacroScopesAux p
| Name.num p _ _   => eraseMacroScopesAux p
| Name.anonymous   => unreachable!

def Name.eraseMacroScopes (n : Name) : Name :=
if n.hasMacroScopes then eraseMacroScopesAux n else n

namespace Macro

structure Context :=
(mainModule     : Name)
(currMacroScope : MacroScope)

inductive Exception
| error             : String → Exception
| unsupportedSyntax : Exception

end Macro

abbrev MacroM := ReaderT Macro.Context (ExceptT Macro.Exception Id)

def Macro.addMacroScope (n : Name) : MacroM Name := do
ctx ← read;
pure $ Lean.addMacroScope ctx.mainModule n ctx.currMacroScope

instance MacroM.monadQuotation : MonadQuotation MacroM :=
{ getCurrMacroScope   := fun ctx => pure ctx.currMacroScope,
  getMainModule       := fun ctx => pure ctx.mainModule,
  withFreshMacroScope := fun _ x => x }

abbrev Macro := Syntax → MacroM Syntax

/- Builtin kinds -/

@[matchPattern] def choiceKind : SyntaxNodeKind := `choice
@[matchPattern] def nullKind : SyntaxNodeKind := `null
def strLitKind : SyntaxNodeKind := `strLit
def charLitKind : SyntaxNodeKind := `charLit
def numLitKind : SyntaxNodeKind := `numLit
def fieldIdxKind : SyntaxNodeKind := `fieldIdx

/- Helper functions for processing Syntax programmatically -/

/--
  Create an identifier using `SourceInfo` from `src`.
  To refer to a specific constant, use `mkCIdentFrom` instead. -/
def mkIdentFrom (src : Syntax) (val : Name) : Syntax :=
let info := src.getHeadInfo;
Syntax.ident info (toString val).toSubstring val []

/--
  Create an identifier referring to a constant `c` using `SourceInfo` from `src`.
  This variant of `mkIdentFrom` makes sure that the identifier cannot accidentally
  be captured. -/
def mkCIdentFrom (src : Syntax) (c : Name) : Syntax :=
let info := src.getHeadInfo;
Syntax.ident info (toString c).toSubstring (`_root_ ++ c) [(c, [])]

def mkAtomFrom (src : Syntax) (val : String) : Syntax :=
let info := src.getHeadInfo;
Syntax.atom info val

def Syntax.identToAtom (stx : Syntax) : Syntax :=
match stx with
| Syntax.ident info _ val _ => Syntax.atom info val.eraseMacroScopes.toString
| _                         => stx

@[export lean_mk_syntax_ident]
def mkIdent (val : Name) : Syntax :=
Syntax.ident none (toString val).toSubstring val []

@[inline] def mkNullNode (args : Array Syntax := #[]) : Syntax :=
Syntax.node nullKind args

def mkOptionalNode (arg : Option Syntax) : Syntax :=
match arg with
| some arg => Syntax.node nullKind #[arg]
| none     => Syntax.node nullKind #[]

/-- Create syntax representing a Lean term application -/
def mkAppStx (fn : Syntax) (args : Array Syntax) : Syntax :=
Syntax.node `Lean.Parser.Term.app #[fn, mkNullNode args]

def mkHole (ref : Syntax) : Syntax :=
Syntax.node `Lean.Parser.Term.hole #[mkAtomFrom ref "_"]

/-- Convert a `Syntax.ident` into a `Lean.Parser.Term.id` node -/
def mkTermIdFromIdent (ident : Syntax) : Syntax :=
match ident with
| Syntax.ident _ _ _ _ => Syntax.node `Lean.Parser.Term.id #[ident, mkNullNode]
| _                    => unreachable!

/--
  Create a simple `Lean.Parser.Term.id` syntax using position
  information from `ref` and name `n`. By simple, we mean that
  `optional (explicitUniv <|> namedPattern)` is none.
  To refer to a specific constant, use `mkCTermIdFrom` instead. -/
def mkTermIdFrom (ref : Syntax) (n : Name) : Syntax :=
mkTermIdFromIdent (mkIdentFrom ref n)

/-- Variant of `mkTermIdFrom` that makes sure that the identifier cannot accidentally
    be captured. -/
def mkCTermIdFrom (ref : Syntax) (c : Name) : Syntax :=
mkTermIdFromIdent (mkCIdentFrom ref c)

def mkTermId (n : Name) : Syntax :=
mkTermIdFrom Syntax.missing n

def mkCTermId (c : Name) : Syntax :=
mkCTermIdFrom Syntax.missing c

def mkCAppStx (fn : Name) (args : Array Syntax) : Syntax :=
mkAppStx (mkCTermId fn) args

def mkStxLit (kind : SyntaxNodeKind) (val : String) (info : Option SourceInfo := none) : Syntax :=
let atom : Syntax := Syntax.atom info val;
Syntax.node kind #[atom]

def mkStxStrLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkStxLit strLitKind (repr val) info

def mkStxNumLit (val : String) (info : Option SourceInfo := none) : Syntax :=
mkStxLit numLitKind val info

namespace Syntax

/- Recall that we don't have special Syntax constructors for storing numeric and string atoms.
   The idea is to have an extensible approach where embedded DSLs may have new kind of atoms and/or
   different ways of representing them. So, our atoms contain just the parsed string.
   The main Lean parser uses the kind `numLitKind` for storing natural numbers that can be encoded
   in binary, octal, decimal and hexadecimal format. `isNatLit` implements a "decoder"
   for Syntax objects representing these numerals. -/

private partial def decodeBinLitAux (s : String) : String.Pos → Nat → Option Nat
| i, val =>
  if s.atEnd i then some val
  else
    let c := s.get i;
    if c == '0' then decodeBinLitAux (s.next i) (2*val)
    else if c == '1' then decodeBinLitAux (s.next i) (2*val + 1)
    else none

private partial def decodeOctalLitAux (s : String) : String.Pos → Nat → Option Nat
| i, val =>
  if s.atEnd i then some val
  else
    let c := s.get i;
    if '0' ≤ c && c ≤ '7' then decodeOctalLitAux (s.next i) (8*val + c.toNat - '0'.toNat)
    else none

private def decodeHexDigit (s : String) (i : String.Pos) : Option (Nat × String.Pos) :=
let c := s.get i;
let i := s.next i;
if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat, i)
else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat, i)
else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat, i)
else none

private partial def decodeHexLitAux (s : String) : String.Pos → Nat → Option Nat
| i, val =>
  if s.atEnd i then some val
  else match decodeHexDigit s i with
    | some (d, i) => decodeHexLitAux i (16*val + d)
    | none        => none

private partial def decodeDecimalLitAux (s : String) : String.Pos → Nat → Option Nat
| i, val =>
  if s.atEnd i then some val
  else
    let c := s.get i;
    if '0' ≤ c && c ≤ '9' then decodeDecimalLitAux (s.next i) (10*val + c.toNat - '0'.toNat)
    else none

private def decodeNatLitVal (s : String) : Option Nat :=
let len := s.length;
if len == 0 then none
else
  let c := s.get 0;
  if c == '0' then
    if len == 1 then some 0
    else
      let c := s.get 1;
      if c == 'x' || c == 'X' then decodeHexLitAux s 2 0
      else if c == 'b' || c == 'B' then decodeBinLitAux s 2 0
      else if c == 'o' || c == 'O' then decodeOctalLitAux s 2 0
      else if c.isDigit then decodeDecimalLitAux s 0 0
      else none
  else if c.isDigit then decodeDecimalLitAux s 0 0
  else none

def isNatLitAux (nodeKind : SyntaxNodeKind) : Syntax → Option Nat
| Syntax.node k args   =>
  if k == nodeKind && args.size == 1 then
    match args.get! 0 with
    | (Syntax.atom _ val) => decodeNatLitVal val
    | _ => none
  else
    none
| _ => none

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

private def decodeQuotedChar (s : String) (i : String.Pos) : Option (Char × String.Pos) :=
let c := s.get i;
let i := s.next i;
if c == '\\' then pure ('\\', i)
else if c = '\"' then pure ('\"', i)
else if c = '\'' then pure ('\'', i)
else if c = 'n'  then pure ('\n', i)
else if c = 't'  then pure ('\t', i)
else if c = 'x'  then do
  (d₁, i) ← decodeHexDigit s i;
  (d₂, i) ← decodeHexDigit s i;
  pure (Char.ofNat (16*d₁ + d₂), i)
else if c = 'u'  then do
  (d₁, i) ← decodeHexDigit s i;
  (d₂, i) ← decodeHexDigit s i;
  (d₃, i) ← decodeHexDigit s i;
  (d₄, i) ← decodeHexDigit s i;
  pure $ (Char.ofNat (16*(16*(16*d₁ + d₂) + d₃) + d₄), i)
else
  none

partial def decodeStrLitAux (s : String) : String.Pos → String → Option String
| i, acc => do
  let c := s.get i;
  let i := s.next i;
  if c == '\"' then
    pure acc
  else if c == '\\' then do
    (c, i) ← decodeQuotedChar s i;
    decodeStrLitAux i (acc.push c)
  else
    decodeStrLitAux i (acc.push c)

def decodeStrLit (s : String) : Option String :=
decodeStrLitAux s 1 ""

def isStrLit? : Syntax → Option String
| Syntax.node k args   =>
  if k == strLitKind && args.size == 1 then
    match args.get! 0 with
    | (Syntax.atom _ val) => decodeStrLit val
    | _                   => none
  else
    none
| _ => none

def decodeCharLit (s : String) : Option Char :=
let c := s.get 1;
if c == '\\' then do
  (c, _) ← decodeQuotedChar s 2;
  pure c
else
  pure c

def isCharLit? : Syntax → Option Char
| Syntax.node k args   =>
  if k == charLitKind && args.size == 1 then
    match args.get! 0 with
    | (Syntax.atom _ val) => decodeCharLit val
    | _ => none
  else
    none
| _ => none

def hasArgs : Syntax → Bool
| Syntax.node _ args => args.size > 0
| _                  => false

def identToStrLit (stx : Syntax) : Syntax :=
match stx with
| Syntax.ident info _ val _ => mkStxStrLit val.toString info
| _                         => stx

def strLitToAtom (stx : Syntax) : Syntax :=
match stx.isStrLit? with
| none     => stx
| some val => Syntax.atom stx.getHeadInfo val

/-- Given `var` a `Term.id`, created the antiquotation syntax representing `$<var>:<catName>` -/
def termIdToAntiquot (var : Syntax) (catName : String) : Syntax :=
Syntax.node `Lean.Parser.antiquot #[mkAtomFrom var "$", var, mkAtomFrom var ":", mkAtomFrom var catName, mkNullNode]

end Syntax
end Lean

abbrev Array.getSepElems := @Array.getEvenElems
