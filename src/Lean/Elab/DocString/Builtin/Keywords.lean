/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
prelude
public import Lean.Elab.DocString.Builtin.Scopes
public import Lean.Elab.DocString.Builtin.Postponed
public meta import Lean.Elab.DocString.Builtin.Postponed
public import Lean.DocString.Syntax
public import Lean.Elab.InfoTree
public import Lean.Parser
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega


namespace Lean.Doc
open Lean Elab Term
open Lean.Parser
open scoped Lean.Doc.Syntax

set_option linter.missingDocs true

/-- The code represents an atom drawn from some syntax. -/
structure Data.Atom where
  /-- The syntax kind's name. -/
  name : Name
  /-- The syntax category -/
  category : Name
deriving TypeName


private def onlyCode [Monad m] [MonadError m] (xs : TSyntaxArray `inline) : m StrLit := do
  if h : xs.size = 1 then
    match xs[0] with
    | `(inline|code($s)) => return s
    | other => throwErrorAt other "Expected code"
  else
    throwError "Expected precisely 1 code argument"


/--
Checks whether a syntax descriptor's value contains the given atom.
-/
private partial def containsAtom (e : Expr) (atom : String) : MetaM Bool := do
  let rec attempt (p : Expr) (tryWhnf : Bool) : MetaM Bool := do
    match p.getAppFnArgs with
    | (``ParserDescr.node, #[_, _, p]) => containsAtom p atom
    | (``ParserDescr.trailingNode, #[_, _, _, p]) => containsAtom p atom
    | (``ParserDescr.unary, #[.app _ (.lit (.strVal _)), p]) => containsAtom p atom
    | (``ParserDescr.binary, #[.app _ (.lit (.strVal "andthen")), p, _]) => containsAtom p atom
    | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _]) => pure (tk.trimAscii == atom.toSlice)
    | (``ParserDescr.symbol, #[.lit (.strVal tk)]) => pure (tk.trimAscii == atom.toSlice)
    | (``Parser.withAntiquot, #[_, p]) => containsAtom p atom
    | (``Parser.leadingNode, #[_, _, p]) => containsAtom p atom
    | (``HAndThen.hAndThen, #[_, _, _, _, p1, p2]) =>
      containsAtom p1 atom <||> containsAtom p2 atom
    | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _]) => pure (tk.trimAscii == atom.toSlice)
    | (``Parser.symbol, #[.lit (.strVal tk)]) => pure (tk.trimAscii == atom.toSlice)
    | (``Parser.symbol, #[_nonlit]) => pure false
    | (``Parser.withCache, #[_, p]) => containsAtom p atom
    | _ => if tryWhnf then attempt (← Meta.whnf p) false else pure false
  attempt e true

/--
Checks whether a syntax descriptor's value contains the given atom. If so, the residual value after
the atom is returned.
-/
private partial def containsAtom' (e : Expr) (atom : String) : MetaM (Option Expr) := do
  let rec attempt (p : Expr) (tryWhnf : Bool) : MetaM (Option Expr) := do
    match p.getAppFnArgs with
    | (``ParserDescr.node, #[_, _, p]) => containsAtom' p atom
    | (``ParserDescr.trailingNode, #[_, _, _, p]) => containsAtom' p atom
    | (``ParserDescr.unary, #[.app _ (.lit (.strVal _)), p]) => containsAtom' p atom
    | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _])
    | (``ParserDescr.symbol, #[.lit (.strVal tk)])
    | (``Parser.symbol, #[.lit (.strVal tk)])
    | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _]) =>
        if tk.trimAscii == atom.toSlice then
          pure (Expr.app (.const ``ParserDescr.const []) (toExpr ``Parser.skip))
        else pure none
    | (``Parser.withAntiquot, #[_, p]) => containsAtom' p atom
    | (``Parser.leadingNode, #[_, _, p]) => containsAtom' p atom
    | (``HAndThen.hAndThen, #[_, _, _, _, p1, p2])
    | (``ParserDescr.binary, #[.app _ (.lit (.strVal "andthen")), p1, p2]) =>
      if let some r ← containsAtom' p1 atom then
        pure <| some <| mkApp3 (.const ``ParserDescr.binary []) (toExpr ``Parser.andthen) r p2
      else containsAtom' p2 atom
    | (``Parser.symbol, #[_nonlit]) => pure none
    | (``Parser.withCache, #[_, p]) => containsAtom' p atom
    | _ => if tryWhnf then attempt (← Meta.whnf p) false else pure none
  attempt e true

private partial def canEpsilon (e : Expr) : MetaM Bool := do
  let rec attempt (p : Expr) (tryWhnf : Bool) : MetaM Bool := do
    match p.getAppFnArgs with
    | (``ParserDescr.node, #[_, _, p]) => canEpsilon p
    | (``ParserDescr.trailingNode, #[_, _, _, p]) => canEpsilon p
    | (``ParserDescr.unary, #[.app _ (.lit (.strVal _)), p]) => canEpsilon p
    | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal _tk), _])
    | (``ParserDescr.symbol, #[_])
    | (``Parser.symbol, #[_])
    | (``Parser.nonReservedSymbol, #[_, _]) =>
      pure false
    | (``Parser.withAntiquot, #[_, p]) => canEpsilon p
    | (``Parser.leadingNode, #[_, _, p]) => canEpsilon p
    | (``HAndThen.hAndThen, #[_, _, _, _, p1, p2])
    | (``ParserDescr.binary, #[(.app _ (.lit (.strVal "andthen"))), p1, p2]) =>
      canEpsilon p1 <&&> canEpsilon p2
    | (``Parser.withCache, #[_, p]) => canEpsilon p
    | _ =>
      if tryWhnf then attempt (← Meta.whnf p) false
      else pure false -- Conservative approximation
  attempt e true

/--
Checks whether a syntax descriptor's value begins with the given atom. If so, the residual value
after the atom is returned.
-/
private partial def startsWithAtom? (e : Expr) (atom : String) : MetaM (Option Expr) := do
  let rec attempt (p : Expr) (tryWhnf : Bool) : MetaM (Option Expr) := do
    match p.getAppFnArgs with
    | (``ParserDescr.node, #[_, _, p]) => startsWithAtom? p atom
    | (``ParserDescr.trailingNode, #[_, _, _, p]) => startsWithAtom? p atom
    | (``ParserDescr.unary, #[.app _ (.lit (.strVal _)), p]) => startsWithAtom? p atom
    | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _])
    | (``ParserDescr.symbol, #[.lit (.strVal tk)])
    | (``Parser.symbol, #[.lit (.strVal tk)])
    | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _]) =>
        if tk.trimAscii == atom.toSlice then
          pure (Expr.app (.const ``ParserDescr.const []) (toExpr ``Parser.skip))
        else pure none
    | (``Parser.withAntiquot, #[_, p]) => startsWithAtom? p atom
    | (``Parser.leadingNode, #[_, _, p]) => startsWithAtom? p atom
    | (``HAndThen.hAndThen, #[_, _, _, _, p1, p2])
    | (``ParserDescr.binary, #[(.app _ (.lit (.strVal "andthen"))), p1, p2]) =>
      if let some r ← startsWithAtom? p1 atom then
        pure <| some <| mkApp3 (.const ``ParserDescr.binary []) (toExpr ``Parser.andthen) r p2
      else if ← canEpsilon p1 then
        startsWithAtom? p2 atom
      else pure none
    | (``Parser.symbol, #[_nonlit]) => pure none
    | (``Parser.withCache, #[_, p]) => startsWithAtom? p atom
    | _ => if tryWhnf then attempt (← Meta.whnf p) false else pure none
  attempt e true

/--
Checks whether a syntax descriptor's value begins with the given atoms. If so, the residual value
after the atoms is returned.
-/
private partial def startsWithAtoms? (e : Expr) (atoms : List String) : MetaM (Option Expr) := do
  match atoms with
  | [] => pure e
  | a :: as =>
    if let some e' ← startsWithAtom? e a then
      startsWithAtoms? e' as
    else pure none

private partial def exprContainsAtoms (e : Expr) (atoms : List String) : MetaM Bool := do
  match atoms with
  | [] => pure true
  | a :: as =>
    if let some e' ← containsAtom' e a then
      (startsWithAtoms? e' as <&> Option.isSome) <||> exprContainsAtoms e' (a :: as)
    else pure false

private def withAtom (cat : Name) (atom : String) : DocM (Array Name) := do
  let env ← getEnv
  let some catContents := (Lean.Parser.parserExtension.getState env).categories.find? cat
    | return #[]
  let kinds := catContents.kinds
  let mut found := #[]
  for (k, _) in kinds do
    if let some d := env.find? k |>.bind (·.value?) then
      if (← containsAtom d atom) then
        found := found.push k
  return found

private partial def isAtoms (atoms : List String) (stx : Syntax) : Bool :=
  StateT.run (go [stx]) atoms |>.fst
where
  go (stxs : List Syntax) : StateM (List String) Bool := do
    match ← get with
    | [] => return true
    | a :: as =>
      match stxs with
      | [] => return false
      | .ident .. :: _ => return false
      | .atom _ s :: ss =>
        if a.trimAscii == s.trimAscii then
          set as
          go ss
        else return false
      | .missing :: ss => go ss
      | .node _ _ args :: ss =>
        go (args.toList ++ ss)

private def parserHasAtomPrefix (atoms : List String) (p : Parser) : TermElabM Bool := do
  let str := " ".intercalate atoms
  let env ← getEnv
  let options ← getOptions
  let s := mkParserState str
  -- Some parsers look upwards in the stack and will crash without this
  let s := s.pushSyntax .missing
  let s := p.fn.run {inputString := str, fileName := "", fileMap := FileMap.ofString str} {env, options} (getTokenTable env) s
  return isAtoms atoms (mkNullNode (s.stxStack.extract 1 s.stxStack.size))

private unsafe def namedParserHasAtomPrefixUnsafe (atoms : List String) (parserName : Name) : TermElabM Bool := do
  try
    let p ← evalConstCheck Parser ``Parser parserName
    parserHasAtomPrefix atoms p
  catch | _ => pure false

@[implemented_by namedParserHasAtomPrefixUnsafe]
private opaque namedParserHasAtomPrefix (atoms : List String) (parserName : Name) : TermElabM Bool

private def parserDescrCanEps : ParserDescr → Bool
  | .node _ _ p | .trailingNode _ _ _ p => parserDescrCanEps p
  | .binary ``Parser.andthen p1 p2 => parserDescrCanEps p1 && parserDescrCanEps p2
  | .binary ``Parser.orelse p1 p2 => parserDescrCanEps p1 || parserDescrCanEps p2
  | .const ``Parser.skip => true
  | .unary ``Parser.optional _ => true
  | .unary ``Parser.many _ => true
  | .const ``Parser.ppSpace => true
  | .const ``Parser.ppLine => true
  | .const ``Parser.ppHardSpace => true
  | _ => false

private def parserDescrHasAtom (atom : String) (p : ParserDescr) : TermElabM (Option ParserDescr) := do
  match p with
  | .node _ _ p | .trailingNode _ _ _ p | .unary _ p =>
    parserDescrHasAtom atom p
  | .nonReservedSymbol tk _ | .symbol tk =>
    if tk.trimAscii == atom.toSlice then
      pure (some (.const ``Parser.skip))
    else pure none
  | .binary ``Parser.andthen p1 p2 =>
    if let some p1' ← parserDescrHasAtom atom p1 then
      pure <| some <| .binary ``Parser.andthen p1' p2
    else parserDescrHasAtom atom p2
  | .binary ``Parser.orelse p1 p2 =>
    let p1' ← parserDescrHasAtom atom p1
    let p2' ← parserDescrHasAtom atom p2
    match p1', p2' with
    | some x, some y => pure <| some (.binary ``Parser.orelse x y)
    | some _, none => pure p1'
    | none, some _ => pure p2'
    | none, none => pure none
  | _ => pure none

private def parserDescrStartsWithAtom (atom : String) (p : ParserDescr) : TermElabM (Option ParserDescr) := do
  match p with
  | .node _ _ p | .trailingNode _ _ _ p | .unary _ p =>
    parserDescrStartsWithAtom atom p
  | .nonReservedSymbol tk _ | .symbol tk =>
    if tk.trimAscii == atom.toSlice then
      pure (some (.const ``Parser.skip))
    else pure none
  | .binary ``Parser.andthen p1 p2 =>
    if let some p1' ← parserDescrStartsWithAtom atom p1 then
      pure <| some <| .binary ``Parser.andthen p1' p2
    else if parserDescrCanEps p1 then parserDescrStartsWithAtom atom p2
    else pure none
  | .binary ``Parser.orelse p1 p2 =>
    let p1' ← parserDescrHasAtom atom p1
    let p2' ← parserDescrHasAtom atom p2
    match p1', p2' with
    | some x, some y => pure <| some (.binary ``Parser.orelse x y)
    | some _, none => pure p1'
    | none, some _ => pure p2'
    | none, none => pure none
  | _ => pure none

private def parserDescrStartsWithAtoms (atoms : List String) (p : ParserDescr) : TermElabM Bool := do
  match atoms with
  | [] => pure true
  | a :: as =>
    if let some p' ← parserDescrStartsWithAtom a p then
      parserDescrStartsWithAtoms as p'
    else pure false

private partial def parserDescrHasAtoms (atoms : List String) (p : ParserDescr) : TermElabM Bool := do
  match atoms with
  | [] => pure true
  | a :: as =>
    if let some p' ← parserDescrHasAtom a p then
      if ← parserDescrStartsWithAtoms as p' then pure true
      else parserDescrHasAtoms (a :: as) p'
    else pure false

private unsafe def parserDescrNameHasAtomsUnsafe (atoms : List String) (p : Name) : TermElabM Bool := do
  try
    let p ← evalConstCheck ParserDescr ``ParserDescr p
    parserDescrHasAtoms atoms p
  catch | _ => pure false

@[implemented_by parserDescrNameHasAtomsUnsafe]
private opaque parserDescrNameHasAtoms (atoms : List String) (p : Name) : TermElabM Bool

private def kindHasAtoms (k : Name) (atoms : List String) : TermElabM Bool := do
  let env ← getEnv
  if let some ci := env.find? k then
    if let some d := ci.value? then
      if (← exprContainsAtoms d atoms) then
        return true
    else if ci.type == .const ``Parser [] then
      if (← namedParserHasAtomPrefix atoms k) then
        return true
    else if ci.type == .const ``ParserDescr [] then
      if (← parserDescrNameHasAtoms atoms k) then
        return true
  return false

private def withAtoms (cat : Name) (atoms : List String) : TermElabM (Array Name) := do
  let env ← getEnv
  let some catContents := (Lean.Parser.parserExtension.getState env).categories.find? cat
    | return #[]
  let kinds := catContents.kinds
  let mut found := #[]
  for (k, _) in kinds do
    if (← kindHasAtoms k atoms) then
      found := found.push k
  return found

private def kwImpl (cat : Ident := mkIdent .anonymous) (of : Ident := mkIdent .anonymous)
    (suggest : Bool)
    (s : StrLit) : TermElabM (Inline ElabInline) := do
  let atoms := s.getString |>.split Char.isWhitespace |>.toStringList
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  let cat' := cat.getId
  let of' ← do
    let x := of.getId
    if x.isAnonymous then pure x else realizeGlobalConstNoOverloadWithInfo of
  let cats ←
    if cat'.isAnonymous then
      pure parsers.categories.toArray
    else
      if let some catImpl := parsers.categories.find? cat' then
        pure #[(cat', catImpl)]
      else throwError m!"Syntax category `{cat'}` not found"

  let mut candidates := #[]
  for (catName, category) in cats do
    if !of'.isAnonymous then
      if category.kinds.contains of' then
        if (← kindHasAtoms of' atoms) then
          candidates := candidates.push (catName, of')
    else
      let which ← withAtoms catName atoms
      candidates := candidates ++ (which.map (catName, ·))

  if h : candidates.size = 0 then
    logErrorAt s m!"No syntax found with atoms `{" ".intercalate atoms}`"
    return .code <| " ".intercalate atoms
  else if h : candidates.size > 1 then
    let choices := .andList (candidates.map (fun (c, k) => m!"{.ofConstName k} : {c}")).toList
    let catSuggs := categorySuggestions cat' candidates
    let ofSuggs ← ofSuggestions of' candidates
    let hintText :=
      if catSuggs.isEmpty then
        if ofSuggs.isEmpty then m!""
        else m!"Specify the syntax kind:"
      else
        if ofSuggs.isEmpty then m!"Specify the category:"
        else m!"Specify the category or syntax kind:"

    let range? :=
      match ← getRef with
      | `(inline|role{$name $args*}[$_]) =>
        (mkNullNode (#[name] ++ args)).getRange?
      | _ => none

    let hint ← makeHint hintText (ofSuggs ++ catSuggs)

    logErrorAt s m!"Multiple syntax entries found with atoms `{" ".intercalate atoms}`: {choices}{hint.getD m!""}"
    return .code s.getString
  else
    let (catName, k) := candidates[0]
    addConstInfo s k
    if of'.isAnonymous && suggest then
      let k' ← unresolveNameGlobalAvoidingLocals k
      if let some h ← makeHint m!"Specify the syntax kind:" #[s!" (of := {k'})"] then
        logInfo h

    return .other {name := ``Data.Atom, val := .mk (Data.Atom.mk k catName)} #[.code s.getString]
where
  categorySuggestions (c candidates) := Id.run do
    if c.isAnonymous then
      let mut counts : NameMap Nat := {}
      for (cat, _) in candidates do
        counts := counts.alter cat (some <| 1 + ·.getD 0)
      counts := counts.filter fun _ n => n == 1
      let sorted := counts.keys.toArray.qsort (fun x y => x.toString < y.toString)
      return sorted.map (s!" (cat := {·})")
    else return #[]
  ofSuggestions (o candidates) : TermElabM (Array String):= do
    if o.isAnonymous then
      let sorted := candidates |>.map (·.2) |>.qsort (fun x y => x.toString < y.toString)
      sorted.mapM fun k => do
        let k ← unresolveNameGlobalAvoidingLocals k
        pure s!" (of := {k})"
    else return #[]
  makeHint (hintText) (suggestions : Array String) : TermElabM (Option MessageData) := do
    let range? :=
      match ← getRef with
      | `(inline|role{$name $args*}[$_]) =>
        (mkNullNode (#[name] ++ args)).getRange?
      | _ => none
    if let some ⟨b, e⟩ := range? then
      let str := String.Pos.Raw.extract (← getFileMap).source b e
      let str := if str.startsWith "kw?" then "kw" ++ str.drop 3 else str
      let stx := Syntax.mkStrLit str (info := .synthetic b e (canonical := true))
      let suggs := suggestions.map (fun (s : String) => {suggestion := str ++ s})
      some <$> MessageData.hint hintText suggs (ref? := some stx)
    else pure none

/--
A reference to a particular syntax kind, via one of its atoms.

It is an error if the syntax kind can't be automatically determined to contain the atom, or if
multiple syntax kinds contain it. If the parser for the syntax kind is sufficiently complex,
detection may fail.

Specifying the category or kind using the named arguments `cat` and `of` can narrow down the
process.

Use `kw?` to receive a suggestion of a specific kind, and `kw!` to disable the check.
-/
@[builtin_doc_role]
public def kw (cat : Ident := mkIdent .anonymous) (of : Ident := mkIdent .anonymous)
    (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  kwImpl (cat := cat) (of := of) false s

@[inherit_doc kw, builtin_doc_role]
public def kw? (cat : Ident := mkIdent .anonymous) (of : Ident := mkIdent .anonymous)
    (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  kwImpl (cat := cat) (of := of) true s

/--
Checks that a syntax kind name exists.
-/
public meta def checkKindExists : PostponedCheckHandler := fun _ info => do
  let some k := info.get? PostponedKind
    | throwError "Expected a `{.ofConstName ``PostponedKind}` but got a `{.ofConstName info.typeName}`"
  let k ← realizeGlobalConstNoOverload (mkIdent k.name)
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  unless parsers.kinds.contains k do
    throwError m!"Not a syntax kind: `{.ofConstName k}`"


@[inherit_doc kw, builtin_doc_role]
public def kw! (of : Option Ident := none) (scope : DocScope := .local)
    (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let some of' := of
    | let h ←
        if let `(inline|role{$n $_*}[$_*]) ← getRef then
          let kwName ← unresolveNameGlobalAvoidingLocals ``kw
          let kw?Name ← unresolveNameGlobalAvoidingLocals ``kw?
          let ss := #[
            { suggestion := s!"{kwName}",
              postInfo? := some "for automatic resolution" },
            { suggestion := s!"{kw?Name}",
              postInfo? := some "for automatic resolution with suggestions" }
          ]
          m!"Use one of the other keyword roles.".hint ss (ref? := n)
        else pure m!""
      logErrorAt s m!"No syntax kind specified. The named argument `of` is required for \
        `{.ofConstName `Lean.Doc.kw!}`.{h}"
      return .code s.getString
  match scope with
  | .local =>
    let k ← realizeGlobalConstNoOverloadWithInfo of'
    let env ← getEnv
    let parsers := Lean.Parser.parserExtension.getState env
    unless parsers.kinds.contains k do
      logErrorAt s m!"Not a syntax kind: `{.ofConstName k}`"
  | .import xs =>
    let postponed : PostponedCheck := {handler := ``checkKindExists, imports := xs.map (⟨·⟩), info := .mk (PostponedKind.mk of'.getId)}
    return .other {name := ``PostponedCheck, val := .mk postponed } #[.code s.getString]

  pure <| .code s.getString

/--
Suggests the `kw` role, if applicable.
-/
@[builtin_doc_code_suggestions]
public def suggestKw (code : StrLit) : DocM (Array CodeSuggestion) := do
  let atoms := code.getString |>.split Char.isWhitespace |>.toStringList
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  let cats := parsers.categories.toArray

  let mut candidates := #[]
  for (catName, _) in cats do
    let which ← withAtoms catName atoms
    candidates := candidates ++ (which.map (catName, ·))

  candidates.mapM fun (cat, of) => do
    return .mk ``kw (some s!"(of := {of})") (some s!"(in `{cat}`)")
