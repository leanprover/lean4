/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura

Message type used by the Lean frontend
-/
import Lean.Data.Position
import Lean.Data.OpenDecl
import Lean.MetavarContext
import Lean.Environment
import Lean.Util.PPExt
import Lean.Util.Sorry

namespace Lean

def mkErrorStringWithPos (fileName : String) (pos : Position) (msg : String) (endPos : Option Position := none) : String :=
  let endPos := match endPos with
    | some endPos => s!"-{endPos.line}:{endPos.column}"
    | none        => ""
  s!"{fileName}:{pos.line}:{pos.column}{endPos}: {msg}"

inductive MessageSeverity where
  | information | warning | error
  deriving Inhabited, BEq

structure MessageDataContext where
  env  : Environment
  mctx : MetavarContext
  lctx : LocalContext
  opts : Options

/-- A naming context is the information needed to shorten names in pretty printing.

It gives the current namespace and the list of open declarations.
-/
structure NamingContext where
  currNamespace : Name
  openDecls : List OpenDecl

/-- Lazily formatted text to be used in `MessageData`. -/
structure PPFormat where
  /-- Pretty-prints text using surrounding context, if any. -/
  pp : Option PPContext → IO FormatWithInfos
  /-- Searches for synthetic sorries in original input. Used to filter out certain messages. -/
  hasSyntheticSorry : MetavarContext → Bool := fun _ => false

/-- Structured message data. We use it for reporting errors, trace messages, etc. -/
inductive MessageData where
  /-- Eagerly formatted text. We inspect this in various hacks, so it is not immediately subsumed by `ofPPFormat`. -/
  | ofFormat          : Format → MessageData
  /-- Lazily formatted text. -/
  | ofPPFormat        : PPFormat → MessageData
  | ofGoal            : MVarId → MessageData
  /-- `withContext ctx d` specifies the pretty printing context `(env, mctx, lctx, opts)` for the nested expressions in `d`. -/
  | withContext       : MessageDataContext → MessageData → MessageData
  | withNamingContext : NamingContext → MessageData → MessageData
  /-- Lifted `Format.nest` -/
  |  nest              : Nat → MessageData → MessageData
  /-- Lifted `Format.group` -/
  |  group             : MessageData → MessageData
  /-- Lifted `Format.compose` -/
  |  compose           : MessageData → MessageData → MessageData
  /-- Tagged sections. `Name` should be viewed as a "kind", and is used by `MessageData` inspector functions.
    Example: an inspector that tries to find "definitional equality failures" may look for the tag "DefEqFailure". -/
  | tagged            : Name → MessageData → MessageData
  | trace (cls : Name) (msg : MessageData) (children : Array MessageData)
    (collapsed : Bool := false)
  deriving Inhabited

namespace MessageData

/-- Determines whether the message contains any content. -/
def isEmpty : MessageData → Bool
  | ofFormat f => f.isEmpty
  | withContext _ m => m.isEmpty
  | withNamingContext _ m => m.isEmpty
  | nest _ m => m.isEmpty
  | group m => m.isEmpty
  | compose m₁ m₂ => m₁.isEmpty && m₂.isEmpty
  | tagged _ m => m.isEmpty
  | _ => false

variable (p : Name → Bool) in
/-- Returns true when the message contains a `MessageData.tagged tag ..` constructor where `p tag` is true. -/
partial def hasTag : MessageData → Bool
  | withContext _ msg       => hasTag msg
  | withNamingContext _ msg => hasTag msg
  | nest _ msg              => hasTag msg
  | group msg               => hasTag msg
  | compose msg₁ msg₂       => hasTag msg₁ || hasTag msg₂
  | tagged n msg            => p n || hasTag msg
  | trace cls msg msgs _    => p cls || hasTag msg || msgs.any hasTag
  | _                       => false

/-- An empty message. -/
def nil : MessageData :=
  ofFormat Format.nil

def mkPPContext (nCtx : NamingContext) (ctx : MessageDataContext) : PPContext := {
  env := ctx.env, mctx := ctx.mctx, lctx := ctx.lctx, opts := ctx.opts,
  currNamespace := nCtx.currNamespace, openDecls := nCtx.openDecls
}

def ofSyntax (stx : Syntax) : MessageData :=
  -- discard leading/trailing whitespace
  let stx := stx.copyHeadTailInfoFrom .missing
  .ofPPFormat {
    pp := fun
      | some ctx => ppTerm ctx ⟨stx⟩  -- HACK: might not be a term
      | none     => return stx.formatStx
  }

def ofExpr (e : Expr) : MessageData :=
  .ofPPFormat {
    pp := fun
      | some ctx => ppExprWithInfos ctx e
      | none     => return format (toString e)
    hasSyntheticSorry := (instantiateMVarsCore · e |>.1.hasSyntheticSorry)
  }

def ofLevel (l : Level) : MessageData := ofFormat (format l)
def ofName (n : Name) : MessageData := ofFormat (format n)

partial def hasSyntheticSorry (msg : MessageData) : Bool :=
  visit none msg
where
  visit (mctx? : Option MetavarContext) : MessageData → Bool
  | ofPPFormat f            => f.hasSyntheticSorry (mctx?.getD {})
  | withContext ctx msg     => visit ctx.mctx msg
  | withNamingContext _ msg => visit mctx? msg
  | nest _ msg              => visit mctx? msg
  | group msg               => visit mctx? msg
  | compose msg₁ msg₂       => visit mctx? msg₁ || visit mctx? msg₂
  | tagged _ msg            => visit mctx? msg
  | trace _ msg msgs _      => visit mctx? msg || msgs.any (visit mctx?)
  | _                       => false

partial def formatAux : NamingContext → Option MessageDataContext → MessageData → IO Format
  | _,    _,         ofFormat fmt             => return fmt
  | nCtx, ctx?,      ofPPFormat f             => (·.fmt) <$> f.pp (ctx?.map (mkPPContext nCtx))
  | _,    none,      ofGoal mvarId            => return "goal " ++ format (mkMVar mvarId)
  | nCtx, some ctx,  ofGoal mvarId            => ppGoal (mkPPContext nCtx ctx) mvarId
  | nCtx, _,         withContext ctx d        => formatAux nCtx ctx d
  | _,    ctx,       withNamingContext nCtx d => formatAux nCtx ctx d
  | nCtx, ctx,       tagged _ d               => formatAux nCtx ctx d
  | nCtx, ctx,       nest n d                 => Format.nest n <$> formatAux nCtx ctx d
  | nCtx, ctx,       compose d₁ d₂            => return (← formatAux nCtx ctx d₁) ++ (← formatAux nCtx ctx d₂)
  | nCtx, ctx,       group d                  => Format.group <$> formatAux nCtx ctx d
  | nCtx, ctx,       trace cls header children _ => do
    let msg := f!"[{cls}] {(← formatAux nCtx ctx header).nest 2}"
    let children ← children.mapM (formatAux nCtx ctx)
    return .nest 2 (.joinSep (msg::children.toList) "\n")

protected def format (msgData : MessageData) : IO Format :=
  formatAux { currNamespace := Name.anonymous, openDecls := [] } none msgData

protected def toString (msgData : MessageData) : IO String := do
  return toString (← msgData.format)

instance : Append MessageData := ⟨compose⟩

instance : Coe String MessageData := ⟨ofFormat ∘ format⟩
instance : Coe Format MessageData := ⟨ofFormat⟩
instance : Coe Level MessageData  := ⟨ofLevel⟩
instance : Coe Expr MessageData   := ⟨ofExpr⟩
instance : Coe Name MessageData   := ⟨ofName⟩
instance : Coe Syntax MessageData := ⟨ofSyntax⟩
instance : Coe MVarId MessageData := ⟨ofGoal⟩
instance : Coe (Option Expr) MessageData := ⟨fun o => match o with | none => "none" | some e => ofExpr e⟩

partial def arrayExpr.toMessageData (es : Array Expr) (i : Nat) (acc : MessageData) : MessageData :=
  if h : i < es.size then
    let e   := es.get ⟨i, h⟩;
    let acc := if i == 0 then acc ++ ofExpr e else acc ++ ", " ++ ofExpr e;
    toMessageData es (i+1) acc
  else
    acc ++ "]"

instance : Coe (Array Expr) MessageData := ⟨fun es => arrayExpr.toMessageData es 0 "#["⟩

/-- Wrap the given message in `l` and `r`. See also `Format.bracket`.  -/
def bracket (l : String) (f : MessageData) (r : String) : MessageData := group (nest l.length <| l ++ f ++ r)
/-- Wrap the given message in parentheses `()`. -/
def paren (f : MessageData) : MessageData := bracket "(" f ")"
/-- Wrap the given message in square brackets `[]`. -/
def sbracket (f : MessageData) : MessageData := bracket "[" f "]"
/-- Append the given list of messages with the given separator. -/
def joinSep : List MessageData → MessageData → MessageData
  | [],    _   => Format.nil
  | [a],   _   => a
  | a::as, sep => a ++ sep ++ joinSep as sep

/-- Write the given list of messages as a list, separating each item with `,\n` and surrounding with square brackets. -/
def ofList : List MessageData → MessageData
  | [] => "[]"
  | xs => sbracket <| joinSep xs (ofFormat "," ++ Format.line)

/-- See `MessageData.ofList`. -/
def ofArray (msgs : Array MessageData) : MessageData :=
  ofList msgs.toList

instance : Coe (List MessageData) MessageData := ⟨ofList⟩
instance : Coe (List Expr) MessageData := ⟨fun es => ofList <| es.map ofExpr⟩

end MessageData

/-- A `Message` is a richly formatted piece of information emitted by Lean.
They are rendered by client editors in the infoview and in diagnostic windows. -/
structure Message where
  fileName      : String
  pos           : Position
  endPos        : Option Position := none
  /-- If `true`, report range as given; see `msgToInteractiveDiagnostic`. -/
  keepFullRange : Bool := false
  severity      : MessageSeverity := MessageSeverity.error
  caption       : String          := ""
  /-- The content of the message. -/
  data          : MessageData
  deriving Inhabited

namespace Message

protected def toString (msg : Message) (includeEndPos := false) : IO String := do
  let mut str ← msg.data.toString
  let endPos := if includeEndPos then msg.endPos else none
  unless msg.caption == "" do
    str := msg.caption ++ ":\n" ++ str
  match msg.severity with
  | MessageSeverity.information => pure ()
  | MessageSeverity.warning     => str := mkErrorStringWithPos msg.fileName msg.pos (endPos := endPos) "warning: " ++ str
  | MessageSeverity.error       => str := mkErrorStringWithPos msg.fileName msg.pos (endPos := endPos) "error: " ++ str
  if str.isEmpty || str.back != '\n' then
    str := str ++ "\n"
  return str

end Message

/-- A persistent array of messages. -/
structure MessageLog where
  msgs : PersistentArray Message := {}
  deriving Inhabited

namespace MessageLog
def empty : MessageLog := ⟨{}⟩

def isEmpty (log : MessageLog) : Bool :=
  log.msgs.isEmpty

def add (msg : Message) (log : MessageLog) : MessageLog :=
  ⟨log.msgs.push msg⟩

protected def append (l₁ l₂ : MessageLog) : MessageLog :=
  ⟨l₁.msgs ++ l₂.msgs⟩

instance : Append MessageLog :=
  ⟨MessageLog.append⟩

def hasErrors (log : MessageLog) : Bool :=
  log.msgs.any fun m => match m.severity with
    | MessageSeverity.error => true
    | _                     => false

def errorsToWarnings (log : MessageLog) : MessageLog :=
  { msgs := log.msgs.map (fun m => match m.severity with | MessageSeverity.error => { m with severity := MessageSeverity.warning } | _ => m) }

def getInfoMessages (log : MessageLog) : MessageLog :=
  { msgs := log.msgs.filter fun m => match m.severity with | MessageSeverity.information => true | _ => false }

def forM {m : Type → Type} [Monad m] (log : MessageLog) (f : Message → m Unit) : m Unit :=
  log.msgs.forM f

def toList (log : MessageLog) : List Message :=
  (log.msgs.foldl (fun acc msg => msg :: acc) []).reverse

end MessageLog

def MessageData.nestD (msg : MessageData) : MessageData :=
  MessageData.nest 2 msg

def indentD (msg : MessageData) : MessageData :=
  MessageData.nestD (Format.line ++ msg)

def indentExpr (e : Expr) : MessageData :=
  indentD e

class AddMessageContext (m : Type → Type) where
  addMessageContext : MessageData → m MessageData

export AddMessageContext (addMessageContext)

instance (m n) [MonadLift m n] [AddMessageContext m] : AddMessageContext n where
  addMessageContext := fun msg => liftM (addMessageContext msg : m _)

def addMessageContextPartial {m} [Monad m] [MonadEnv m] [MonadOptions m] (msgData : MessageData) : m MessageData := do
  let env ← getEnv
  let opts ← getOptions
  return MessageData.withContext { env := env, mctx := {}, lctx := {}, opts := opts } msgData

def addMessageContextFull {m} [Monad m] [MonadEnv m] [MonadMCtx m] [MonadLCtx m] [MonadOptions m] (msgData : MessageData) : m MessageData := do
  let env ← getEnv
  let mctx ← getMCtx
  let lctx ← getLCtx
  let opts ← getOptions
  return MessageData.withContext { env := env, mctx := mctx, lctx := lctx, opts := opts } msgData

class ToMessageData (α : Type) where
  toMessageData : α → MessageData

export ToMessageData (toMessageData)

def stringToMessageData (str : String) : MessageData :=
  let lines := str.split (· == '\n')
  let lines := lines.map (MessageData.ofFormat ∘ format)
  MessageData.joinSep lines (MessageData.ofFormat Format.line)

instance [ToFormat α] : ToMessageData α := ⟨MessageData.ofFormat ∘ format⟩
instance : ToMessageData Expr          := ⟨MessageData.ofExpr⟩
instance : ToMessageData Level         := ⟨MessageData.ofLevel⟩
instance : ToMessageData Name          := ⟨MessageData.ofName⟩
instance : ToMessageData String        := ⟨stringToMessageData⟩
instance : ToMessageData Syntax        := ⟨MessageData.ofSyntax⟩
instance : ToMessageData (TSyntax k)   := ⟨(MessageData.ofSyntax ·)⟩
instance : ToMessageData Format        := ⟨MessageData.ofFormat⟩
instance : ToMessageData MVarId        := ⟨MessageData.ofGoal⟩
instance : ToMessageData MessageData   := ⟨id⟩
instance [ToMessageData α] : ToMessageData (List α)  := ⟨fun as => MessageData.ofList <| as.map toMessageData⟩
instance [ToMessageData α] : ToMessageData (Array α) := ⟨fun as => toMessageData as.toList⟩
instance [ToMessageData α] : ToMessageData (Subarray α) := ⟨fun as => toMessageData as.toArray.toList⟩
instance [ToMessageData α] : ToMessageData (Option α) := ⟨fun | none => "none" | some e => "some (" ++ toMessageData e ++ ")"⟩
instance [ToMessageData α] [ToMessageData β] : ToMessageData (α × β) :=
  ⟨fun (a, b) => .paren <| toMessageData a ++ "," ++ Format.line ++ toMessageData b⟩
instance : ToMessageData (Option Expr) := ⟨fun | none => "<not-available>" | some e => toMessageData e⟩

syntax:max "m!" interpolatedStr(term) : term

macro_rules
  | `(m! $interpStr) => do interpStr.expandInterpolatedStr (← `(MessageData)) (← `(toMessageData))

def toMessageList (msgs : Array MessageData) : MessageData :=
  indentD (MessageData.joinSep msgs.toList m!"\n\n")

namespace KernelException

private def mkCtx (env : Environment) (lctx : LocalContext) (opts : Options) (msg : MessageData) : MessageData :=
  MessageData.withContext { env := env, mctx := {}, lctx := lctx, opts := opts } msg

def toMessageData (e : KernelException) (opts : Options) : MessageData :=
  match e with
  | unknownConstant env constName       => mkCtx env {} opts m!"(kernel) unknown constant '{constName}'"
  | alreadyDeclared env constName       => mkCtx env {} opts m!"(kernel) constant has already been declared '{constName}'"
  | declTypeMismatch env decl givenType =>
    mkCtx env {} opts <|
    let process (n : Name) (expectedType : Expr) : MessageData :=
      m!"(kernel) declaration type mismatch, '{n}' has type{indentExpr givenType}\nbut it is expected to have type{indentExpr expectedType}";
    match decl with
    | Declaration.defnDecl { name := n, type := type, .. } => process n type
    | Declaration.thmDecl { name := n, type := type, .. }  => process n type
    | _ => "(kernel) declaration type mismatch" -- TODO fix type checker, type mismatch for mutual decls does not have enough information
  | declHasMVars env constName _        => mkCtx env {} opts m!"(kernel) declaration has metavariables '{constName}'"
  | declHasFVars env constName _        => mkCtx env {} opts m!"(kernel) declaration has free variables '{constName}'"
  | funExpected env lctx e              => mkCtx env lctx opts m!"(kernel) function expected{indentExpr e}"
  | typeExpected env lctx e             => mkCtx env lctx opts m!"(kernel) type expected{indentExpr e}"
  | letTypeMismatch  env lctx n _ _     => mkCtx env lctx opts m!"(kernel) let-declaration type mismatch '{n}'"
  | exprTypeMismatch env lctx e _       => mkCtx env lctx opts m!"(kernel) type mismatch at{indentExpr e}"
  | appTypeMismatch  env lctx e fnType argType =>
    mkCtx env lctx opts m!"application type mismatch{indentExpr e}\nargument has type{indentExpr argType}\nbut function has type{indentExpr fnType}"
  | invalidProj env lctx e              => mkCtx env lctx opts m!"(kernel) invalid projection{indentExpr e}"
  | other msg                           => m!"(kernel) {msg}"
  | deterministicTimeout                => "(kernel) deterministic timeout"
  | excessiveMemory                     => "(kernel) excessive memory consumption detected"
  | deepRecursion                       => "(kernel) deep recursion detected"

end KernelException
end Lean
