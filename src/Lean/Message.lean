/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura

Message Type used by the Lean frontend
-/
import Lean.Data.Position
import Lean.Data.OpenDecl
import Lean.Syntax
import Lean.MetavarContext
import Lean.Environment
import Lean.Util.PPExt

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
  env : Environment
  mctx : MetavarContext
  lctx : LocalContext
  opts : Options

structure NamingContext where
  currNamespace : Name
  openDecls : List OpenDecl

/- Structure message data. We use it for reporting errors, trace messages, etc. -/
inductive MessageData where
  | ofFormat          : Format → MessageData
  | ofSyntax          : Syntax → MessageData
  | ofExpr            : Expr → MessageData
  | ofLevel           : Level → MessageData
  | ofName            : Name  → MessageData
  | ofGoal            : MVarId → MessageData
  /- `withContext ctx d` specifies the pretty printing context `(env, mctx, lctx, opts)` for the nested expressions in `d`. -/
  | withContext       : MessageDataContext → MessageData → MessageData
  | withNamingContext : NamingContext → MessageData → MessageData
  /- Lifted `Format.nest` -/
  | nest              : Nat → MessageData → MessageData
  /- Lifted `Format.group` -/
  | group             : MessageData → MessageData
  /- Lifted `Format.compose` -/
  | compose           : MessageData → MessageData → MessageData
  /- Tagged sections. `Name` should be viewed as a "kind", and is used by `MessageData` inspector functions.
     Example: an inspector that tries to find "definitional equality failures" may look for the tag "DefEqFailure". -/
  | tagged            : Name → MessageData → MessageData
  | node              : Array MessageData → MessageData
  deriving Inhabited

namespace MessageData

/- Instantiate metavariables occurring in nexted `ofExpr` constructors.
   It uses the surrounding `MetavarContext` at `withContext` constructors.
-/
partial def instantiateMVars (msg : MessageData) : MessageData :=
  visit msg {}
where
  visit (msg : MessageData) (mctx : MetavarContext) : MessageData :=
    match msg with
    | ofExpr e                  => ofExpr <| mctx.instantiateMVars e |>.1
    | withContext ctx msg       => withContext ctx  <| visit msg ctx.mctx
    | withNamingContext ctx msg => withNamingContext ctx <| visit msg mctx
    | nest n msg                => nest n <| visit msg mctx
    | group msg                 => group <| visit msg mctx
    | compose msg₁ msg₂         => compose (visit msg₁ mctx) <| visit msg₂ mctx
    | tagged n msg              => tagged n <| visit msg mctx
    | node msgs                 => node <| msgs.map (visit . mctx)
    | _                         => msg

variable (tag : Name) in
partial def hasTag : MessageData → Bool
  | withContext _ msg       => hasTag msg
  | withNamingContext _ msg => hasTag msg
  | nest _ msg              => hasTag msg
  | group msg               => hasTag msg
  | compose msg₁ msg₂       => hasTag msg₁ || hasTag msg₂
  | tagged n msg            => tag == n || hasTag msg
  | node msgs               => msgs.any hasTag
  | _                       => false

def nil : MessageData :=
  ofFormat Format.nil

def isNil : MessageData → Bool
  | ofFormat Format.nil => true
  | _                   => false

def isNest : MessageData → Bool
  | nest _ _ => true
  | _        => false

def mkPPContext (nCtx : NamingContext) (ctx : MessageDataContext) : PPContext := {
  env := ctx.env, mctx := ctx.mctx, lctx := ctx.lctx, opts := ctx.opts,
  currNamespace := nCtx.currNamespace, openDecls := nCtx.openDecls
}

partial def formatAux : NamingContext → Option MessageDataContext → MessageData → IO Format
  | _,    _,         ofFormat fmt             => pure fmt
  | _,    _,         ofLevel u                => pure $ format u
  | _,    _,         ofName n                 => pure $ format n
  | nCtx, some ctx,  ofSyntax s               => ppTerm (mkPPContext nCtx ctx) s  -- HACK: might not be a term
  | _,    none,      ofSyntax s               => pure $ s.formatStx
  | _,    none,      ofExpr e                 => pure $ format (toString e)
  | nCtx, some ctx,  ofExpr e                 => ppExpr (mkPPContext nCtx ctx) e
  | _,    none,      ofGoal mvarId            => pure $ "goal " ++ format (mkMVar mvarId)
  | nCtx, some ctx,  ofGoal mvarId            => ppGoal (mkPPContext nCtx ctx) mvarId
  | nCtx, _,         withContext ctx d        => formatAux nCtx ctx d
  | _,    ctx,       withNamingContext nCtx d => formatAux nCtx ctx d
  | nCtx, ctx,       tagged t d               =>
    /- Messages starting a trace context have their tags postfixed with `_traceCtx` so that
    we can detect them later. Here, we do so in order to print the trace context class. -/
    if let Name.str cls "_traceCtx" _ := t then do
      let d₁ ← formatAux nCtx ctx d
      return f!"[{cls}] {d₁}"
    else
      formatAux nCtx ctx d
  | nCtx, ctx,       nest n d                 => Format.nest n <$> formatAux nCtx ctx d
  | nCtx, ctx,       compose d₁ d₂            => do let d₁ ← formatAux nCtx ctx d₁; let d₂ ← formatAux nCtx ctx d₂; pure $ d₁ ++ d₂
  | nCtx, ctx,       group d                  => Format.group <$> formatAux nCtx ctx d
  | nCtx, ctx,       node ds                  => Format.nest 2 <$> ds.foldlM (fun r d => do let d ← formatAux nCtx ctx d; pure $ r ++ Format.line ++ d) Format.nil

protected def format (msgData : MessageData) : IO Format :=
  formatAux { currNamespace := Name.anonymous, openDecls := [] } none msgData

protected def toString (msgData : MessageData) : IO String := do
  let fmt ← msgData.format
  pure $ toString fmt

instance : Append MessageData := ⟨compose⟩

instance : Coe String MessageData := ⟨ofFormat ∘ format⟩
instance : Coe Format MessageData := ⟨ofFormat⟩
instance : Coe Level MessageData  := ⟨ofLevel⟩
instance : Coe Expr MessageData   := ⟨ofExpr⟩
instance : Coe Name MessageData   := ⟨ofName⟩
instance : Coe Syntax MessageData := ⟨ofSyntax⟩
instance : Coe (Option Expr) MessageData := ⟨fun o => match o with | none => "none" | some e => ofExpr e⟩

partial def arrayExpr.toMessageData (es : Array Expr) (i : Nat) (acc : MessageData) : MessageData :=
  if h : i < es.size then
    let e   := es.get ⟨i, h⟩;
    let acc := if i == 0 then acc ++ ofExpr e else acc ++ ", " ++ ofExpr e;
    toMessageData es (i+1) acc
  else
    acc ++ "]"

instance : Coe (Array Expr) MessageData := ⟨fun es => arrayExpr.toMessageData es 0 "#["⟩

def bracket (l : String) (f : MessageData) (r : String) : MessageData := group (nest l.length $ l ++ f ++ r)
def paren (f : MessageData) : MessageData := bracket "(" f ")"
def sbracket (f : MessageData) : MessageData := bracket "[" f "]"
def joinSep : List MessageData → MessageData → MessageData
  | [],    sep => Format.nil
  | [a],   sep => a
  | a::as, sep => a ++ sep ++ joinSep as sep
def ofList: List MessageData → MessageData
  | [] => "[]"
  | xs => sbracket $ joinSep xs (ofFormat "," ++ Format.line)
def ofArray (msgs : Array MessageData) : MessageData :=
  ofList msgs.toList

instance : Coe (List MessageData) MessageData := ⟨ofList⟩
instance : Coe (List Expr) MessageData := ⟨fun es => ofList $ es.map ofExpr⟩

end MessageData

structure Message where
  fileName : String
  pos      : Position
  endPos   : Option Position := none
  severity : MessageSeverity := MessageSeverity.error
  caption  : String          := ""
  data     : MessageData
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

structure MessageLog where
  msgs : Std.PersistentArray Message := {}
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
  pure $ MessageData.withContext { env := env, mctx := {}, lctx := {}, opts := opts } msgData

def addMessageContextFull {m} [Monad m] [MonadEnv m] [MonadMCtx m] [MonadLCtx m] [MonadOptions m] (msgData : MessageData) : m MessageData := do
  let env ← getEnv
  let mctx ← getMCtx
  let lctx ← getLCtx
  let opts ← getOptions
  pure $ MessageData.withContext { env := env, mctx := mctx, lctx := lctx, opts := opts } msgData

class ToMessageData (α : Type) where
  toMessageData : α → MessageData

export ToMessageData (toMessageData)

def stringToMessageData (str : String) : MessageData :=
  let lines := str.split (· == '\n')
  let lines := lines.map (MessageData.ofFormat ∘ format)
  MessageData.joinSep lines (MessageData.ofFormat Format.line)

instance {α} [ToFormat α] : ToMessageData α := ⟨MessageData.ofFormat ∘ format⟩
instance : ToMessageData Expr          := ⟨MessageData.ofExpr⟩
instance : ToMessageData Level         := ⟨MessageData.ofLevel⟩
instance : ToMessageData Name          := ⟨MessageData.ofName⟩
instance : ToMessageData String        := ⟨stringToMessageData⟩
instance : ToMessageData Syntax        := ⟨MessageData.ofSyntax⟩
instance : ToMessageData Format        := ⟨MessageData.ofFormat⟩
instance : ToMessageData MessageData   := ⟨id⟩
instance {α} [ToMessageData α] : ToMessageData (List α)  := ⟨fun as => MessageData.ofList $ as.map toMessageData⟩
instance {α} [ToMessageData α] : ToMessageData (Array α) := ⟨fun as => toMessageData as.toList⟩
instance {α} [ToMessageData α] : ToMessageData (Subarray α) := ⟨fun as => toMessageData as.toArray.toList⟩
instance {α} [ToMessageData α] : ToMessageData (Option α) := ⟨fun | none => "none" | some e => "some (" ++ toMessageData e ++ ")"⟩
instance : ToMessageData (Option Expr) := ⟨fun | none => "<not-available>" | some e => toMessageData e⟩

syntax:max "m!" interpolatedStr(term) : term

macro_rules
  | `(m! $interpStr) => do interpStr.expandInterpolatedStr (← `(MessageData)) (← `(toMessageData))


namespace KernelException

private def mkCtx (env : Environment) (lctx : LocalContext) (opts : Options) (msg : MessageData) : MessageData :=
  MessageData.withContext { env := env, mctx := {}, lctx := lctx, opts := opts } msg

def toMessageData (e : KernelException) (opts : Options) : MessageData :=
  match e with
  | unknownConstant env constName       => mkCtx env {} opts m!"(kernel) unknown constant '{constName}'"
  | alreadyDeclared env constName       => mkCtx env {} opts m!"(kernel) constant has already been declared '{constName}'"
  | declTypeMismatch env decl givenType =>
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

end KernelException
end Lean
