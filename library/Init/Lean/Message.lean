/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura

Message Type used by the Lean frontend
-/
prelude
import Init.Data.ToString
import Init.Lean.Position
import Init.Lean.Syntax
import Init.Lean.MetavarContext
import Init.Lean.Environment

namespace Lean
def mkErrorStringWithPos (fileName : String) (line col : Nat) (msg : String) : String :=
fileName ++ ":" ++ toString line ++ ":" ++ toString col ++ " " ++ toString msg

inductive MessageSeverity
| information | warning | error

/- Structure message data. We use it for reporting errors, trace messages, etc. -/
inductive MessageData
| ofFormat : Format → MessageData
| ofSyntax : Syntax → MessageData
| ofExpr   : Expr → MessageData
| ofLevel  : Level → MessageData
/- `context env mctx lctx d` specifies the pretty printing context `(env, mctx, lctx)` for the nested expressions in `d`. -/
| context  : Environment → MetavarContext → LocalContext → MessageData → MessageData
/- Lifted `Format.nest` -/
| nest     : Nat → MessageData → MessageData
/- Lifted `Format.group` -/
| group    : MessageData → MessageData
/- Lifted `Format.compose` -/
| compose  : MessageData → MessageData → MessageData
/- Tagged sections. `Name` should be viewed as a "kind", and is used by `MessageData` inspector functions.
   Example: an inspector that tries to find "definitional equality failures" may look for the tag "DefEqFailure". -/
| tagged   : Name → MessageData → MessageData
| node     : Array MessageData → MessageData

namespace MessageData

instance : Inhabited MessageData := ⟨MessageData.ofFormat (default _)⟩

partial def formatAux : Option (Environment × MetavarContext × LocalContext) → MessageData → Format
| _, ofFormat fmt                  => fmt
| _, ofSyntax s                    => s.formatStx
| _, ofLevel u                     => fmt u
| none, ofExpr e                   => "<expr>"
| some (env, mctx, lctx), ofExpr e => "<expr>" -- TODO: invoke pretty printer
| _, context env mctx lctx d       => formatAux (some (env, mctx, lctx)) d
| ctx, tagged cls d                => Format.sbracket (format cls) ++ " " ++ Format.nest 2 (formatAux ctx d)
| ctx, nest n d                    => Format.nest n (formatAux ctx d)
| ctx, compose d₁ d₂               => formatAux ctx d₁ ++ formatAux ctx d₂
| ctx, group d                     => Format.group (formatAux ctx d)
| ctx, node ds                     => ds.foldl (fun r d => r ++ Format.line ++ formatAux ctx d) Format.nil

instance : HasAppend MessageData := ⟨compose⟩

instance : HasFormat MessageData := ⟨fun d => formatAux none d⟩

instance : HasCoe String MessageData := ⟨fun s => ofFormat s⟩

end MessageData

structure Message :=
(fileName : String)
(pos      : Position)
(endPos   : Option Position := none)
(severity : MessageSeverity := MessageSeverity.error)
(caption  : String          := "")
(data     : MessageData)

namespace Message

protected def toString (msg : Message) : String :=
mkErrorStringWithPos msg.fileName msg.pos.line msg.pos.column
 ((match msg.severity with
   | MessageSeverity.information => ""
   | MessageSeverity.warning => "warning: "
   | MessageSeverity.error => "error: ") ++
  (if msg.caption == "" then "" else msg.caption ++ ":\n") ++ toString (fmt msg.data))

instance : Inhabited Message :=
⟨{ fileName := "", pos := ⟨0, 1⟩, data := default _}⟩

instance : HasToString Message :=
⟨Message.toString⟩
end Message

structure MessageLog :=
-- messages are stored in reverse for efficient append
(revList : List Message := [])

namespace MessageLog
def empty : MessageLog := ⟨{}⟩

def isEmpty (log : MessageLog) : Bool :=
log.revList.isEmpty

instance : Inhabited MessageLog := ⟨{}⟩

def add (msg : Message) (log : MessageLog) : MessageLog :=
⟨msg :: log.revList⟩

protected def append (l₁ l₂ : MessageLog) : MessageLog :=
⟨l₂.revList ++ l₁.revList⟩

instance : HasAppend MessageLog :=
⟨MessageLog.append⟩

def hasErrors (log : MessageLog) : Bool :=
log.revList.any $ fun m => match m.severity with
| MessageSeverity.error => true
| _                     => false

def toList (log : MessageLog) : List Message :=
log.revList.reverse
end MessageLog
end Lean
