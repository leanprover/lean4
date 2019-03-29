/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-Level parsers
-/
prelude
import init.lean.parser.command

namespace Lean
namespace Parser

open Combinators MonadParsec
open Parser.HasTokens Parser.HasView

local postfix `?`:10000 := optional
local postfix *:10000 := Combinators.many
local postfix +:10000 := Combinators.many1

structure ModuleParserConfig extends CommandParserConfig :=
(commandParsers : TokenMap commandParser)

instance moduleParserConfigCoe : HasCoe ModuleParserConfig CommandParserConfig :=
⟨ModuleParserConfig.toCommandParserConfig⟩

section
@[derive Monad Alternative MonadReader MonadState MonadParsec MonadExcept]
def ModuleParserM := StateT ParserState $ ParserT ModuleParserConfig Id
abbrev moduleParser := ModuleParserM Syntax
end

instance ModuleParserM.liftParserT (ρ : Type) [HasLiftT ModuleParserConfig ρ] :
  HasMonadLift (ParserT ρ Id) ModuleParserM :=
{ monadLift := λ α x st cfg, (λ a, (a, st)) <$> x.run ↑cfg }

section
local attribute [reducible] BasicParserM
instance ModuleParserM.BasicParserM (ρ : Type) [HasLiftT ModuleParserConfig ρ] :
  HasMonadLift BasicParserM ModuleParserM :=
  inferInstance
end

namespace Module
@[derive Parser.HasView Parser.HasTokens]
def prelude.Parser : basicParser :=
node! «prelude» ["prelude"]

@[derive Parser.HasView Parser.HasTokens]
def importPath.Parser : basicParser :=
-- use `raw` to ignore registered tokens like ".."
node! importPath [
  dirups: (rawStr ".")*,
  Module: ident.Parser]

@[derive Parser.HasView Parser.HasTokens]
def import.Parser : basicParser :=
node! «import» ["import", imports: importPath.Parser+]

@[derive Parser.HasView Parser.HasTokens]
def header.Parser : basicParser :=
node! «header» [«prelude»: prelude.Parser?, imports: import.Parser*]

@[pattern] def eoi : SyntaxNodeKind := ⟨`Lean.Parser.Module.eoi⟩

def eoi.Parser : moduleParser := do
  MonadParsec.eoi,
  it ← leftOver,
  -- add `eoi` Node for left-over input
  let stop := it.toEnd,
  pure $ Syntax.mkNode eoi [Syntax.atom ⟨some ⟨⟨stop, stop⟩, stop.offset, ⟨stop, stop⟩⟩, ""⟩]

/-- Read command, recovering from errors inside commands (attach partial Syntax tree)
    as well as unknown commands (skip input). -/
private def commandWrecAux : Bool → Nat → ModuleParserM (Bool × Syntax)
| recovering 0            := error "unreachable"
| recovering (Nat.succ n) := do
  -- terminate at EOF
  Nat.succ _ ← remaining | (Prod.mk false) <$> eoi.Parser,
  (recovering, c) ← catch (do {
    cfg ← read,
    c ← monadLift $ command.Parser.run cfg.commandParsers,
    pure (false, some c)
  } <|> do {
    -- unknown command: try to skip token, or else single character
    when (¬ recovering) $ do {
      it ← leftOver,
      logMessage {expected := DList.singleton "command", it := it, custom := some ()}
    },
    try (monadLift token *> pure ()) <|> (any *> pure ()),
    pure (true, none)
  }) $ λ msg, do {
    -- error inside command: log error, return partial Syntax tree
    logMessage msg,
    pure (true, some msg.custom.get)
  },
  /- NOTE: We need to make very sure that these recursive calls are happening in tail positions.
     Otherwise, resuming the coroutine is linear in the number of previous commands. -/
  match c with
  | some c := pure (recovering, c)
  | none   := commandWrecAux recovering n

def parseCommandWithRecovery (recovering : Bool) :=
do { rem ← remaining, commandWrecAux recovering rem.succ }
end Module
open Module

structure ModuleParserSnapshot :=
-- it there was a parse error in the previous command, we shouldn't complain if parsing immediately after it
-- fails as well
(recovering : Bool)
(it : String.OldIterator)

-- return (partial) Syntax tree and single fatal or multiple non-fatal messages
def resumeModuleParser {α : Type} (cfg : ModuleParserConfig) (snap : ModuleParserSnapshot) (mkRes : α → Syntax × ModuleParserSnapshot)
  (p : ModuleParserM α) : Syntax × Except Message (ModuleParserSnapshot × MessageLog) :=
let (r, _) := ((((Prod.mk <$> p <*> leftOver).run {messages:=MessageLog.empty}).run cfg).runFrom snap.it).run {} in
match r with
| Except.ok ((a, it), st) := let (stx, snap) := mkRes a in (stx, Except.ok ({snap with it := it}, st.messages))
| Except.error msg  := (msg.custom.get, Except.error $ messageOfParsecMessage cfg msg)

def parseHeader (cfg : ModuleParserConfig) :=
let snap := {ModuleParserSnapshot . recovering := false, it := cfg.input.mkOldIterator} in
resumeModuleParser cfg snap (λ stx, (stx, snap)) $ do
  -- `token` assumes that there is no leading whitespace
  monadLift whitespace,
  monadLift header.Parser

def parseCommand (cfg) (snap) := resumeModuleParser cfg snap (λ p, (Prod.snd p, {snap with recovering := Prod.fst p}))
  (parseCommandWithRecovery snap.recovering)

end Parser
end Lean
