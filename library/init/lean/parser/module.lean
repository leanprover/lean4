/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level parsers
-/
prelude
import init.lean.parser.command

namespace lean
namespace parser

open combinators monadParsec
open parser.hasTokens parser.hasView

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

structure moduleParserConfig extends commandParserConfig :=
(commandParsers : tokenMap commandParser)

instance moduleParserConfigCoe : hasCoe moduleParserConfig commandParserConfig :=
⟨moduleParserConfig.toCommandParserConfig⟩

section
@[derive monad alternative monadReader monadState monadParsec monadExcept]
def moduleParserM := stateT parserState $ parserT moduleParserConfig id
abbrev moduleParser := moduleParserM syntax
end

instance moduleParserM.liftParserT (ρ : Type) [hasLiftT moduleParserConfig ρ] :
  hasMonadLift (parserT ρ id) moduleParserM :=
{ monadLift := λ α x st cfg, (λ a, (a, st)) <$> x.run ↑cfg }

section
local attribute [reducible] basicParserM
instance moduleParserM.basicParserM (ρ : Type) [hasLiftT moduleParserConfig ρ] :
  hasMonadLift basicParserM moduleParserM :=
  inferInstance
end

namespace module
@[derive parser.hasView parser.hasTokens]
def prelude.parser : basicParser :=
node! «prelude» ["prelude"]

@[derive parser.hasView parser.hasTokens]
def importPath.parser : basicParser :=
-- use `raw` to ignore registered tokens like ".."
node! importPath [
  dirups: (rawStr ".")*,
  module: ident.parser]

@[derive parser.hasView parser.hasTokens]
def import.parser : basicParser :=
node! «import» ["import", imports: importPath.parser+]

@[derive parser.hasView parser.hasTokens]
def header.parser : basicParser :=
node! «header» [«prelude»: prelude.parser?, imports: import.parser*]

@[pattern] def eoi : syntaxNodeKind := ⟨`lean.parser.module.eoi⟩

def eoi.parser : moduleParser := do
  monadParsec.eoi,
  it ← leftOver,
  -- add `eoi` node for left-over input
  let stop := it.toEnd,
  pure $ syntax.mkNode eoi [syntax.atom ⟨some ⟨⟨stop, stop⟩, stop.offset, ⟨stop, stop⟩⟩, ""⟩]

/-- Read command, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def commandWrecAux : bool → nat → moduleParserM (bool × syntax)
| recovering 0            := error "unreachable"
| recovering (nat.succ n) := do
  -- terminate at EOF
  nat.succ _ ← remaining | (prod.mk ff) <$> eoi.parser,
  (recovering, c) ← catch (do {
    cfg ← read,
    c ← monadLift $ command.parser.run cfg.commandParsers,
    pure (ff, some c)
  } <|> do {
    -- unknown command: try to skip token, or else single character
    when (¬ recovering) $ do {
      it ← leftOver,
      logMessage {expected := dlist.singleton "command", it := it, custom := some ()}
    },
    try (monadLift token *> pure ()) <|> (any *> pure ()),
    pure (tt, none)
  }) $ λ msg, do {
    -- error inside command: log error, return partial syntax tree
    logMessage msg,
    pure (tt, some msg.custom.get)
  },
  /- NOTE: We need to make very sure that these recursive calls are happening in tail positions.
     Otherwise, resuming the coroutine is linear in the number of previous commands. -/
  match c with
  | some c := pure (recovering, c)
  | none   := commandWrecAux recovering n

def parseCommandWithRecovery (recovering : bool) :=
do { rem ← remaining, commandWrecAux recovering rem.succ }
end module
open module

structure moduleParserSnapshot :=
-- it there was a parse error in the previous command, we shouldn't complain if parsing immediately after it
-- fails as well
(recovering : bool)
(it : string.iterator)

-- return (partial) syntax tree and single fatal or multiple non-fatal messages
def resumeModuleParser {α : Type} (cfg : moduleParserConfig) (snap : moduleParserSnapshot) (mkRes : α → syntax × moduleParserSnapshot)
  (p : moduleParserM α) : syntax × except message (moduleParserSnapshot × messageLog) :=
let (r, _) := ((((prod.mk <$> p <*> leftOver).run {messages:=messageLog.empty}).run cfg).runFrom snap.it).run {} in
match r with
| except.ok ((a, it), st) := let (stx, snap) := mkRes a in (stx, except.ok ({snap with it := it}, st.messages))
| except.error msg  := (msg.custom.get, except.error $ messageOfParsecMessage cfg msg)

def parseHeader (cfg : moduleParserConfig) :=
let snap := {moduleParserSnapshot . recovering := ff, it := cfg.input.mkIterator} in
resumeModuleParser cfg snap (λ stx, (stx, snap)) $ do
  -- `token` assumes that there is no leading whitespace
  monadLift whitespace,
  monadLift header.parser

def parseCommand (cfg) (snap) := resumeModuleParser cfg snap (λ p, (prod.snd p, {snap with recovering := prod.fst p}))
  (parseCommandWithRecovery snap.recovering)

end parser
end lean
