import Lean.Data.Position
import Lean.Expr
import Lean.Message
import Lean.Data.Json

namespace Lean.Elab

open Std (PersistentArray PersistentArray.empty)

/-- A (go-to-def clickable) link to a source module -/
structure SrcLink where
  modName : Name := `MyMod
  srcPos : String.Pos := 0
  srcEndPos : String.Pos := 0
  deriving Inhabited

/-- An elaborated term -/
structure TermInfo where
  /- Elaboratad expression -/
  e : Expr
  stx : Syntax
  srcLink? : Option SrcLink := none
  deriving Inhabited

structure TacticState

structure MacroExpansionInfo

/-- Tree of semantic information about a term or command.
See `MessageData` for a similar type used for messages. -/
inductive InfoTree
  | ofTermInfo (i : TermInfo)
  -- NOTE(WN): perhaps withContext carries the same information and this is redundant?
  | ofTacticState (s : TacticState)
  | ofJson (j : Json) -- For user data
  | withContext (ctx : MessageDataContext) (t : InfoTree)
  | withNamingContext (nctx : NamingContext) (t : InfoTree)
  | withMacro (m : MacroExpansionInfo) (t : InfoTree)
  | node (k : SyntaxNodeKind) (args : PersistentArray InfoTree)
  deriving Inhabited

namespace InfoTree

open MessageData in
partial def formatAux : NamingContext → Option MessageDataContext → InfoTree → IO Format
  | nCtx, some ctx, ofTermInfo i              => ppExpr (mkPPContext nCtx ctx) i.e
  | nCtx, none,     ofTermInfo i              => pure s!"({i.e})"
  | _,    _,        ofTacticState ..          => pure "⊢"
  | _,    _,        ofJson j                  => pure <| toString j
  | nCtx, _,        withContext ctx d         => formatAux nCtx ctx d
  | _,    ctx?,     withNamingContext nCtx d  => formatAux nCtx ctx? d
  | nCtx, ctx?,     withMacro m t             => do let t ← formatAux nCtx ctx? t; pure s!"(withMacro (..) {t})"
  | nCtx, ctx,      node k args               => do
    let ts ← Format.nest 2 <$> args.foldlM (fun r t => do let t ← formatAux nCtx ctx t; pure $ r ++ Format.line ++ t) Format.nil
    return (toString k) ++ Format.line ++ ts

protected def format (t : InfoTree) : IO Format :=
  formatAux { currNamespace := Name.anonymous, openDecls := [] } none t

protected def toString (t : InfoTree) : IO String := do
  let fmt ← t.format
  pure $ toString fmt

end InfoTree

structure InfoState where
  enabled : Bool := true
  trees : PersistentArray InfoTree := {} -- NOTE(WN): Just a flat array in this experiment
  deriving Inhabited

class MonadInfoTree (m : Type → Type)  where
  getInfoState    : m InfoState
  modifyInfoState : (InfoState → InfoState) → m Unit

export MonadInfoTree (getInfoState modifyInfoState)

instance (m n) [MonadInfoTree m] [MonadLift m n] : MonadInfoTree n where
  getInfoState      := liftM (getInfoState : m _)
  modifyInfoState f := liftM (modifyInfoState f : m _)

section
variables [Monad m] [MonadInfoTree m]

def modifyInfoTrees (f : PersistentArray InfoTree → PersistentArray InfoTree)
  : m Unit :=
  modifyInfoState (fun s => { s with trees := f s.trees })

def pushInfoTree (t : InfoTree) : m Unit := do
  if (←getInfoState).enabled then
    modifyInfoTrees (fun ts => ts.push t)
  pure ()

def mkInfoNode (k : SyntaxNodeKind) : m Unit := do
  if (←getInfoState).enabled then
    modifyInfoTrees (fun ts => PersistentArray.empty.push <| InfoTree.node k ts)
end

end Lean.Elab