import Lean.Data.Position
import Lean.Data.Lsp

namespace Lean
namespace Server

def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
let start := text.lspPosToUtf8Pos r.start;
let «end» := text.lspPosToUtf8Pos r.«end»;
let pre := text.source.extract 0 start;
let post := text.source.extract «end» text.source.bsize;
(pre ++ newText ++ post).toFileMap

-- TODO(WN): should these instances be in Core?
instance Thunk.monad : Monad Thunk :=
{ pure := @Thunk.pure,
  bind := @Thunk.bind }

end Server
end Lean
