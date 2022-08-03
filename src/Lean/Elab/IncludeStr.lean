/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Xubai Wang, Wojciech Nawrocki
-/

import Lean.Elab.Term
import Lean.Elab.Eval

namespace Lean.Elab.Term

private unsafe def evalFilePathUnsafe (stx : Syntax) : TermElabM System.FilePath :=
  evalTerm System.FilePath (Lean.mkConst ``System.FilePath) stx

@[implementedBy evalFilePathUnsafe]
private opaque evalFilePath (stx : Syntax) : TermElabM System.FilePath

/-- When `parent_dir` contains the current Lean file, `include_str "path" / "to" / "file"` becomes
a string literal with the contents of the file at `"parent_dir" / "path" / "to" / "file"`. If this
file cannot be read, elaboration fails. -/
elab (name := includeStr) "include_str " path:term : term => do
  let path ← evalFilePath path
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  let path := srcDir / path
  Lean.mkStrLit <$> IO.FS.readFile path

end Lean.Elab.Term
