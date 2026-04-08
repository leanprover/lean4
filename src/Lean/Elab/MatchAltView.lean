/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.Term

public section

namespace Lean.Elab.Term

/-! This module assumes `match`-expressions use the following syntax.

```lean
def matchDiscr := leading_parser optional (try (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> termParser

def «match» := leading_parser:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
```
-/

structure MatchAltView (k : SyntaxNodeKinds) where
  ref      : Syntax
  patterns : Array Syntax
  lhs      : Syntax
  rhs      : TSyntax k
  deriving Inhabited

end Lean.Elab.Term
