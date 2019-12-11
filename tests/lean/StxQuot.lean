import Init.Lean

namespace Lean
open Lean.Elab

def run : Unhygienic Syntax → String := toString ∘ Unhygienic.run

#eval run `(Nat.one)
#eval run `(1 + 1)
#eval run $ do a ← `(Nat.one); `(%%a)
#eval run $ do a ← `(Nat.one); `(f %%(id a))

end Lean
