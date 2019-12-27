import Init.Lean

namespace Lean
open Lean.Elab

def run {α} [HasToString α] : Unhygienic α → String := toString ∘ Unhygienic.run

#eval run `(Nat.one)
#eval run `($Syntax.missing)
namespace Syntax
#eval run `($missing)
#eval run `($(missing.getArg 0))
#eval run `($(id Syntax.missing) + 1)
#eval run $ let id := Syntax.missing; `($id + 1)
end Syntax
#eval run `(1 + 1)
#eval run $ `(fun a => a) >>= pure
#eval run $ do a ← `(Nat.one); `($a)
#eval run $ do a ← `(Nat.one); `(f $a $a)
#eval run $ do a ← `(Nat.one); `(f $ f $a 1)
#eval run $ do a ← `(Nat.one); `(f $(id a))
#eval run $ do a ← `(1 + 2); match_syntax a with `($a + $b) => `($b + $a) | _ => pure Syntax.missing

#eval run $ do a ← `(aa); match_syntax a with `($id:id) => pure 0 | `($e) => pure 1 | _ => pure 2
#eval run $ do a ← `(1 + 2); match_syntax a with `($id:id) => pure 0 | `($e) => pure 1 | _ => pure 2

#eval run $ do params ← #[`(a), `((b : Nat))].mapM id; `(fun $params* => 1)
#eval run $ do a ← `(fun (a : Nat) b => c); match_syntax a with `(fun $aa* => $e) => pure aa | _ => pure #[]
#eval run $ do a ← `(∀ a, c); match_syntax a with `(∀ $id:ident, $e) => pure id | _ => pure a
#eval run $ do a ← `(∀ _, c); match_syntax a with `(∀ $id:ident, $e) => pure id | _ => pure a
#eval run $ do a ← `(a); match_syntax a with `($id:ident) => pure id | _ => pure a
#eval run $ do a ← `(a.{0}); match_syntax a with `($id:ident) => pure id | _ => pure a
#eval run $ do a ← `(match a with | a => 1 | _ => 2); match_syntax a with `(match $e with $eqns:matchAlt*) => pure eqns | _ => pure #[]

end Lean
