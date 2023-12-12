import Lean

open Lean
open Lean.Elab

def run {α} [ToString α] : Unhygienic α → String := toString ∘ Unhygienic.run

#eval run `()
#eval run `(Nat.one)
def miss : TSyntax `term := ⟨Syntax.missing⟩
#eval run `($miss)
namespace Lean.Syntax
#eval run `($miss)
#eval run `($(miss))
#eval run `($(id miss) + 1)
#eval run $ let id := miss; `($id + 1)
end Lean.Syntax
#eval run `(1 + 1)
#eval run `([x+])
#eval run $ `(fun a => a) >>= pure
#eval run $ `(def foo := 1)
#eval run $ `(def foo := 1 def bar := 2)
#eval run $ do let a ← `(Nat.one); `($a)
#eval run $ do `($(← `(Nat.one)))
#eval run $ do let a ← `(Nat.one); `(f $a $a)
#eval run $ do let a ← `(Nat.one); `(f $ f $a 1)
#eval run $ do let a ← `(Nat.one); `(f $(id a))
#eval run $ do let a ← `(Nat.one); `($(a).b)
#eval run $ do let a ← `(1 + 2); match a with | `($a + $b) => `($b + $a) | _ => pure miss
#eval run $ do let a ← `(1 + 2); match a with | stx@`($a + $b) => `($stx + $a) | _ => pure miss
#eval run $ do let a ← `(def foo := 1); match a with | `($f:command) => pure f
#eval run $ do let a ← `(def foo := 1 def bar := 2); match a with | `($f:command $g:command) => `($g:command $f:command) | _ => pure ⟨Syntax.missing⟩

#eval run $ do let a ← `(aa); match a with | `($_:ident) => pure 0 | `($_) => pure 1
#eval match mkIdent `aa with | `(aa) => 0 | _ => 1
#eval match mkIdent `aa with | `(ab) => 0 | _ => 1
#eval run $ do let a ← `(1 + 2); match a with | `($id:ident) => pure 0 | `($e) => pure 1
#eval run $ do let params ← #[`(a), `((b : Nat))].mapM id; `(fun $params:term* => 1)
#eval run $ do let a ← `(fun (a : Nat) b => c); match a with | `(fun $aa* => $e) => pure aa | _ => pure #[]
#eval run $ do let a ← `(∀ a, c); match a with | `(∀ $id:ident, $e) => pure id | _ => pure ⟨a⟩
#eval run $ do let a ← `(∀ _, c); match a with | `(∀ $id:ident, $e) => pure id | _ => pure ⟨a⟩
-- this one should NOT check the kind of the matched node
#eval run $ do let a ← `(∀ _, c); match a with | `(∀ $a, $e) => pure a | _ => pure ⟨a⟩
#eval run $ do let a ← `(a); match a with | `($id:ident) => pure id | _ => pure ⟨a⟩
#eval run $ do let a ← `(a.{0}); match a with | `($id:ident) => pure id | _ => pure ⟨a⟩
#eval run $ do let a ← `(match a with | a => 1 | _ => 2); match a with | `(match $e:term with $eqns:matchAlt*) => pure eqns | _ => pure #[]

def f (stx : Syntax) : Unhygienic Syntax := match stx with
  | `({ $f:ident := $e $[: $a]?}) => `({ $f:ident := $e $[: $(id a)]?})
  | _ => unreachable!
#eval run do f (← `({ a := a : a }))
#eval run do f (← `({ a := a }))

def f' (stx : Syntax) : Unhygienic Syntax := match stx with
  | `(section $(id?)?) => `(section $(id?)?)
  | _ => unreachable!
#eval run do f' (← `(section))
#eval run do f' (← `(section foo))

#eval run do
  match ← `(match a with | a => b | a + 1 => b + 1) with
  | `(match $e:term with $[| $pats =>%$arr $rhss]*) => `(match $e:term with $[| $pats =>%$arr $rhss]*)
  | _ => unreachable!

#eval run do
  match ← `(match a with | a => b | a + 1 => b + 1) with
  | `(match $e:term with $alts:matchAlt*) => `(match $e:term with $alts:matchAlt*)
  | _ => unreachable!

open Parser.Term
#eval run do
  match ← `(structInstField|a := b) with
  | `(Parser.Term.structInstField| $lhs:ident := $rhs) => pure #[lhs.raw, rhs]
  | _ => unreachable!

#eval run do
  match ← `({ a := a : a }) with
  | `({ $f:ident := $e : 0 })      => pure "0"
  | `({ $f:ident := $e $[: $a?]?}) => pure "1"
  | stx                    => pure "2"

#eval run `(sufficesDecl|x from x)

#eval run do
  match ← `([1, 2, 3, 4]) with
    | `([$x, $ys,*, $z]) => pure #[x.raw, mkNullNode ys, z]
    | _ => unreachable!

#eval run do
  match ← `([1, 2]) with
    | `([$x, $y, $zs,*]) => pure zs.getElems
    | `([$x, $ys,*])     => pure ys.getElems
    | _ => unreachable!

#check (match · with | `([1, $ys,*, 2, $zs,*, 3]) => _)

#eval run do
  match Syntax.setHeadInfo (← `(fun x =>%$(Syntax.atom (SourceInfo.synthetic ⟨2⟩ ⟨2⟩) "") x)) (SourceInfo.synthetic ⟨1⟩ ⟨1⟩) with
  | `(fun%$i1 $x =>%$i2 $y) => pure #[i1.getPos?, i2.getPos?]
  | _ => unreachable!

#eval run ``(x)
#eval run ``(id)
#eval run ``(pure)
syntax "foo" term : term
#eval run ``(foo $(miss))  -- syntax with no quoted identifiers should be ignored
#eval run ``(fun x => x)
#eval run ``(fun x => y)
#eval run ``(fun x y => x y)
#eval run ``(fun ⟨x, y⟩ => x)

#eval run do
  match mkIdent `b with
  | `(a) => pure "0"
  | `(b) => pure "1"
  | _    => pure "2"

declare_syntax_cat mycat
syntax "mystx" : mycat
#eval run `(mycat| mystx)

-- should not introduce an anonymous ldecl
example
  | `([$_,*]) => id 0
  | _ => 1

syntax "test" ("a" <|> ("b" <|> "c")) : term
#check fun e => `(test $e)
