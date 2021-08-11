import Lean

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Elab.Command
open Std.Format open Std
open Lean.PrettyPrinter
open Lean.PrettyPrinter.Delaborator

open Lean.Meta

def checkM (stx : TermElabM Syntax) (optionsPerPos : OptionsPerPos := {}) : TermElabM Unit := do
let opts ← getOptions
let stx ← stx
let e ← elabTermAndSynthesize stx none <* throwErrorIfErrors
let stx' ← delab Name.anonymous [] e optionsPerPos
let f' ← PrettyPrinter.ppTerm stx'
let s := f'.pretty' opts
IO.println s
let env ← getEnv
match Parser.runParserCategory env `term s "<input>" with
| Except.error e => throwErrorAt stx e
| Except.ok stx'' => do
  let e' ← elabTermAndSynthesize stx'' none <* throwErrorIfErrors
  unless (← isDefEq e e') do
    throwErrorAt stx (m!"failed to round-trip" ++ line ++ format e ++ line ++ format e')

-- set_option trace.PrettyPrinter.parenthesize true
set_option format.width 20

-- #eval checkM `(?m)  -- fails round-trip

#eval checkM `(Sort)
#eval checkM `(Type)
#eval checkM `(Type 0)
#eval checkM `(Type 1)
-- TODO: we need support for parsing `?u` to roundtrip the terms containing universe metavariables. Just pretty printing them as `_` is bad for error and trace messages
-- #eval checkM `(Type _)
-- #eval checkM `(Type (_ + 2))

#eval checkM `(Nat)
#eval checkM `(List Nat)
#eval checkM `(id Nat)
#eval checkM `(id (id (id Nat)))
section
  set_option pp.explicit true
  #eval checkM `(List Nat)
  #eval checkM `(id Nat)
end
section
  set_option pp.universes true
  #eval checkM `(List Nat)
  #eval checkM `(id Nat)
  #eval checkM `(Sum Nat Nat)
end
#eval checkM `(id (id Nat)) (Std.RBMap.empty.insert 5 $ KVMap.empty.insert `pp.explicit true)

-- specify the expected type of `a` in a way that is not erased by the delaborator
def typeAs.{u} (α : Type u) (a : α) := ()

set_option pp.analyze.knowsType false in
#eval checkM `(fun (a : Nat) => a)

#eval checkM `(fun (a : Nat) => a)
#eval checkM `(fun (a b : Nat) => a)
#eval checkM `(fun (a : Nat) (b : Bool) => a)
#eval checkM `(fun {a b : Nat} => a)
-- implicit lambdas work as long as the expected type is preserved
#eval checkM `(typeAs ({α : Type} → (a : α) → α) fun a => a)
section
  set_option pp.explicit true
  #eval checkM `(fun {α : Type} [ToString α] (a : α) => toString a)
end

#eval checkM `((α : Type) → α)
#eval checkM `((α β : Type) → α)  -- group
#eval checkM `((α β : Type) → Type)  -- don't group
#eval checkM `((α : Type) → (a : α) → α)
#eval checkM `({α : Type} → α)
#eval checkM `({α : Type} → [ToString α] → α)
#eval checkM `(∀ x : Nat, x = x)
#eval checkM `(∀ {x : Nat} [ToString Nat], x = x)
set_option pp.piBinderTypes false in
#eval checkM `(∀ x : Nat, x = x)

-- TODO: hide `ofNat`
#eval checkM `(0)
#eval checkM `(1)
#eval checkM `(42)
#eval checkM `("hi")

set_option pp.structureInstanceTypes true in
#eval checkM `({ type := Nat, val := 0 : PointedType })
#eval checkM `((1,2,3))
#eval checkM `((1,2).fst)

#eval checkM `(1 < 2 || true)

#eval checkM `(id (fun a => a) 0)

#eval checkM `(typeAs Nat (do
  let x := 1
  discard <| pure 2
  let y := 3
  return x + y))

#eval checkM `(typeAs (Id Nat) (pure 1 >>= pure))

#eval checkM `((0 ≤ 1) = False)
#eval checkM `((0 = 1) = False)

#eval checkM `(-(-0))
