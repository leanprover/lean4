/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Parser.Term
import Lean.Elab.Term.TermElabM
meta import Lean.Parser.Do

namespace Lean.Elab.Do

open Lean.Parser.Term

/--
A body that effect-forwards into the enclosing `do` block via a `do←` marker, captured from
syntax of the form `do← body` or `fun b₁ … bₖ => do← body`. `binders` is empty in the bare
form.
-/
public structure ForwardArg where
  binders : Array (TSyntax ``funBinder)
  body    : DoSeq

/--
If `e` is a function application whose last argument effect-forwards into the enclosing `do`
block (its body bears a `do←` marker, possibly under `fun` binders), return the application
head sans the forwarding argument together with the `ForwardArg` description.
-/
public def Forward.matchApp? (e : Term) : Option (Term × ForwardArg) := do
  let `($head $args*) := (⟨dropParens e.raw⟩ : Term) | none
  let last : Term := ⟨dropParens (← args.back?).raw⟩
  let arg : ForwardArg ←
    if last.raw.isOfKind ``doForward then
      some ⟨#[], ⟨last.raw[2]⟩⟩
    else if let `(fun $bs:funBinder* => $rest) := last then
      let rest := dropParens rest.raw
      if rest.isOfKind ``doForward then some ⟨bs, ⟨rest[2]⟩⟩ else none
    else none
  let preArgs := args.pop
  let head' : Term :=
    if preArgs.isEmpty then head
    else ⟨mkNode ``Lean.Parser.Term.app #[head, mkNullNode preArgs]⟩
  some (head', arg)

end Lean.Elab.Do
