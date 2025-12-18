import Lean
open Lean

local macro "ofNat_class" Class:ident n:num : command =>
  let field := Lean.mkIdent <| .mkSimple Class.getId.eraseMacroScopes.getString!.toLower
  `(class $Class:ident.{u} (α : Type u) where
    $field:ident : α

  instance {α} [$Class α] : OfNat α (nat_lit $n) where
    ofNat := ‹$Class α›.1

  instance {α} [OfNat α (nat_lit $n)] : $Class α where
    $field:ident := $n)

ofNat_class Zero' 0
