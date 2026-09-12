/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam, Gabriel Ebner
-/

module

prelude
public import Lean.Elab.Command.WithWeakNamespace

namespace Lean.Elab.Command

private def toTermAttrs (attr : TSyntax `Lean.Parser.Command.scopedNSAttrs) :
    TSyntax `Lean.Parser.Term.attributes :=
  ⟨attr.raw.setKind `Lean.Parser.Term.attributes⟩

@[builtin_macro Lean.Parser.Command.scopedNS] def expandScopedNS : Macro
  | `($[$doc]? $(attr)? scoped[$ns] notation $(prec)? $(n)? $(prio)? $sym* => $t) => do
    let attr' := attr.map toTermAttrs
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $[$attr']? scoped notation $(prec)? $(n)? $(prio)? $sym* => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:prefix $prec $(n)? $(prio)? $sym => $t) => do
    let attr' := attr.map toTermAttrs
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $[$attr']? scoped $mk:prefix $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:infix $prec $(n)? $(prio)? $sym => $t) => do
    let attr' := attr.map toTermAttrs
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $[$attr']? scoped $mk:infix $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:infixl $prec $(n)? $(prio)? $sym => $t) => do
    let attr' := attr.map toTermAttrs
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $[$attr']? scoped $mk:infixl $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:infixr $prec $(n)? $(prio)? $sym => $t) => do
    let attr' := attr.map toTermAttrs
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $[$attr']? scoped $mk:infixr $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:postfix $prec $(n)? $(prio)? $sym => $t) => do
    let attr' := attr.map toTermAttrs
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $[$attr']? scoped $mk:postfix $prec $(n)? $(prio)? $sym => $t)
  | `(scoped[$ns] attribute [$[$attr:attr],*] $ids*) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      attribute [$[scoped $attr:attr],*] $ids*)
  | _ => Macro.throwUnsupported

end Lean.Elab.Command
