module
public import Lean.Elab.Command.WithWeakNamespace
/-
Tests for scoping syntax to a specific namespace using `scoped[NS]`
-/

open Lean

syntax (name := scopedNS) (docComment)? (Parser.Term.attributes)?
  "scoped" "[" ident "] " command : command

macro_rules
  | `($[$doc]? $(attr)? scoped[$ns] notation $(prec)? $(n)? $(prio)? $sym* => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $(attr)? scoped notation $(prec)? $(n)? $(prio)? $sym* => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:prefix $prec $(n)? $(prio)? $sym => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $(attr)? scoped $mk:prefix $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:infix $prec $(n)? $(prio)? $sym => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $(attr)? scoped $mk:infix $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:infixl $prec $(n)? $(prio)? $sym => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $(attr)? scoped $mk:infixl $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:infixr $prec $(n)? $(prio)? $sym => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $(attr)? scoped $mk:infixr $prec $(n)? $(prio)? $sym => $t)
  | `($[$doc]? $(attr)? scoped[$ns] $mk:postfix $prec $(n)? $(prio)? $sym => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $(attr)? scoped $mk:postfix $prec $(n)? $(prio)? $sym => $t)
  | `(scoped[$ns] attribute [$[$attr:attr],*] $ids*) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      attribute [$[scoped $attr:attr],*] $ids*)


-- Test 1: Scoped notation in a different namespace
namespace A

scoped[B] postfix:1024 " !" => Nat.succ

end A

-- The notation should be accessible when opening B
open B
#guard (5 ! = 6)

-- Test 2: Scoped infix notation
scoped[Math] infix:65 " ⊕ " => Nat.add

/-- info: 7 -/
#guard_msgs in
open Math in
#eval 3 ⊕ 4

/--
error: failed to synthesize instance of type class
  OfNat (Type ?u.19670) 3
numerals are polymorphic in Lean, but the numeral `3` cannot be used in a context where the expected type is
  Type ?u.19670
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  OfNat (Type ?u.19669) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Type ?u.19669
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: cannot evaluate, types are not computationally relevant
-/
#guard_msgs in
#eval 3 ⊕ 4


-- Test 3: Scoped attribute
def myInstance : Inhabited Nat := ⟨42⟩

scoped[MyNS] attribute [instance] myInstance

/-- info: 42 -/
#guard_msgs in
open MyNS in
#eval (default : Nat)

/-- info: 0 -/
#guard_msgs in
#eval (default : Nat)
