/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura

Confirm that @[class] annotation means definition can be treated as class.
-/

@[class] def Foo (n : Nat) : Prop := n > 2
@[instance] axiom foo2 : Foo 2

axiom natToType (n : Nat) : Type

@[instance] axiom foo2mul (n : Nat) [Foo n] : HasMul (natToType n)

axiom f1 (α β : natToType 2) : α * β = β * α
axiom f2 (n : Nat) (fn : Foo n) (α β : natToType n) : α * β = β * α
