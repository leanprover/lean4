/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.ToString

namespace Lean

inductive LBool
| false
| true
| undef

namespace LBool

instance : Inhabited LBool := ⟨false⟩

def neg : LBool → LBool
| true  => false
| false => true
| undef => undef

def and : LBool → LBool → LBool
| true,  b  => b
| a,     _  => a

def beq : LBool → LBool → Bool
| true,  true  => Bool.true
| false, false => Bool.true
| undef, undef => Bool.true
| _,     _     => Bool.false

instance : HasBeq LBool := ⟨beq⟩

def toString : LBool → String
| true  => "true"
| false => "false"
| undef => "undef"

instance : HasToString LBool := ⟨toString⟩

end LBool

end Lean

def Bool.toLBool : Bool → Lean.LBool
| true  => Lean.LBool.true
| false => Lean.LBool.false

@[inline] def toLBoolM {m : Type → Type} [Monad m] (x : m Bool) : m Lean.LBool :=
do b ← x; pure b.toLBool
