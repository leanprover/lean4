/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.nat.div init.coe
namespace nat

def bitwise (f : bool → bool → bool) : nat → nat → nat | n m :=
if n = 0 then      (if f ff tt then m else 0)
else if m = 0 then (if f tt ff then n else 0)
else
  let n' := n / 2 in
  let m' := m / 2 in
  let b₁ := n % 2 = 1 in
  let b₂ := m % 2 = 1 in
  let r  := bitwise n' m' in
  if f b₁ b₂ then bit1 r else bit0 r

def land : nat → nat → nat := bitwise band
def lor  : nat → nat → nat := bitwise bor

end nat
