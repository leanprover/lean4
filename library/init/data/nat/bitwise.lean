/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic init.data.nat.div init.coe
namespace Nat

partial def bitwise (f : Bool → Bool → Bool) : Nat → Nat → Nat | n, m =>
if n = 0 then      (if f false true then m else 0)
else if m = 0 then (if f true false then n else 0)
else
  let n' := n / 2;
  let m' := m / 2;
  let b₁ := n % 2 = 1;
  let b₂ := m % 2 = 1;
  let r  := bitwise n' m';
  if f b₁ b₂ then bit1 r else bit0 r

@[extern c "lean_nat_land" cpp "lean::nat_land"]
def land : Nat → Nat → Nat := bitwise and
@[extern c "lean_nat_lor" cpp "lean::nat_lor"]
def lor  : Nat → Nat → Nat := bitwise or

end Nat
