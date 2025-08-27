/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Core
public import Init.Grind.AC
public section
namespace Lean.Grind.AC

def Seq.length : Seq → Nat
  | .var _ => 1
  | .cons _ s => s.length + 1

end Lean.Grind.AC
