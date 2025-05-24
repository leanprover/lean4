/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Core
import Init.Grind.Tactics

attribute [grind cases eager] And Prod False Empty True PUnit Exists Subtype
attribute [grind cases] Or

attribute [grind cases] Std.Associative Std.Commutative Std.IdempotentOp
  Std.LawfulLeftIdentity Std.LawfulRightIdentity Std.LawfulIdentity Std.LawfulCommIdentity
  Std.Refl Std.Antisymm Std.Asymm Std.Total Std.Irrefl
