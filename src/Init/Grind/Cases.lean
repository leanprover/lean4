/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Grind.Tactics

attribute [grind cases eager] And Prod False Empty True Unit Exists
attribute [grind cases] Or
