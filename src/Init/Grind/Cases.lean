/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Core
public import Init.Grind.Tactics

public section

attribute [grind cases eager] And False Empty True PUnit Exists Subtype Prod PProd MProd
attribute [grind cases] Or
