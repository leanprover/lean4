/-
Copyright (c) 2024 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/
prelude
import Std.Tactic.BVAckermannize.Syntax

/-!
This directory contains the lazy ackermannization tactic.
This uses lean's builtin bitblaster to reduce uninterpreted functions + bitvectors to SAT.
-/
