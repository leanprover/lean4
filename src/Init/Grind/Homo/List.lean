/-
Copyright (c) 2026 Andres Erbsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Erbsen, Leonardo de Moura
-/
module
prelude
import Init.Grind.Attr
public import Init.Data.List.Lemmas
public import Init.Data.List.TakeDrop
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.List.Nat.InsertIdx
public import Init.Data.List.Nat.Modify
public import Init.Data.List.Erase
public import Init.Data.List.Zip
public section

/-!
Homomorphism rules for `List` used by the `grind` tactic.
The injection function is `List.length`.
-/

attribute [grind homo]
  List.length_nil List.length_cons List.length_append List.length_drop List.length_take
  List.length_reverse List.length_map List.length_replicate List.length_tail List.length_concat
  List.length_zipWith List.length_zip List.length_set List.length_insertIdx List.length_eraseIdx
  List.length_modify List.length_singleton List.length_dropLast List.length_dropLast_cons
  List.length_replace
  List.drop_drop List.take_take
