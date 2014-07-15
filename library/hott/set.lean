-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

definition is_set (A : Type) := Π (x y : A) (p q : x = y), p = q

inductive hset : Type :=
| hset_intro : Π (A : Type), is_set A → hset
