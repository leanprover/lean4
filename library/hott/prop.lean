-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

definition is_prop (A : Type) := Π (x y : A), x = y

inductive hprop : Type :=
| hprop_intro : Π (A : Type), is_prop A → hprop
