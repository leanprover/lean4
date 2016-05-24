/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.char

definition string := list char

definition string.empty : string := list.nil
definition string.str : char → string → string := list.cons
