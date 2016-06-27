/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
structure pattern :=
(target : expr) (output : list expr) (nuvars : nat) (nmvars : nat)

meta_constant mk_pattern : list level → list expr → expr → list expr → tactic pattern
meta_constant match_pattern_core : transparency → pattern → expr → tactic (list expr)

meta_definition match_pattern : pattern → expr → tactic (list expr) :=
match_pattern_core transparency.semireducible

end tactic
