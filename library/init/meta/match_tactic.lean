/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
structure pattern :=
/- Term to match. -/
(target : expr)
/- Set of terms that is instantiated for each successful match. -/
(output : list expr)
/- Number of (temporary) universe meta-variables in this pattern. -/
(nuvars : nat)
/- Number of (temporary) meta-variables in this pattern. -/
(nmvars : nat)

/- (mk_pattern ls es t o) creates a new pattern with (length ls) universe meta-variables and (length es) meta-variables.
   In the produced pattern p, we have that
   - (pattern.target p) is the term t where the universes ls and expressions es have been replaced with temporary meta-variables.
   - (pattern.output p) is the list o where the universes ls and expressions es have been replaced with temporary meta-variables.
   - (pattern.nuvars p) = length ls
   - (pattern.nmvars p) = length es

   The tactic fails if o and the types of es do not contain all universes ls and expressions es. -/
meta_constant mk_pattern : list level → list expr → expr → list expr → tactic pattern
/- (mk_pattern_core m p e) matches (pattern.target p) and e using transparency m.
   If the matching is successful, then return the instantiation of (pattern.output p).
   The tactic fails if not all (temporary) meta-variables are assigned. -/
meta_constant match_pattern_core : transparency → pattern → expr → tactic (list expr)

meta_definition match_pattern : pattern → expr → tactic (list expr) :=
match_pattern_core semireducible

end tactic
