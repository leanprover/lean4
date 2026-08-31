prelude

/-! Completing declaration names in arbitrary namespaces -/

axiom Lean.Elab.Term.elabTermEnsuringType : Type
axiom Lean.Elab.Tactic.elabTermEnsuringType : Type

-- adding full namespace

#check elabTermEnsuring
                     --^ completion

-- adding partial namespace

open Lean.Elab in
#check elabTermEnsuring
                     --^ completion

-- direct + indirect match

open Lean.Elab.Term in
#check elabTermEnsuring
                     --^ completion

-- same, on the top level

axiom elabTermEnsuringType : Type
#check elabTermEnsuring
                     --^ completion

-- prioritize smaller prefixes

axiom Lean.Elab.elabTermEnsuringType : Type
#check elabTermEnsuring
                     --^ completion
