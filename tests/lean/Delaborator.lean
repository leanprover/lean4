import Init.Lean
open Lean
open Lean.Elab
open Lean.Elab.Term

def check (stx : TermElabM Syntax) (optionsPerPos : OptionsPerPos := {}) : TermElabM Unit := do
stx ← stx;
opts ← getOptions;
e ← elabTermAndSynthesize stx none <* throwErrorIfErrors;
stx' ← liftMetaM stx $ delab e opts optionsPerPos;
dbgTrace $ toString stx';
e' ← elabTermAndSynthesize stx' none <* throwErrorIfErrors;
unlessM (isDefEq stx e e') $
  throwError stx "failed to round-trip"

-- #eval check `(?m)  -- fails round-trip

#eval check `(Sort)
#eval check `(Type)
#eval check `(Type 0)
#eval check `(Type 1)
-- can't add a new universe variable inside a term...
#eval check `(Type _)
#eval check `(Type (_ + 2))

#eval check `(Nat)
#eval check `(List Nat)
#eval check `(id Nat)
section
  set_option pp.explicit true
  #eval check `(List Nat)
  #eval check `(id Nat)
end
section
  set_option pp.universes true
  #eval check `(List Nat)
  #eval check `(id Nat)
end
#eval check `(id (id Nat)) (RBMap.empty.insert 4 $ KVMap.empty.insert `pp.explicit true)

#eval check `(fun (a : Nat) => a)
#eval check `(fun (a b : Nat) => a)
#eval check `(fun (a : Nat) (b : Bool) => a)
#eval check `(@(fun {a b : Nat} => a))
#eval check `(@(fun {α} [HasToString α] => true))

-- TODO: hide `ofNat`
#eval check `(0)
#eval check `(1)
#eval check `(42)
#eval check `("hi")
