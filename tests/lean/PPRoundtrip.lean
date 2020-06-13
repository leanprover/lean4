import Lean
open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Format

def check (stx : TermElabM Syntax) (optionsPerPos : OptionsPerPos := {}) : TermElabM Unit := do
stx ← stx;
opts ← getOptions;
e ← elabTermAndSynthesize stx none <* throwErrorIfErrors;
stx' ← liftMetaM stx $ delab e opts optionsPerPos;
stx' ← liftMetaM stx' $ PrettyPrinter.parenthesizeTerm stx';
dbgTrace $ toString stx';
e' ← elabTermAndSynthesize stx' none <* throwErrorIfErrors;
unlessM (isDefEq stx e e') $
  throwError stx (fmt "failed to round-trip" ++ line ++ fmt e ++ line ++ fmt e')

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
#eval check `(id (id (id Nat)))
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

-- specify the expected type of `a` in a way that is not erased by the delaborator
def typeAs.{u} (α : Type u) (a : α) := ()

#eval check `(fun (a : Nat) => a)
#eval check `(fun (a b : Nat) => a)
#eval check `(fun (a : Nat) (b : Bool) => a)
#eval check `(fun {a b : Nat} => a)
-- implicit lambdas work as long as the expected type is preserved
#eval check `(typeAs ({α : Type} → (a : α) → α) fun a => a)
section set_option pp.explicit true
  #eval check `(fun {α : Type} [HasToString α] (a : α) => toString a)
end

#eval check `((α : Type) → α)
#eval check `((α β : Type) → α)  -- group
#eval check `((α β : Type) → Type)  -- don't group
#eval check `((α : Type) → (a : α) → α)
#eval check `((α : Type) → (a : α) → a = a)
#eval check `({α : Type} → α)
#eval check `({α : Type} → [HasToString α] → α)

-- TODO: hide `ofNat`
#eval check `(0)
#eval check `(1)
#eval check `(42)
#eval check `("hi")

#eval check `((1,2).fst)

#eval check `(1 < 2 || true)
