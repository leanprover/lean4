import Lean.Elab.Term
open Lean

def isProp.{u} : Prop := ∀ (x : Sort u) (y z : x), y = z

theorem isProp_prop : isProp.{0} := fun _ _ _ => rfl
theorem not_isProp_type : ¬isProp.{1} := fun h => nomatch h _ 0 1

theorem isProp_not_invariant : isProp.{0} ≠ isProp.{1} :=
  mt (fun h => cast h isProp_prop) not_isProp_type

def mkLevel : Nat → Level → Level
  | 0, e => e
  | n+1, e => mkLevel n (.max .zero e)

-- #eval (mkLevel (2^24) (.param `u)).hasParam -- false!

#guard_msgs(drop all) in
run_elab
  let l := mkLevel (2^24) (.param `u)
  Lean.addDecl <| .defnDecl {
    name := `magic
    levelParams := []
    type := .sort .zero
    value := .const `isProp [l]
    hints := .opaque
    safety := .safe
  }

run_elab
  Lean.addDecl <| .defnDecl {
    name := `magic_eq
    levelParams := [`u]
    type := mkPropEq (.const `magic []) (.const `isProp [.param `u])
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (.sort .zero) (.const `magic [])
    hints := .opaque
    safety := .safe
  }

universe u
example : magic = isProp.{u} := magic_eq.{u}

theorem contradiction : False := isProp_not_invariant (magic_eq.{0}.symm.trans magic_eq.{1})

#print axioms contradiction
