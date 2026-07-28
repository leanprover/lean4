import Lean
open Lean Elab Command

/-! Regression test for the nested-inductive parameter uniformity check (follow-up to #14576).

The parametric arguments of a nested occurrence `I Ds is` are dropped from the generated
auxiliary declaration, so a datatype `E` being declared must occur inside `Ds` *uniformly*,
i.e. applied to the parameters of the mutual declaration. Here `E.mk` uses `E ⟨false⟩` in the
nested field `L (E ⟨false⟩)` while the constructor targets `E w`; `⟨false⟩` is not the
parameter `w`, so the kernel must reject it (Arthur Adjedj's observation). A uniform occurrence
`L (E w)`, as in `Good` below, remains accepted. -/

inductive W : Type where | mk (p : Bool)
inductive L (α : Type) : Type where | mk

meta def build : CommandElabM Unit := do
  let Ew := mkApp (mkConst `E) (mkApp (mkConst ``W.mk) (mkConst ``false))
  let l := mkApp (mkConst ``L) Ew
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  -- constructor type: ∀ (w : W) (l : L (E ⟨false⟩)), E w
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `E) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `E, type := Et, ctors := [{ name := `E.mk, type := ct }] }] false

elab "mkbug" : command => build

/--
error: (kernel) invalid occurrence of datatype 'E' being declared: it must be applied to the parameters of the mutual declaration
-/
#guard_msgs in
mkbug

-- A non-uniform occurrence may also hide behind a redex in a phantom argument, where the positivity
-- check never fires: here `β := (fun g => g ⟨false⟩) E` reduces to `E ⟨false⟩`. The check must inspect
-- every occurrence of `E`, not only fully applied ones.
inductive L2 (α : Type) (β : Type) : Type where | mk (a : α)

meta def buildPhantom : CommandElabM Unit := do
  let w := mkBVar 0
  let Ew := mkApp (mkConst `F) w
  let redex := mkApp (mkLambda `g .default (mkForall `_ .default (mkConst ``W) (mkSort 1))
                        (mkApp (mkBVar 0) (mkApp (mkConst ``W.mk) (mkConst ``false)))) (mkConst `F)
  let l := mkApp2 (mkConst ``L2) Ew redex
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `F) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `F, type := Et, ctors := [{ name := `F.mk, type := ct }] }] false

elab "mkbug2" : command => buildPhantom

/--
error: (kernel) invalid occurrence of datatype 'F' being declared: it must be applied to the parameters of the mutual declaration
-/
#guard_msgs in
mkbug2

-- A non-uniform occurrence hidden in an *index* of a dropped parameter is also rejected: the check
-- recurses into the indices. Here `E`'s index in `L (E w (E ⟨false⟩))` contains the non-uniform `E ⟨false⟩`.
meta def buildIndex : CommandElabM Unit := do
  let w := mkBVar 0
  let Efalse := mkApp (mkConst `G) (mkApp (mkConst ``W.mk) (mkConst ``false))
  let l := mkApp (mkConst ``L) (mkApp2 (mkConst `G) w Efalse)
  let Et := mkForall `w .default (mkConst ``W) (mkForall `i .default (mkSort 1) (mkSort 1))
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp2 (mkConst `G) (mkBVar 1) (mkConst ``Nat))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `G, type := Et, ctors := [{ name := `G.mk, type := ct }] }] false

elab "mkbug3" : command => buildIndex

/--
error: (kernel) invalid occurrence of datatype 'G' being declared: it must be applied to the parameters of the mutual declaration
-/
#guard_msgs in
mkbug3

-- Documenting current behaviour: a datatype occurring in the *index* of a dropped parameter is only
-- checked for parameter uniformity, not for the `#2125` "no occurrence in an index" rule. Here `E`
-- occurs in the index of itself (`E (E Nat)`), which is uniform (`E` has no parameters), so it is
-- accepted. Whether dropped-parameter indices should also be checked is left open.
meta def buildSelfIndex : CommandElabM Unit := do
  let ENat := mkApp (mkConst `H) (mkConst ``Nat)
  let l := mkApp (mkConst ``L) (mkApp (mkConst `H) ENat)  -- L (H (H Nat))
  let Et := mkForall `i .default (mkSort 1) (mkSort 1)
  let ct := mkForall `l .default l ENat
  liftCoreM <| addDecl <| .inductDecl [] 0 [{
    name := `H, type := Et, ctors := [{ name := `H.mk, type := ct }] }] false
  logInfo "H accepted"

elab "mkselfindex" : command => buildSelfIndex

/-- info: H accepted -/
#guard_msgs in
mkselfindex

-- Uniform nested occurrences are still accepted.
inductive Good (p : Type) where
  | mk : List (Good p) → Good p

mutual
  inductive A (p : Type) where | mk : List (B p) → A p
  inductive B (p : Type) where | mk : Array (A p) → B p
end
