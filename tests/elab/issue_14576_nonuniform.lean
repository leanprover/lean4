import Lean
open Lean Elab Command

/-! The kernel rejects inductive declarations in which a datatype being declared occurs applied to
something other than the parameters and universe levels of the declaration (follow-up to #14576).

The frontend already enforces this (`lean.inductiveParamMismatch`, `lean.inductiveParamMissing`) and
normalizes the occurrences it accepts, so the declarations below are built with `addDecl` directly. -/

inductive W : Type where | mk (p : Bool)
inductive L (α : Type) : Type where | mk
inductive L2 (α : Type) (β : Type) : Type where | mk (a : α)
def Ignore (_ : Type) : Type := Unit

-- The parametric arguments of a nested occurrence `I Ds is` are dropped from the auxiliary
-- declaration the kernel generates, so a non-uniform occurrence inside `Ds` escaped checking, a
-- potential soundness issue (Arthur Adjedj's observation). Here `E.mk` uses `E ⟨false⟩` in the
-- nested field `L (E ⟨false⟩)` while the constructor targets `E w`.
meta def buildNested : CommandElabM Unit := do
  let Ew := mkApp (mkConst `E) (mkApp (mkConst ``W.mk) (mkConst ``false))
  let l := mkApp (mkConst ``L) Ew
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  -- constructor type: ∀ (w : W) (l : L (E ⟨false⟩)), E w
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `E) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `E, type := Et, ctors := [{ name := `E.mk, type := ct }] }] false

elab "mkbug" : command => buildNested

/--
error: (kernel) invalid occurrence of datatype 'E' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkbug

-- A non-uniform occurrence may also hide behind a redex in a phantom argument, where the positivity
-- check never fires: here `β := (fun g => g ⟨false⟩) F` reduces to `F ⟨false⟩`.
meta def buildPhantom : CommandElabM Unit := do
  let Fw := mkApp (mkConst `F) (mkBVar 0)
  let redex := mkApp (mkLambda `g .default (mkForall `_ .default (mkConst ``W) (mkSort 1))
                        (mkApp (mkBVar 0) (mkApp (mkConst ``W.mk) (mkConst ``false)))) (mkConst `F)
  let l := mkApp2 (mkConst ``L2) Fw redex
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `F) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `F, type := Et, ctors := [{ name := `F.mk, type := ct }] }] false

elab "mkbug2" : command => buildPhantom

/--
error: (kernel) invalid occurrence of datatype 'F' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkbug2

-- The occurrence may also sit in an index of a dropped parameter: `G`'s index in
-- `L (G w (G ⟨false⟩))` contains the non-uniform `G ⟨false⟩`.
meta def buildIndex : CommandElabM Unit := do
  let Gfalse := mkApp (mkConst `G) (mkApp (mkConst ``W.mk) (mkConst ``false))
  let l := mkApp (mkConst ``L) (mkApp2 (mkConst `G) (mkBVar 0) Gfalse)
  let Et := mkForall `w .default (mkConst ``W) (mkForall `i .default (mkSort 1) (mkSort 1))
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp2 (mkConst `G) (mkBVar 1) (mkConst ``Nat))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `G, type := Et, ctors := [{ name := `G.mk, type := ct }] }] false

elab "mkbug3" : command => buildIndex

/--
error: (kernel) invalid occurrence of datatype 'G' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkbug3

-- Changed behaviour: an occurrence that a later `whnf` erases is now rejected as well. The field
-- `Ignore (D Nat)` of `D.mk` reduces to `Unit`, so this declaration used to be accepted.
meta def buildErased : CommandElabM Unit := do
  let Dt := mkForall `p .default (mkSort 1) (mkSort 1)
  -- constructor type: ∀ (p : Type), Ignore (D Nat) → D p
  let ct := mkForall `p .default (mkSort 1) <|
    mkForall `_ .default (mkApp (mkConst ``Ignore) (mkApp (mkConst `D) (mkConst ``Nat)))
      (mkApp (mkConst `D) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `D, type := Dt, ctors := [{ name := `D.mk, type := ct }] }] false

elab "mkerased" : command => buildErased

/--
error: (kernel) invalid occurrence of datatype 'D' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkerased

-- Changed behaviour: the universe levels must be uniform too. The nested field of `U.mk` uses
-- `U.{v, u}` while the declaration is `U.{u, v}`; this used to be accepted.
meta def buildLevels : CommandElabM Unit := do
  let Ut := mkForall `p .default (mkSort 1) (mkSort 1)
  let ct := mkForall `p .default (mkSort 1) <|
    mkForall `_ .default (mkApp (mkConst ``L) (mkApp (mkConst `U [.param `v, .param `u]) (mkBVar 0)))
      (mkApp (mkConst `U [.param `u, .param `v]) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [`u, `v] 1 [{
    name := `U, type := Ut, ctors := [{ name := `U.mk, type := ct }] }] false

elab "mklevels" : command => buildLevels

/--
error: (kernel) invalid occurrence of datatype 'U' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mklevels

-- A datatype without parameters is unconstrained by this check; the occurrence of `H` in the index
-- of the dropped parameter `H (H Nat)` is accepted (the `#2125` rule does not apply there).
meta def buildSelfIndex : CommandElabM Unit := do
  let HNat := mkApp (mkConst `H) (mkConst ``Nat)
  let l := mkApp (mkConst ``L) (mkApp (mkConst `H) HNat)  -- L (H (H Nat))
  let Ht := mkForall `i .default (mkSort 1) (mkSort 1)
  let ct := mkForall `l .default l HNat
  liftCoreM <| addDecl <| .inductDecl [] 0 [{
    name := `H, type := Ht, ctors := [{ name := `H.mk, type := ct }] }] false
  logInfo "H accepted"

elab "mkselfindex" : command => buildSelfIndex

/-- info: H accepted -/
#guard_msgs in
mkselfindex

-- Uniform occurrences are still accepted. The frontend normalizes the occurrences it accepts, so
-- `Ignore (T (id Nat))` below reaches the kernel as `Ignore (T p)`.
inductive Good (p : Type) where
  | mk : List (Good p) → Good p

inductive T (p : Type) where
  | mk : Ignore (T (id p)) → List (T p) → T p

/-- info: constructor T.mk : {p : Type} → Ignore (T p) → List (T p) → T p -/
#guard_msgs in
#print T.mk

mutual
  inductive A (p : Type) where | mk : List (B p) → A p
  inductive B (p : Type) where | mk : Array (A p) → B p
end
