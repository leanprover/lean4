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
def IdT (α : Type 1) : Type 1 := α

/-- Log the declaration in readable form, then add it. -/
meta def mkInd (lparams : List Name) (nparams : Nat) (types : List InductiveType) :
    CommandElabM Unit := do
  let mut msg := m!"num parameters: {nparams}, universe parameters: {lparams}"
  for t in types do
    msg := msg ++ m!"\ninductive {t.name} : {t.type}"
    for c in t.ctors do
      msg := msg ++ m!"\n  | {c.name} : {c.type}"
  logInfo msg
  liftCoreM <| addDecl <| .inductDecl lparams nparams types false
  logInfo "accepted"

-- The parametric arguments of a nested occurrence `I Ds is` are dropped from the auxiliary
-- declaration the kernel generates, so a non-uniform occurrence inside `Ds` escaped checking, a
-- potential soundness issue (Arthur Adjedj's observation).
meta def buildNested : CommandElabM Unit := do
  let Efalse := mkApp (mkConst `E) (mkApp (mkConst ``W.mk) (mkConst ``false))
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default (mkApp (mkConst ``L) Efalse) (mkApp (mkConst `E) (mkBVar 1))
  mkInd [] 1 [{ name := `E, type := Et, ctors := [{ name := `E.mk, type := ct }] }]

elab "mkbug" : command => buildNested

/--
info: num parameters: 1, universe parameters: []
inductive E : W → Type
  | E.mk : (w : W) → L (E (W.mk false)) → E w
---
error: (kernel) invalid occurrence of datatype 'E' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkbug

-- A non-uniform occurrence may also hide behind a redex in a phantom argument, where the positivity
-- check never fires.
meta def buildPhantom : CommandElabM Unit := do
  let redex := mkApp (mkLambda `g .default (mkForall `_ .default (mkConst ``W) (mkSort 1))
                        (mkApp (mkBVar 0) (mkApp (mkConst ``W.mk) (mkConst ``false)))) (mkConst `F)
  let Ft := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default (mkApp2 (mkConst ``L2) (mkApp (mkConst `F) (mkBVar 0)) redex)
      (mkApp (mkConst `F) (mkBVar 1))
  mkInd [] 1 [{ name := `F, type := Ft, ctors := [{ name := `F.mk, type := ct }] }]

elab "mkbug2" : command => buildPhantom

/--
info: num parameters: 1, universe parameters: []
inductive F : W → Type
  | F.mk : (w : W) → L2 (F w) ((fun g => g (W.mk false)) F) → F w
---
error: (kernel) invalid occurrence of datatype 'F' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkbug2

-- The occurrence may also sit in an index of a dropped parameter.
meta def buildIndex : CommandElabM Unit := do
  let Gfalse := mkApp (mkConst `G) (mkApp (mkConst ``W.mk) (mkConst ``false))
  let Gt := mkForall `w .default (mkConst ``W) (mkForall `i .default (mkSort 1) (mkSort 1))
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default (mkApp (mkConst ``L) (mkApp2 (mkConst `G) (mkBVar 0) Gfalse))
      (mkApp2 (mkConst `G) (mkBVar 1) (mkConst ``Nat))
  mkInd [] 1 [{ name := `G, type := Gt, ctors := [{ name := `G.mk, type := ct }] }]

elab "mkbug3" : command => buildIndex

/--
info: num parameters: 1, universe parameters: []
inductive G : W → Type → Type
  | G.mk : (w : W) → L (G w (G (W.mk false))) → G w Nat
---
error: (kernel) invalid occurrence of datatype 'G' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkbug3

-- Changed behaviour: an occurrence that a later `whnf` erases is now rejected as well. The field of
-- `D.mk` reduces to `Unit`, so this declaration used to be accepted.
meta def buildErased : CommandElabM Unit := do
  let Dt := mkForall `p .default (mkSort 1) (mkSort 1)
  let ct := mkForall `p .default (mkSort 1) <|
    mkForall `_ .default (mkApp (mkConst ``Ignore) (mkApp (mkConst `D) (mkConst ``Nat)))
      (mkApp (mkConst `D) (mkBVar 1))
  mkInd [] 1 [{ name := `D, type := Dt, ctors := [{ name := `D.mk, type := ct }] }]

elab "mkerased" : command => buildErased

/--
info: num parameters: 1, universe parameters: []
inductive D : Type → Type
  | D.mk : (p : Type) → Ignore (D Nat) → D p
---
error: (kernel) invalid occurrence of datatype 'D' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
mkerased

-- Changed behaviour: the universe levels must be uniform too; this used to be accepted.
meta def buildLevels : CommandElabM Unit := do
  let Ut := mkForall `p .default (mkSort 1) (mkSort 1)
  let ct := mkForall `p .default (mkSort 1) <|
    mkForall `_ .default (mkApp (mkConst ``L) (mkApp (mkConst `U [.param `v, .param `u]) (mkBVar 0)))
      (mkApp (mkConst `U [.param `u, .param `v]) (mkBVar 1))
  mkInd [`u, `v] 1 [{ name := `U, type := Ut, ctors := [{ name := `U.mk, type := ct }] }]

elab "mklevels" : command => buildLevels

/--
info: num parameters: 1, universe parameters: [u, v]
inductive U : Type → Type
  | U.mk : (p : Type) → L (@U.{v, u} p) → @U.{u, v} p
---
error: (kernel) invalid occurrence of datatype 'U' being declared: it must be applied to the parameters and universe levels of the mutual declaration
-/
#guard_msgs in
set_option pp.universes true in
mklevels

-- A datatype without parameters is unconstrained by this check, so the occurrence of `H` in the
-- index of the dropped parameter is accepted (the `#2125` rule does not apply there).
meta def buildSelfIndex : CommandElabM Unit := do
  let HNat := mkApp (mkConst `H) (mkConst ``Nat)
  let Ht := mkForall `i .default (mkSort 1) (mkSort 1)
  let ct := mkForall `l .default (mkApp (mkConst ``L) (mkApp (mkConst `H) HNat)) HNat
  mkInd [] 0 [{ name := `H, type := Ht, ctors := [{ name := `H.mk, type := ct }] }]

elab "mkselfindex" : command => buildSelfIndex

/--
info: num parameters: 0, universe parameters: []
inductive H : Type → Type
  | H.mk : L (H (H Nat)) → H Nat
---
info: accepted
-/
#guard_msgs in
mkselfindex

-- A constructor's parameter binder only has to be *definitionally equal* to the corresponding
-- parameter of the type former, which `check_constructors` verifies. The check must therefore accept
-- an occurrence applied to that binder, here `p : IdT Type` standing in for `p : Type`.
meta def buildDefeqParam : CommandElabM Unit := do
  let Vt := mkForall `p .default (mkSort 1) (mkSort 1)
  let ct := mkForall `p .default (mkApp (mkConst ``IdT) (mkSort 1)) <|
    mkForall `l .default (mkApp (mkConst ``L) (mkApp (mkConst `V) (mkBVar 0)))
      (mkApp (mkConst `V) (mkBVar 1))
  mkInd [] 1 [{ name := `V, type := Vt, ctors := [{ name := `V.mk, type := ct }] }]

elab "mkdefeqparam" : command => buildDefeqParam

/--
info: num parameters: 1, universe parameters: []
inductive V : Type → Type
  | V.mk : (p : IdT Type) → L (V p) → V p
---
info: accepted
-/
#guard_msgs in
mkdefeqparam

-- A constructor type whose leading binders are not the parameters is rejected downstream, so the
-- check need not (and does not) recognize the situation: `C.mk` applies `C` to a `let`-bound
-- variable, which looks like the parameter at that binder depth.
meta def buildLetParam : CommandElabM Unit := do
  let Ct := mkForall `p .default (mkSort 1) (mkSort 1)
  let ct := .letE `x (mkSort 1) (mkConst ``Nat)
    (mkForall `p .default (mkSort 1) (mkApp (mkConst `C) (mkBVar 1))) false
  mkInd [] 1 [{ name := `C, type := Ct, ctors := [{ name := `C.mk, type := ct }] }]

elab "mkletparam" : command => buildLetParam

/--
info: num parameters: 1, universe parameters: []
inductive C : Type → Type
  | C.mk : let x := Nat;
Type → C x
---
error: (kernel) invalid inductive datatype declaration, incorrect number of parameters
-/
#guard_msgs in
mkletparam

-- Uniform occurrences are still accepted. The frontend normalizes the occurrences it accepts, so
-- `Ignore (T (id p))` below reaches the kernel as `Ignore (T p)`.
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
