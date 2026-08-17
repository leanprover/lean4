import Lean

open Lean

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace RecClass

def rcStep (x : Bool) (n : Nat) (ih : (m : Nat) → m < n → Bool) : Bool :=
  match n with
  | 0 => x
  | k + 1 => ih k (Nat.lt_succ_self k)

def rcRun (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => rcStep x m) h

opaque rcOpaque : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def rcA (x : Bool) := rcRun x 1 rcOpaque
def rcB (x : Bool) := rcRun x 1 (Acc.intro 1 fun _ => Acc.inv rcOpaque)
def rcC (x : Bool) := rcRun x 0 (Acc.inv rcOpaque (Nat.lt_succ_self 0))

end RecClass

namespace Core64Repro

private def a : Name := .num (.num `Native64TwoHashA 0) 572478232
private def b : Name := .num (.num `Native64TwoHashB 0) 2525080234
private def c : Name := .num (.num `Native64TwoHashC 0) 3119207123
private def gate : Name := `Native64TwoHashGate
private def owner : Name := `Native64TwoHashOwner
private def bool := mkConst ``Bool

private def checked (env : Environment) (decl : Declaration) : CoreM Environment := do
  match env.addDeclCore 800000 8000 decl none with
  | .ok next => return next
  -- Report only that the kernel rejected the declaration. The rejected term is ill-typed, and its
  -- pretty-printed form is not stable across environments, so we do not include it in the message.
  | .error _ => throwError "kernel error"

private def pad (salt : Nat) (e : Expr) : Expr :=
  mkApp (mkLambda `salt .default (mkConst ``Nat) (e.liftLooseBVars 0 1)) (mkNatLit salt)

private def values (x : Expr) : Array Expr :=
  let px := pad 101831 x
  let qx := pad 47770 (mkApp (mkLambda `z .default bool (.bvar 0)) x)
  #[mkApp (mkConst a) px, mkApp (mkConst b) px, mkApp (mkConst c) qx]

private def canonical (v : Array Expr) : Array Expr := #[v[2]!, v[1]!, v[0]!, v[2]!]
private def requested (v : Array Expr) : Array Expr := #[v[1]!, v[0]!, v[0]!, v[0]!]

private def gateCall (x : Expr) (args : Array Expr) (major result : Expr) : Expr :=
  let majorType := mkAppN (mkConst gate)
    #[x.liftLooseBVars 0 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]
  let motive := (List.range 4).foldr
    (fun _ body => mkLambda `index .default bool body)
    (mkLambda `proof .default majorType (mkSort 1))
  mkAppN (mkConst (.str gate "rec") [Level.succ Level.one])
    (#[x, motive, result] ++ args ++ #[major])

private def gateDecl : Declaration :=
  let x := mkBVar 0
  let result := mkAppN (mkConst gate) (#[x] ++ canonical (values x))
  .inductDecl [] 1 [{
    name := gate
    type := (List.range 5).foldr (fun _ body => mkForall `bit .default bool body) (mkSort 0)
    ctors := [{name := .str gate "intro", type := mkForall `x .default bool result}]
  }] false

private def ownerDecl : Declaration :=
  let self := mkConst owner
  let x := mkBVar 0
  let proofType := mkAppN (mkConst gate) (#[x] ++ requested (values x))
  let x := mkBVar 1
  let childType := gateCall x (requested (values x)) (.bvar 0) self
  .inductDecl [] 0 [{
    name := owner, type := mkSort 1
    ctors := [{name := .str owner "base", type := self},
      {name := .str owner "step", type := mkForall `x .default bool <|
        mkForall `h .default proofType <| mkForall `child .default childType self}]
  }] false

/--
error: kernel error
-/
#guard_msgs in
run_meta do
  let mut env ← getEnv
  for (name, value) in [(a, ``RecClass.rcA), (b, ``RecClass.rcB), (c, ``RecClass.rcC)] do
    env ← checked env (.defnDecl {
      name, levelParams := [], type := mkForall `x .default bool bool,
      value := mkConst value, hints := .regular 1021, safety := .safe})
  for i in [3, 9] do
    let v := values (.fvar ⟨.num `_ind_fresh i⟩)
    unless v[0]!.hash == v[2]!.hash do throwError "required collision changed at {i}"
  let v := values (.fvar ⟨.num `_ind_fresh 14⟩)
  unless v[0]!.hash != v[2]!.hash do throwError "unexpected collision at 14"
  env ← checked env gateDecl
  env ← checked env ownerDecl
  setEnv env
  let some (.recInfo ri) := env.toKernelEnv.find? (.str owner "rec")
    | throwError "missing recursor"
  let .forallE _ _ t _ := ri.type | throwError "missing motive"
  let .forallE _ _ t _ := t | throwError "missing base minor"
  let .forallE _ stepType _ _ := t | throwError "missing step minor"
  let rec arity : Expr → Nat
    | .forallE _ _ body _ => arity body + 1
    | _ => 0
  let some rule := ri.rules.find? (·.ctor == .str owner "step")
    | throwError "missing step rule"
  let rec tail : Expr → Expr
    | .lam _ _ body _ => tail body
    | e => e
  unless arity stepType == 4 && (tail rule.rhs).getAppNumArgs == 3 do
    throwError "missing-IH signature changed"
  logInfo "Checked missing-IH producer: step minor expects 4 arguments; rule supplies 3."

#exit

-- Rest of the attack does not work anymore after previous command is rejected.

end Core64Repro

open RecClass

private theorem run_eq (x : Bool) (n : Nat) (h : Acc (· < ·) n) :
    rcRun x n h = x := by
  induction h with
  | intro n smaller ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [rcRun, rcStep] using ih n (Nat.lt_succ_self n)

private theorem gateConstant (x : Bool) (T : Type)
    (i j k l : Bool) (h : Native64TwoHashGate x i j k l) :
    Native64TwoHashGate.rec (motive := fun _ _ _ _ _ => Type) T h = T :=
  Native64TwoHashGate.rec
    (motive := fun _ _ _ _ h =>
      Native64TwoHashGate.rec (motive := fun _ _ _ _ _ => Type) T h = T)
    rfl h

private theorem gateTransport (G : Bool → Bool → Bool → Bool → Prop)
    (a b c : Bool) (ab : a = b) (bc : b = c)
    (h : G c b a c) : G b a a a := by
  cases ab
  cases bc
  exact h

private theorem gateWitness : Native64TwoHashGate false
    (rcB false) (rcA false) (rcA false) (rcA false) :=
  gateTransport (Native64TwoHashGate false) (rcA false) (rcB false) (rcC false)
    ((run_eq false _ _).trans (run_eq false _ _).symm)
    ((run_eq false _ _).trans (run_eq false _ _).symm)
    (Native64TwoHashGate.intro false)

private noncomputable def major : Native64TwoHashOwner :=
  Native64TwoHashOwner.step false gateWitness
    (Eq.mpr (gateConstant false Native64TwoHashOwner
      (rcB false) (rcA false) (rcA false) (rcA false) gateWitness)
      Native64TwoHashOwner.base)

-- The generated step rule omits its IH. Consequently this proposition reduces
-- to Bool, even though Bool is data in Type rather than a proposition.
private noncomputable def badProp : Prop :=
  Native64TwoHashOwner.rec (motive := fun _ => Type → Prop)
    (fun _ => True) (fun _ _ _ ih => ih) major Bool

private theorem propRepresentationFalse (P : Prop) (encode : Bool → P)
    (decode : P → Bool)
    (onFalse : decode (encode false) = false)
    (onTrue : decode (encode true) = true) : False := by
  have same : encode false = encode true := Subsingleton.elim _ _
  exact Bool.noConfusion (onFalse.symm.trans ((congrArg decode same).trans onTrue))

public theorem inconsistent : False :=
  propRepresentationFalse badProp (fun b => b) (fun p => p) rfl rfl
