/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Term

namespace Lean.Elab.Term
namespace MatchExpr
/--
`match_expr` alternative. Recall that it has the following structure.
```
| (ident "@")? ident bindeIdent* => rhs
```

Example:
```
| c@Eq _ a b => f c a b
```
-/
structure Alt where
  /--
  `some c` if there is a variable binding to the function symbol being matched.
  `c` is the variable name.
  -/
  var?    : Option Ident
  /-- Function being matched. -/
  funName : Ident
  /-- Pattern variables. The list uses `none` for representing `_`, and `some a` for pattern variable `a`. -/
  pvars   : List (Option Ident)
  /-- right-hand-side for the alternative. -/
  rhs     : Syntax
  /-- Store the auxliary continuation function for each right-hand-side. -/
  k       : Ident := ⟨.missing⟩
  /-- Actual value to be passed as an argument. -/
  actuals : List Term := []

/--
`match_expr` else-alternative. Recall that it has the following structure.
```
| _ => rhs
```
-/
structure ElseAlt where
  rhs : Syntax

open Parser Term

/--
Converts syntax representing a `match_expr` else-alternative into an `ElseAlt`.
-/
def toElseAlt? (stx : Syntax) : Option ElseAlt :=
  if !stx.isOfKind ``matchExprElseAlt then none else
  some { rhs := stx[3] }

/--
Converts syntax representing a `match_expr` alternative into an `Alt`.
-/
def toAlt? (stx : Syntax) : Option Alt :=
  if !stx.isOfKind ``matchExprAlt then none else
  match stx[1] with
  | `(matchExprPat| $[$var? @]? $funName:ident $pvars*) =>
    let pvars := pvars.toList.reverse.map fun arg =>
      match arg.raw with
      | `(_) => none
      | _ => some ⟨arg⟩
    let rhs := stx[3]
    some { var?, funName, pvars, rhs }
  | _ => none

/--
Returns the function names of alternatives that do not have any pattern variable left.
-/
def getFunNamesToMatch (alts : List Alt) : List Ident := Id.run do
  let mut funNames := #[]
  for alt in alts do
    if alt.pvars.isEmpty then
      if Option.isNone <| funNames.find? fun funName => funName.getId == alt.funName.getId then
        funNames := funNames.push alt.funName
  return funNames.toList

/--
Returns `true` if there is at least one alternative whose next pattern variable is not a `_`.
-/
def shouldSaveActual (alts : List Alt) : Bool :=
  alts.any fun alt => alt.pvars matches some _ :: _

/--
Returns the first alternative whose function name is `funName` **and**
does not have pattern variables left to match.
-/
def getAltFor? (alts : List Alt) (funName : Ident) : Option Alt :=
  alts.find? fun alt => alt.funName.getId == funName.getId && alt.pvars.isEmpty

/--
Removes alternatives that do not have any pattern variable left to be matched.
For the ones that still have pattern variables, remove the first one, and
save `actual` if the removed pattern variable is not a `_`.
-/
def next (alts : List Alt) (actual : Term) : List Alt :=
  alts.filterMap fun alt =>
    if let some _ :: pvars := alt.pvars then
      some { alt with pvars, actuals := actual :: alt.actuals }
    else if let none :: pvars := alt.pvars then
      some { alt with pvars }
    else
      none

/--
Creates a fresh identifier for representing the continuation function used to
execute the RHS of the given alternative, and stores it in the field `k`.
-/
def initK (alt : Alt) : MacroM Alt := withFreshMacroScope do
  -- Remark: the compiler frontend implemented in C++ currently detects jointpoints created by
  -- the "do" notation by testing the name. See hack at method `visit_let` at `lcnf.cpp`
  -- We will remove this hack when we re-implement the compiler frontend in Lean.
  let k : Ident ← `(__do_jp)
  return { alt with k }

/--
Generates parameters for the continuation function used to execute
the RHS of the given alternative.
-/
def getParams (alt : Alt) : MacroM (Array (TSyntax ``bracketedBinder)) := do
  let mut params := #[]
  if let some var := alt.var? then
    params := params.push (← `(bracketedBinderF| ($var : Expr)))
  params := params ++ (← alt.pvars.toArray.reverse.filterMapM fun
    | none => return none
    | some arg => return some (← `(bracketedBinderF| ($arg : Expr))))
  if params.isEmpty then
    return #[(← `(bracketedBinderF| (_ : Unit)))]
  return params

/--
Generates the actual arguments for invoking the auxiliary continuation function
associated with the given alternative. The arguments are the actuals stored in `alt`.
`discr` is also an argument if `alt.var?` is not none.
-/
def getActuals (discr : Term) (alt : Alt) : MacroM (Array Term) := do
  let mut actuals := #[]
  if alt.var?.isSome then
    actuals := actuals.push discr
  actuals := actuals ++ alt.actuals.toArray
  if actuals.isEmpty then
    return #[← `(())]
  return actuals

def toDoubleQuotedName (ident : Ident) : Term :=
  ⟨mkNode ``Parser.Term.doubleQuotedName #[mkAtom "`", mkAtom "`", ident]⟩

/--
Generates an `if-then-else` tree for implementing a `match_expr` with discriminant `discr`,
alternatives `alts`, and else-alternative `elseAlt`.
-/
partial def generate (discr : Term) (alts : List Alt) (elseAlt : ElseAlt) : MacroM Syntax := do
  let alts ← alts.mapM initK
  let discr' ← `(__discr)
  -- Remark: the compiler frontend implemented in C++ currently detects jointpoints created by
  -- the "do" notation by testing the name. See hack at method `visit_let` at `lcnf.cpp`
  -- We will remove this hack when we re-implement the compiler frontend in Lean.
  let kElse ← `(__do_jp)
  let rec loop (discr : Term) (alts : List Alt) : MacroM Term := withFreshMacroScope do
    let funNamesToMatch := getFunNamesToMatch alts
    let saveActual := shouldSaveActual alts
    let actual ← if saveActual then `(a) else `(_)
    let altsNext := next alts actual
    let body ← if altsNext.isEmpty then
      `($kElse ())
    else
      let discr' ← `(__discr)
      let body ← loop discr' altsNext
      if saveActual then
        `(if h : ($discr).isApp then let a := Expr.appArg $discr h; let __discr := Expr.appFnCleanup $discr h; $body else $kElse ())
      else
        `(if h : ($discr).isApp then let __discr := Expr.appFnCleanup $discr h; $body else $kElse ())
    let mut result := body
    for funName in funNamesToMatch do
      if let some alt := getAltFor? alts funName then
        let actuals ← getActuals discr alt
        result ← `(if ($discr).isConstOf $(toDoubleQuotedName funName) then $alt.k $actuals* else $result)
    return result
  let body ← loop discr' alts
  let mut result ← `(let_delayed __do_jp (_ : Unit) := $(⟨elseAlt.rhs⟩):term; let __discr := Expr.cleanupAnnotations $discr:term; $body:term)
  for alt in alts do
    let params ← getParams alt
    result ← `(let_delayed $alt.k:ident $params:bracketedBinder* := $(⟨alt.rhs⟩):term; $result:term)
  return result

def main (discr : Term) (alts : Array Syntax) (elseAlt : Syntax) : MacroM Syntax := do
  let alts ← alts.toList.mapM fun alt =>
    if let some alt := toAlt? alt then
      pure alt
    else
      Macro.throwErrorAt alt "unexpected `match_expr` alternative"
  let some elseAlt := toElseAlt? elseAlt
    | Macro.throwErrorAt elseAlt "unexpected `match_expr` else-alternative"
  generate discr alts elseAlt

end MatchExpr

@[builtin_macro Lean.Parser.Term.matchExpr] def expandMatchExpr : Macro := fun stx =>
  match stx with
  | `(match_expr $discr:term with $alts) =>
    MatchExpr.main discr alts.raw[0].getArgs alts.raw[1]
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.letExpr] def expandLetExpr : Macro := fun stx =>
  match stx with
  | `(let_expr $pat:matchExprPat := $discr:term | $elseBranch:term; $body:term) =>
    `(match_expr $discr with
      | $pat:matchExprPat => $body
      | _ => $elseBranch)
  | _ => Macro.throwUnsupported

end Lean.Elab.Term
