/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.Types

namespace Lean.Compiler.LCNF
namespace FixedParams

/-! # Fixed Parameter Static Analyzer -/

/-
If function is partially applied, we assume missing parameters are not fixed.
Note that, since LCNF is in A-normal form, if function is used as an argument, none of its parameters
will be considered fixed.

We assume functions that are not in mutual block do not invoke the function being
analyzed.

We track fixed arguments using "abstract values". They are just a "token" or ⊤.
We can view it as a form of constant propagation.

When analyzing a function call to another function in the same mutual block,
we visit its body after binding its parameters to "abstract values". We keep a cache
of the already visited pairs ("declName", "abstract values").

Whenever, we find a recursive call to the function being analyzed, we check whether
the arguments match the initial "abstract values".

We interrupt the analysis if all parameters of the function being analyzed have been
marked as not fixed.
-/

/-- Abstract value for the "fixed parameter" analysis. -/
inductive Value where
  | top
  | erased
  | val (i : Nat)
  deriving Inhabited, BEq, Hashable

structure Context where
  /-- Declaration in the same mutual block. -/
  decls : Array Decl
  /--
  Function being analyzed. We check every recursive call to this function.
  Remark: `main` is in `decls`.
  -/
  main : Decl
  /--
  The assignment maps free variable ids in the current code being analyzed to abstract values.
  We only track the abstract value assigned to parameters.
  -/
  assignment : FVarIdMap Value

structure State where
  /--
  Set of calls that have been already analyzed.
  Recall that we assume that only functions in `decls` may have recursive calls to the function being analyzed (i.e., `main`).
  Whenever there is function application `f a₁ ... aₙ`, where `f` is in `decls`, `f` is not `main`, and
  we visit with the abstract values assigned to `aᵢ`, but first we record the visit here.
  -/
  visited : HashSet (Name × Array Value) := {}
  /--
  Bitmask containing the result, i.e., which parameters of `main` are fixed.
  We initialize it with `true` everywhere.
  -/
  fixed : Array Bool

/-- Monad for the fixed parameter static analyzer. We use the unit-exception to interrupt the analysis. -/
abbrev FixParamM := ReaderT Context <| EStateM Unit State

/-- Stop the analysis and mark all parameters as non-fixed. -/
abbrev abort : FixParamM α := do
  modify fun s => { s with fixed := s.fixed.map fun _ => false }
  throw ()

def evalArg (arg : Expr) : FixParamM Value := do
  if arg.isErased then
    return .erased
  let .fvar fvarId := arg | return .top
  let some val := (← read).assignment.find? fvarId | return .top
  return val

def inMutualBlock (declName : Name) : FixParamM Bool :=
  return (← read).decls.any (·.name == declName)

def mkAssignment (decl : Decl) (values : Array Value) : FVarIdMap Value := Id.run do
  let mut assignment := {}
  for param in decl.params, value in values do
    assignment := assignment.insert param.fvarId value
  return assignment

mutual

partial def evalExpr (e : Expr) : FixParamM Unit := do
  match e with
  | .const declName _ => evalApp declName #[]
  | .app .. =>
    let .const declName _ := e.getAppFn | return ()
    if (← inMutualBlock declName) then
      evalApp declName e.getAppArgs
  | _ => return ()

partial def evalCode (code : Code) : FixParamM Unit := do
  match code with
  | .let decl k => evalExpr decl.value; evalCode k
  | .fun decl k | .jp decl k => evalCode decl.value; evalCode k
  | .cases c => c.alts.forM fun alt => evalCode alt.getCode
  | .unreach .. | .jmp .. | .return .. => return ()

partial def evalApp (declName : Name) (args : Array Expr) : FixParamM Unit := do
  let main := (← read).main
  if declName == main.name then
    -- Recursive call to the function being analyzed
    for h : i in [:main.params.size] do
      if _h : i < args.size then
        have : i < main.params.size := h.upper
        let param := main.params[i]
        let val ← evalArg args[i]
        unless val == .val i || (val == .erased && param.type.isErased) do
          -- Found non fixed argument
          -- Remark: if the argument is erased and the type of the parameter is erased we assume it is a fixed "propositonal" parameter.
          modify fun s => { s with fixed := s.fixed.set! i false }
      else
        -- Partial application mark argument as not fixed
        modify fun s => { s with fixed := s.fixed.set! i false }
    unless (← get).fixed.contains true do
      throw () -- stop analysis, none of the arguments are fixed.
  for decl in (← read).decls do
    if declName == decl.name then
      -- Call to another function in the same mutual block.
      let mut values := #[]
      for i in [:decl.params.size] do
        if h : i < args.size then
          values := values.push (← evalArg args[i])
        else
          values := values.push .top
      let key := (declName, values)
      unless (← get).visited.contains key do
        modify fun s => { s with visited := s.visited.insert key }
        let assignment := mkAssignment decl values
        withReader (fun ctx => { ctx with assignment }) <| evalCode decl.value

end

def mkInitialValues (numParams : Nat) : Array Value := Id.run do
  let mut values := #[]
  for i in [:numParams] do
    values := values.push <| .val i
  return values

end FixedParams
open FixedParams

/--
Given the (potentially mutually) recursive declarations `decls`,
return a map from declaration name `decl.name` to a bit-mask `m` where `m[i]` is true
iff the `decl.params[i]` is a fixed argument. That is, it does not change in recursive
applications.
The function assumes that if a function `f` was declared in a mutual block, then `decls`
contains all (computationally relevant) functions in the mutual block.
-/
def mkFixedParamsMap (decls : Array Decl) : NameMap (Array Bool) := Id.run do
  let mut result := {}
  for decl in decls do
    let values := mkInitialValues decl.params.size
    let assignment := mkAssignment decl values
    let fixed := Array.mkArray decl.params.size true
    match evalCode decl.value |>.run { main := decl, decls, assignment } |>.run { fixed } with
    | .ok _ s | .error _ s => result := result.insert decl.name s.fixed
  return result

end Lean.Compiler.LCNF
