/-
Copyright (c) 2024 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/
module

prelude
public import Lean.Compiler.IR.Basic
public import Std.Data.TreeMap

public section

namespace Lean.IR
namespace SSA

private abbrev MaxM := StateM Index

private def visitIndex (i : Index) : MaxM Unit :=
  modify (·.max i)

private def visitVar (x : VarId) : MaxM Unit :=
  visitIndex x.idx

private def visitJP (j : JoinPointId) : MaxM Unit :=
  visitIndex j.idx

private def visitArg : Arg → MaxM Unit
  | .var x => visitVar x
  | .erased => pure ()

private def visitExpr : Expr → MaxM Unit
  | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x | .reset _ x |
    .isShared x => visitVar x
  | .ctor _ args | .fap _ args | .pap _ args => args.forM visitArg
  | .ap x args | .reuse x _ _ args => do
    visitVar x
    args.forM visitArg
  | .lit _ => pure ()

private partial def maxIndex : FnBody → MaxM Unit
  | .vdecl x _ value next => do
    visitVar x
    visitExpr value
    maxIndex next
  | .jdecl j params body next => do
    visitJP j
    params.forM (visitVar ·.x)
    maxIndex body
    maxIndex next
  | .set x _ y next => do
    visitVar x
    visitArg y
    maxIndex next
  | .uset x _ y next | .sset x _ _ y _ next => do
    visitVar x
    visitVar y
    maxIndex next
  | .setTag x _ next | .inc x _ _ _ next | .dec x _ _ _ next | .del x next => do
    visitVar x
    maxIndex next
  | .case _ x _ alts => do
    visitVar x
    alts.forM (maxIndex ·.body)
  | .jmp j args => do
    visitJP j
    args.forM visitArg
  | .ret arg => visitArg arg
  | .unreachable => pure ()

/-- State for SSA conversion tracking variable versions -/
structure State where
  nextVersion : Std.TreeMap VarId VarId (fun a b => compare a.idx b.idx)
  nextIdx : Index

abbrev M := StateM State

@[inline] def mkFreshVar : M VarId := do
  let idx := (← get).nextIdx
  modify fun s => { s with nextIdx := idx + 1 }
  return ⟨idx⟩

def getVersion (x : VarId) : M VarId := do
  let s ← get
  match s.nextVersion.get? x with
  | some v => return v
  | none => return x

def setVersion (x : VarId) (v : VarId) : M Unit :=
  modify fun s => { s with nextVersion := s.nextVersion.insert x v }

def convertArg : Arg → M Arg
  | .var x => .var <$> getVersion x
  | .erased => pure .erased

def convertArgs (args : Array Arg) : M (Array Arg) :=
  args.mapM convertArg

mutual

  partial def convertExpr : Expr → M Expr
    | .ctor i ys => .ctor i <$> convertArgs ys
    | .reset n x => .reset n <$> getVersion x
    | .reuse x i h ys => do
      let x' ← getVersion x
      let ys' ← convertArgs ys
      return .reuse x' i h ys'
    | .proj i x => .proj i <$> getVersion x
    | .uproj i x => .uproj i <$> getVersion x
    | .sproj n o x => .sproj n o <$> getVersion x
    | .fap f ys => .fap f <$> convertArgs ys
    | .pap f ys => .pap f <$> convertArgs ys
    | .ap x ys => do
      let x' ← getVersion x
      let ys' ← convertArgs ys
      return .ap x' ys'
    | .box ty x => .box ty <$> getVersion x
    | .unbox x => .unbox <$> getVersion x
    | .lit v => pure (.lit v)
    | .isShared x => .isShared <$> getVersion x

  partial def convertFnBody : FnBody → M FnBody
    | .vdecl x ty e b => do
      let e' ← convertExpr e
      let x' ← mkFreshVar
      setVersion x x'
      let b' ← convertFnBody b
      return .vdecl x' ty e' b'

    | .jdecl j ps v b => do
      -- Save current renamings
      let savedVersions := (← get).nextVersion
      -- Rename parameters
      let mut renamedPs := Array.mkEmpty ps.size
      for p in ps do
        let x' ← mkFreshVar
        setVersion p.x x'
        renamedPs := renamedPs.push { p with x := x' }
      let v' ← convertFnBody v
      -- Restore renamings before converting continuation
      modify fun s => { s with nextVersion := savedVersions }
      let b' ← convertFnBody b
      return .jdecl j renamedPs v' b'

    | .set x _i y b => do
      -- Convert set to new binding: x₂ := update x₁ i y
      let xOld ← getVersion x
      let y' ← convertArg y
      let xNew ← mkFreshVar
      setVersion x xNew
      let b' ← convertFnBody b
      -- Create update operation as ctor
      let updateExpr :=
        .ctor { name := `update, cidx := 0, size := 1, usize := 0, ssize := 0 }
          #[.var xOld, y']
      return .vdecl xNew .object updateExpr b'

    | .uset x _i y b => do
      let xOld ← getVersion x
      let yVer ← getVersion y
      let xNew ← mkFreshVar
      setVersion x xNew
      let b' ← convertFnBody b
      let updateExpr :=
        .ctor { name := `uset, cidx := 0, size := 1, usize := 1, ssize := 0 }
          #[.var xOld, .var yVer]
      return .vdecl xNew .object updateExpr b'

    | .sset x _i _o y _ty b => do
      let xOld ← getVersion x
      let yVer ← getVersion y
      let xNew ← mkFreshVar
      setVersion x xNew
      let b' ← convertFnBody b
      let updateExpr :=
        .ctor { name := `sset, cidx := 0, size := 1, usize := 0, ssize := 8 }
          #[.var xOld, .var yVer]
      return .vdecl xNew .object updateExpr b'

    | .setTag x c b => do
      let xOld ← getVersion x
      let xNew ← mkFreshVar
      setVersion x xNew
      let b' ← convertFnBody b
      let tagExpr :=
        .ctor { name := `tag, cidx := c, size := 0, usize := 0, ssize := 0 }
          #[.var xOld]
      return .vdecl xNew .tagged tagExpr b'

    | .inc x n c persistent b => do
      let x' ← getVersion x
      let b' ← convertFnBody b
      return .inc x' n c persistent b'

    | .dec x n c persistent b => do
      let x' ← getVersion x
      let b' ← convertFnBody b
      return .dec x' n c persistent b'

    | .del x b => do
      let x' ← getVersion x
      let b' ← convertFnBody b
      return .del x' b'

    | .case tid x xType cs => do
      let x' ← getVersion x
      let state0 ← get
      let baseVersion := state0.nextVersion
      let mut nextIdx := state0.nextIdx
      let mut newAlts := Array.mkEmpty cs.size
      for alt in cs do
        modify fun s => { s with nextVersion := baseVersion, nextIdx := nextIdx }
        let alt' ← convertAlt alt
        newAlts := newAlts.push alt'
        let afterAlt ← get
        nextIdx := afterAlt.nextIdx
      modify fun s => { s with nextVersion := baseVersion, nextIdx := nextIdx }
      return .case tid x' xType newAlts

    | .ret x => .ret <$> convertArg x

    | .jmp j ys =>
      return .jmp j (← convertArgs ys)

    | .unreachable => pure .unreachable

  partial def convertAlt : Alt → M Alt
    | .ctor info b => .ctor info <$> convertFnBody b
    | .default b => .default <$> convertFnBody b

end

@[inline] def runOnBody (body : FnBody) (startIdx : Index) : FnBody :=
  let initState : State := { nextVersion := {}, nextIdx := startIdx }
  (convertFnBody body).run' initState

/-- Convert function body to SSA form -/
def toSSA (b : FnBody) (maxIdx : Index := 0) : FnBody :=
  runOnBody b (maxIdx + 1)

/-- Convert parameters and body to SSA form -/
def convertDecl : Decl → Decl
  | .fdecl f ps ty body info =>
    let maxIdx := (maxIndex body).run 0 |>.2
    let initState : State := { nextVersion := {}, nextIdx := maxIdx + 1 }
    let ((params', body'), _) :=
      (do
        let rec renameList : List Param → M (List Param)
          | [] => pure []
          | p :: rest => do
              let x' ← mkFreshVar
              setVersion p.x x'
              let rest' ← renameList rest
              pure ({ p with x := x' } :: rest')
        let paramsList ← renameList ps.toList
        let params' := paramsList.toArray
        let body' ← convertFnBody body
        pure (params', body')
      ).run initState
    .fdecl f params' ty body' info
  | d => d

end SSA
end Lean.IR
