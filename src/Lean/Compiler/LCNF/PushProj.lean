/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.Internalize

namespace Lean.Compiler.LCNF

/-!
This pass pushes projections into directly neighboring nested case statements.

Suppose we have an LCNF pure input that looks as follows:
```
cases a with
| alt1 p1 p2 =>
  cases b with
  | alt2 p3 p4 =>
    ...
  | alt3 p5 p6 =>
    ...
| ...
```
ToImpure will convert this into:
```
cases a with
| alt1 p1 p2 =>
  let p1 := proj[0] a;
  let p2 := proj[1] a;
  cases b with
  | alt2 p3 p4 =>
    let p3 := proj[0] b;
    let p4 := proj[1] b;
    ...
  | alt3 p5 p6 =>
    let p5 := proj[0] b;
    let p6 := proj[1] b;
    ...
| ...
```
Let's assume `p1` is used in both `alt2` and `alt3` and `p2` is used only in `alt3` then this pass
will convert the code into:
```
cases a with
| alt1 p1 p2 =>
  cases b with
  | alt2 p3 p4 =>
    let p1 := proj[0] a;
    let p3 := proj[0] b;
    let p4 := proj[1] b;
    ...
  | alt3 p5 p6 =>
    let p1 := proj[0] a;
    let p2 := proj[1] a;
    let p5 := proj[0] b;
    let p6 := proj[1] b;
    ...
| ...
```
This helps to avoid loading memory that is not actually required in all branches.

Note that unlike `floatLetIn`, this pass is willing to duplicate projections that are being pushed
around.


TODO: we suspect it might also help with reuse analysis, check this. This pass was ported from IR to
LCNF.
-/

mutual

partial def Cases.pushProjs (c : Cases .impure) (decls : Array (CodeDecl .impure)) :
    CompilerM (Code .impure) := do
  let altsUsed := c.alts.map (·.getCode.collectUsed)
  let ctxUsed := ({} : FVarIdHashSet) |>.insert c.discr
  let (bs, alts) ← go decls c.alts altsUsed #[] ctxUsed
  let alts ← alts.mapMonoM (·.mapCodeM Code.pushProj)
  let c := c.updateAlts alts
  return attachCodeDecls bs (.cases c)
where
  /-
  Here:
  - `decls` are the declarations that are still under consideration for being pushed into `alts`
  - `alts` are the alternatives of the current case arms,
  - `altsUsed` contains the used fvars per arm, both these sets and `alts` will be updated as we push
    things into them
  - `ctx` is the set of declarations that we decided not to push into any alt already
  - `ctxUsed` fulfills the same purpose as `altsUsed` for `ctx`
  -/
  go (decls : Array (CodeDecl .impure)) (alts : Array (Alt .impure)) (altsUsed : Array FVarIdHashSet)
      (ctx : Array (CodeDecl .impure)) (ctxUsed : FVarIdHashSet) :
      CompilerM (Array (CodeDecl .impure) × Array (Alt .impure)) :=
    if decls.isEmpty then
      return (ctx.reverse, alts)
    else
      let b := decls.back!
      let bs := decls.pop
      let done := return (bs.push b ++ ctx.reverse, alts)
      let skip := go bs alts altsUsed (ctx.push b) (b.collectUsed ctxUsed)
      let push (fvar : FVarId) : CompilerM (Array (CodeDecl .impure) × Array (Alt .impure)) := do
        if !ctxUsed.contains fvar then
          let alts ← alts.mapIdxM fun i alt => alt.mapCodeM fun k => do
            if altsUsed[i]!.contains fvar then
              return attachCodeDecls #[b] k
            else
              return k
          let altsUsed := altsUsed.map fun used =>
            if used.contains fvar then
              b.collectUsed used
            else
              used
          go bs alts altsUsed ctx ctxUsed
        else
          skip
      match b with
      | .let decl =>
        match decl.value with
        | .uproj .. | .oproj .. | .sproj .. => push decl.fvarId
        -- TODO | .isShared .. => skip
        | _ => done
      | _ => done

partial def Code.pushProj (code : Code .impure) : CompilerM (Code .impure) := do
  go code #[]
where
  go (c : Code .impure) (decls : Array (CodeDecl .impure)) : CompilerM (Code .impure) := do
    match c with
    | .let decl k => go k (decls.push (.let decl))
    | .jp decl k =>
      let decl ← decl.updateValue (← decl.value.pushProj)
      go k (decls.push (.jp decl))
    | .uset var i y k _ =>
      go k (decls.push (.uset var i y))
    | .sset var i offset y ty k _ =>
      go k (decls.push (.sset var i offset y ty))
    | .inc fvarId n check persistent k _ =>
      go k (decls.push (.inc fvarId n check persistent))
    | .dec fvarId n check persistent k _ =>
      go k (decls.push (.dec fvarId n check persistent))
    | .cases c => c.pushProjs decls
    | .jmp .. | .return .. | .unreach .. =>
      return attachCodeDecls decls c

end

def Decl.pushProj (decl : Decl .impure) : CompilerM (Decl .impure) := do
  let value ← decl.value.mapCodeM (·.pushProj)
  let decl := { decl with value }
  decl.internalize

public def pushProj (occurrence : Nat) : Pass :=
  Pass.mkPerDeclaration `pushProj .impure Decl.pushProj occurrence

builtin_initialize
  registerTraceClass `Compiler.pushProj (inherited := true)

end Lean.Compiler.LCNF
