/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.IR.CompilerM

/-!
This module "topologically sorts" an SCC of decls (an SCC of decls in the pipeline may in fact
contain more than one SCC at the moment). This is relevant because EmitC relies on the invariant
that the constants (and in particular also the closed terms) occur in a reverse topologically sorted
order for emitting them.
-/

namespace Lean.IR

structure TopoState where
  declsMap : Std.HashMap Name Decl
  seen : Std.HashSet Name
  order : Array Decl

abbrev ToposortM := StateRefT TopoState CompilerM

partial def toposort (decls : Array Decl) : CompilerM (Array Decl) := do
  let declsMap := .ofList (decls.toList.map (fun d => (d.name, d)))
  let (_, s) ← go decls |>.run {
    declsMap,
    seen := .emptyWithCapacity decls.size,
    order := .emptyWithCapacity decls.size
  }
  return s.order
where
  go (decls : Array Decl) : ToposortM Unit := do
    decls.forM process

  process (decl : Decl) : ToposortM Unit := do
    if (← get).seen.contains decl.name then
      return ()

    modify fun s => { s with seen := s.seen.insert decl.name }
    let .fdecl (body := body) .. := decl | unreachable!
    processBody body
    modify fun s => { s with order := s.order.push decl }

  processBody (b : FnBody) : ToposortM Unit := do
    match b with
    | .vdecl _ _ e b =>
      match e with
      | .fap c .. | .pap c .. =>
        if let some decl := (← get).declsMap[c]? then
          process decl
      | _ => pure ()
      processBody b
    | .jdecl _ _ v b =>
      processBody v
      processBody b
    | .case _ _ _ cs => cs.forM (fun alt => processBody alt.body)
    | .jmp .. | .ret .. | .unreachable => return ()
    | _ => processBody b.body


public def toposortDecls (decls : Array Decl) : CompilerM (Array Decl) := do
  let (externDecls, otherDecls) := decls.partition (fun decl => decl.isExtern)
  let otherDecls ← toposort otherDecls
  return externDecls ++ otherDecls

end Lean.IR
