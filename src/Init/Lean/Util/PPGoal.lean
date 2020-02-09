/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Lean.Util.PPExt

namespace Lean

def ppGoal (env : Environment) (mctx : MetavarContext) (opts : Options) (mvarId : MVarId) : Format :=
match mctx.findDecl? mvarId with
| none          => "unknown goal"
| some mvarDecl =>
  let indent := 2; -- Use option
  let lctx   := mvarDecl.lctx;
  let pp (e : Expr) : Format := ppExpr env mctx lctx opts e;
  let instMVars (e : Expr) : Expr := (mctx.instantiateMVars e).1;
  let addLine (fmt : Format) : Format := if fmt.isNil then fmt else fmt ++ Format.line;
  let pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : Format :=
    let fmt := addLine fmt;
    match ids, type? with
    | [], _        => fmt
    | _, none      => fmt
    | _, some type => fmt ++ (Format.joinSep ids.reverse " " ++ " :" ++ Format.nest indent (Format.line ++ pp type)).group;
  let (varNames, type?, fmt) := mvarDecl.lctx.foldl
    (fun (acc : List Name × Option Expr × Format) (localDecl : LocalDecl) =>
       let (varNames, prevType?, fmt) := acc;
       match localDecl with
       | LocalDecl.cdecl _ _ varName type _   =>
         let type := instMVars type;
         if prevType? == none || prevType? == some type then
           (varName :: varNames, some type, fmt)
         else
           let fmt := pushPending varNames prevType? fmt;
           ([varName], some type, fmt)
       | LocalDecl.ldecl _ _ varName type val =>
         let fmt  := pushPending varNames prevType? fmt;
         let fmt  := addLine fmt;
         let type := instMVars type;
         let val  := instMVars val;
         let fmt  := fmt ++ (format varName ++ " : " ++ pp type ++ " :=" ++ Format.nest indent (Format.line ++ pp val)).group;
         ([], none, fmt))
    ([], none, Format.nil);
  let fmt := pushPending varNames type? fmt;
  let fmt := addLine fmt;
  let fmt := fmt ++ "⊢" ++ " " ++ Format.nest indent (pp mvarDecl.type);
  match mvarDecl.userName with
  | Name.anonymous => fmt
  | name           => "case " ++ format name ++ Format.line ++ fmt

end Lean
