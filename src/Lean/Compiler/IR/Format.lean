/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.IR.Basic

namespace Lean
namespace IR

private def formatArg : Arg → Format
  | Arg.var id     => format id
  | Arg.irrelevant => "◾"

instance : ToFormat Arg := ⟨formatArg⟩

def formatArray {α : Type} [ToFormat α] (args : Array α) : Format :=
  args.foldl (fun r a => r ++ " " ++ format a) Format.nil

private def formatLitVal : LitVal → Format
  | LitVal.num v => format v
  | LitVal.str v => format (repr v)

instance : ToFormat LitVal := ⟨formatLitVal⟩

private def formatCtorInfo : CtorInfo → Format
  | { name := name, cidx := cidx, usize := usize, ssize := ssize, .. } => Id.run do
    let mut r := f!"ctor_{cidx}"
    if usize > 0 || ssize > 0 then
      r := f!"{r}.{usize}.{ssize}"
    if name != Name.anonymous then
      r := f!"{r}[{name}]"
    r

instance : ToFormat CtorInfo := ⟨formatCtorInfo⟩

private def formatExpr : Expr → Format
  | Expr.ctor i ys      => format i ++ formatArray ys
  | Expr.reset n x      => "reset[" ++ format n ++ "] " ++ format x
  | Expr.reuse x i u ys => "reuse" ++ (if u then "!" else "") ++ " " ++ format x ++ " in " ++ format i ++ formatArray ys
  | Expr.proj i x       => "proj[" ++ format i ++ "] " ++ format x
  | Expr.uproj i x      => "uproj[" ++ format i ++ "] " ++ format x
  | Expr.sproj n o x    => "sproj[" ++ format n ++ ", " ++ format o ++ "] " ++ format x
  | Expr.fap c ys       => format c ++ formatArray ys
  | Expr.pap c ys       => "pap " ++ format c ++ formatArray ys
  | Expr.ap x ys        => "app " ++ format x ++ formatArray ys
  | Expr.box _ x        => "box " ++ format x
  | Expr.unbox x        => "unbox " ++ format x
  | Expr.lit v          => format v
  | Expr.isShared x     => "isShared " ++ format x

instance : ToFormat Expr := ⟨formatExpr⟩
instance : ToString Expr := ⟨fun e => Format.pretty (format e)⟩

private partial def formatIRType : IRType → Format
  | IRType.float        => "float"
  | IRType.float32      => "float32"
  | IRType.uint8        => "u8"
  | IRType.uint16       => "u16"
  | IRType.uint32       => "u32"
  | IRType.uint64       => "u64"
  | IRType.usize        => "usize"
  | IRType.irrelevant   => "◾"
  | IRType.object       => "obj"
  | IRType.tobject      => "tobj"
  | IRType.struct _ tys =>
    let _ : ToFormat IRType := ⟨formatIRType⟩
    "struct " ++ Format.bracket "{" (Format.joinSep tys.toList ", ") "}"
  | IRType.union _ tys  =>
    let _ : ToFormat IRType := ⟨formatIRType⟩
    "union " ++ Format.bracket "{" (Format.joinSep  tys.toList ", ") "}"

instance : ToFormat IRType := ⟨formatIRType⟩
instance : ToString IRType := ⟨toString ∘ format⟩

private def formatParam : Param → Format
  | { x := name, borrow := b, ty := ty } => "(" ++ format name ++ " : " ++ (if b then "@& " else "") ++ format ty ++ ")"

instance : ToFormat Param := ⟨formatParam⟩

def formatAlt (fmt : FnBody → Format) (indent : Nat) : Alt → Format
  | Alt.ctor i b  => format i.name ++ " →" ++ Format.nest indent (Format.line ++ fmt b)
  | Alt.default b => "default →" ++ Format.nest indent (Format.line ++ fmt b)

def formatParams (ps : Array Param) : Format :=
  formatArray ps

def formatFnBodyHead : FnBody → Format
  | FnBody.vdecl x ty e _      => "let " ++ format x ++ " : " ++ format ty ++ " := " ++ format e
  | FnBody.jdecl j xs _ _      => format j ++ formatParams xs ++ " := ..."
  | FnBody.set x i y _         => "set " ++ format x ++ "[" ++ format i ++ "] := " ++ format y
  | FnBody.uset x i y _        => "uset " ++ format x ++ "[" ++ format i ++ "] := " ++ format y
  | FnBody.sset x i o y ty _   => "sset " ++ format x ++ "[" ++ format i ++ ", " ++ format o ++ "] : " ++ format ty ++ " := " ++ format y
  | FnBody.setTag x cidx _     => "setTag " ++ format x ++ " := " ++ format cidx
  | FnBody.inc x n _ _ _       => "inc" ++ (if n != 1 then Format.sbracket (format n) else "") ++ " " ++ format x
  | FnBody.dec x n _ _ _       => "dec" ++ (if n != 1 then Format.sbracket (format n) else "") ++ " " ++ format x
  | FnBody.del x _             => "del " ++ format x
  | FnBody.mdata d _           => "mdata " ++ format d
  | FnBody.case _   x _     _  => "case " ++ format x ++ " of ..."
  | FnBody.jmp j ys            => "jmp " ++ format j ++ formatArray ys
  | FnBody.ret x               => "ret " ++ format x
  | FnBody.unreachable         => "⊥"

@[export lean_ir_format_fn_body_head]
private def formatFnBodyHead' (fn : FnBody) : String :=
  formatFnBodyHead fn |>.pretty

partial def formatFnBody (fnBody : FnBody) (indent : Nat := 2) : Format :=
  let rec loop : FnBody → Format
    | FnBody.vdecl x ty e b      => "let " ++ format x ++ " : " ++ format ty ++ " := " ++ format e ++ ";" ++ Format.line ++ loop b
    | FnBody.jdecl j xs v b      => format j ++ formatParams xs ++ " :=" ++ Format.nest indent (Format.line ++ loop v) ++ ";" ++ Format.line ++ loop b
    | FnBody.set x i y b         => "set " ++ format x ++ "[" ++ format i ++ "] := " ++ format y ++ ";" ++ Format.line ++ loop b
    | FnBody.uset x i y b        => "uset " ++ format x ++ "[" ++ format i ++ "] := " ++ format y ++ ";" ++ Format.line ++ loop b
    | FnBody.sset x i o y ty b   => "sset " ++ format x ++ "[" ++ format i ++ ", " ++ format o ++ "] : " ++ format ty ++ " := " ++ format y ++ ";" ++ Format.line ++ loop b
    | FnBody.setTag x cidx b     => "setTag " ++ format x ++ " := " ++ format cidx ++ ";" ++ Format.line ++ loop b
    | FnBody.inc x n _ _ b       => "inc" ++ (if n != 1 then Format.sbracket (format n) else "") ++ " " ++ format x ++ ";" ++ Format.line ++ loop b
    | FnBody.dec x n _ _ b       => "dec" ++ (if n != 1 then Format.sbracket (format n) else "") ++ " " ++ format x ++ ";" ++ Format.line ++ loop b
    | FnBody.del x b             => "del " ++ format x ++ ";" ++ Format.line ++ loop b
    | FnBody.mdata d b           => "mdata " ++ format d ++ ";" ++ Format.line ++ loop b
    | FnBody.case _ x xType cs   => "case " ++ format x ++ " : " ++ format xType ++ " of" ++ cs.foldl (fun r c => r ++ Format.line ++ formatAlt loop indent c) Format.nil
    | FnBody.jmp j ys            => "jmp " ++ format j ++ formatArray ys
    | FnBody.ret x               => "ret " ++ format x
    | FnBody.unreachable         => "⊥"
  loop fnBody

instance : ToFormat FnBody := ⟨formatFnBody⟩
instance : ToString FnBody := ⟨fun b => (format b).pretty⟩

def formatDecl (decl : Decl) (indent : Nat := 2) : Format :=
  match decl with
  | Decl.fdecl f xs ty b _  => "def " ++ format f ++ formatParams xs ++ format " : " ++ format ty ++ " :=" ++ Format.nest indent (Format.line ++ formatFnBody b indent)
  | Decl.extern f xs ty _   => "extern " ++ format f ++ formatParams xs ++ format " : " ++ format ty

instance : ToFormat Decl := ⟨formatDecl⟩

@[export lean_ir_decl_to_string]
def declToString (d : Decl) : String :=
  (format d).pretty

instance : ToString Decl := ⟨declToString⟩

end Lean.IR
