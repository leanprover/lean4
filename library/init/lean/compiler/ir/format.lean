/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic init.lean.format

namespace Lean
namespace IR

private def formatArg : Arg → Format
| (Arg.var id)   := format id
| Arg.irrelevant := "◾"

instance argHasFormat : HasFormat Arg := ⟨formatArg⟩

private def formatArray {α : Type} [HasFormat α] (args : Array α) : Format :=
args.foldl (λ r a, r ++ " " ++ format a) Format.nil

private def formatLitVal : LitVal → Format
| (LitVal.num v) := format v
| (LitVal.str v) := format (repr v)

instance litValHasFormat : HasFormat LitVal := ⟨formatLitVal⟩

private def formatCtorInfo : CtorInfo → Format
| { name := name, cidx := cidx, usize := usize, ssize := ssize, .. } :=
  let r := format "ctor_" ++ format cidx;
  let r := if usize > 0 || ssize > 0 then r ++ "." ++ format usize ++ "." ++ format ssize else r;
  let r := if name != Name.anonymous then r ++ "[" ++ format name ++ "]" else r;
  r

instance ctorInfoHasFormat : HasFormat CtorInfo := ⟨formatCtorInfo⟩

private def formatExpr : Expr → Format
| (Expr.ctor i ys)       := format i ++ formatArray ys
| (Expr.reset n x)       := "reset[" ++ format n ++ "] " ++ format x
| (Expr.reuse x i u ys)  := "reuse" ++ (if u then "!" else "") ++ " " ++ format x ++ " in " ++ format i ++ formatArray ys
| (Expr.proj i x)        := "proj[" ++ format i ++ "] " ++ format x
| (Expr.uproj i x)       := "uproj[" ++ format i ++ "] " ++ format x
| (Expr.sproj n o x)     := "sproj[" ++ format n ++ ", " ++ format o ++ "] " ++ format x
| (Expr.fap c ys)        := format c ++ formatArray ys
| (Expr.pap c ys)        := "pap " ++ format c ++ formatArray ys
| (Expr.ap x ys)         := "app " ++ format x ++ formatArray ys
| (Expr.box _ x)         := "box " ++ format x
| (Expr.unbox x)         := "unbox " ++ format x
| (Expr.lit v)           := format v
| (Expr.isShared x)      := "isShared " ++ format x
| (Expr.isTaggedPtr x)   := "isTaggedPtr " ++ format x

instance exprHasFormat   : HasFormat Expr := ⟨formatExpr⟩
instance exprHasToString : HasToString Expr := ⟨λ e, Format.pretty (format e)⟩

private def formatIRType : IRType → Format
| IRType.float      := "float"
| IRType.uint8      := "u8"
| IRType.uint16     := "u16"
| IRType.uint32     := "u32"
| IRType.uint64     := "u64"
| IRType.usize      := "usize"
| IRType.irrelevant := "◾"
| IRType.object     := "obj"
| IRType.tobject    := "tobj"

instance typeHasFormat : HasFormat IRType := ⟨formatIRType⟩

private def formatParam : Param → Format
| { x := name, borrow := b, ty := ty } := "(" ++ format name ++ " : " ++ (if b then "@& " else "") ++ format ty ++ ")"

instance paramHasFormat : HasFormat Param := ⟨formatParam⟩

def formatAlt (fmt : FnBody → Format) (indent : Nat) : Alt → Format
| (Alt.ctor i b)  := format i.name ++ " →" ++ Format.nest indent (Format.line ++ fmt b)
| (Alt.default b) := "default →" ++ Format.nest indent (Format.line ++ fmt b)

def formatParams (ps : Array Param) : Format :=
formatArray ps

partial def formatFnBody (indent : Nat := 2) : FnBody → Format
| (FnBody.vdecl x ty e b)    := "let " ++ format x ++ " : " ++ format ty ++ " := " ++ format e ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.jdecl j xs v b)    := format j ++ formatParams xs ++ " :=" ++ Format.nest indent (Format.line ++ formatFnBody v) ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.set x i y b)       := "set " ++ format x ++ "[" ++ format i ++ "] := " ++ format y ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.uset x i y b)      := "uset " ++ format x ++ "[" ++ format i ++ "] := " ++ format y ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.sset x i o y ty b) := "sset " ++ format x ++ "[" ++ format i ++ ", " ++ format o ++ "] : " ++ format ty ++ " := " ++ format y ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.setTag x cidx b)   := "setTag " ++ format x ++ " := " ++ format cidx ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.inc x n c b)       := "inc" ++ (if n != 1 then Format.sbracket (format n) else "") ++ " " ++ format x ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.dec x n c b)       := "dec" ++ (if n != 1 then Format.sbracket (format n) else "") ++ " " ++ format x ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.del x b)           := "del " ++ format x ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.mdata d b)         := "mdata " ++ format d ++ ";" ++ Format.line ++ formatFnBody b
| (FnBody.case tid x cs)     := "case " ++ format x ++ " of" ++ cs.foldl (λ r c, r ++ Format.line ++ formatAlt formatFnBody indent c) Format.nil
| (FnBody.jmp j ys)          := "jmp " ++ format j ++ formatArray ys
| (FnBody.ret x)             := "ret " ++ format x
| FnBody.unreachable         := "⊥"

instance fnBodyHasFormat : HasFormat FnBody := ⟨formatFnBody⟩
instance fnBodyHasToString : HasToString FnBody := ⟨λ b, (format b).pretty⟩

def formatDecl (indent : Nat := 2) : Decl → Format
| (Decl.fdecl f xs ty b)  := "def " ++ format f ++ formatParams xs ++ format " : " ++ format ty ++ " :=" ++ Format.nest indent (Format.line ++ formatFnBody indent b)
| (Decl.extern f xs ty _) := "extern " ++ format f ++ formatParams xs ++ format " : " ++ format ty

instance declHasFormat : HasFormat Decl := ⟨formatDecl⟩

@[export lean.ir.decl_to_string_core]
def declToString (d : Decl) : String :=
(format d).pretty

instance declHasToString : HasToString Decl := ⟨declToString⟩

end IR
end Lean
