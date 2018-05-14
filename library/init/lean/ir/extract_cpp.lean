/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name_mangling init.lean.config
import init.lean.ir.type_check

namespace lean
namespace ir
namespace cpp
def file_header :=
"#include <lean_obj.h>
typedef lean::lean_obj obj;"

structure extract_env :=
(external_names : fnid → option string)
(ctx            : context)
(env            : environment)

@[reducible] def extract_m := reader_t extract_env (except_t format (state_t string id))

def emit {α} [has_to_string α] (a : α) : extract_m unit :=
modify (++ (to_string a))

def emit_line : extract_m unit :=
emit "\n"

def paren {α} (a : extract_m α) : extract_m α :=
emit "(" >> a <* emit ")"

def comma (a b : extract_m unit) : extract_m unit :=
a >> emit ", " >> b

local infix `<+>`:65 := comma

def emit_var (x : var) : extract_m unit :=
emit $ name.mangle x "_x"

def emit_blockid (b : blockid) : extract_m unit :=
emit $ name.mangle b "_lbl"

def fid2cpp (fid : fnid) : extract_m string :=
do env ← read,
   match env.external_names fid with
   | some s := return s
   | none   := return (name.mangle fid)

def emit_fnid (fid : fnid) : extract_m unit :=
fid2cpp fid >>= emit

def type2cpp : type → string
| type.bool   := "unsigned char"  | type.byte   := "unsigned char"
| type.uint16 := "unsigned short" | type.uint32 := "unsigned"      | type.uint64 := "unsigned long long"  | type.usize  := "size_t"
| type.int16  := "short"          | type.int32  := "int"           | type.int64  := "long long"
| type.float  := "float"          | type.double := "double"
| type.object := "obj*"

def emit_type (ty : type) : extract_m unit :=
emit (type2cpp ty)

def emit_sep_aux {α} (f : α → extract_m unit) (sep : string) : list α → extract_m unit
| []      := return ()
| [a]     := f a
| (a::as) := f a >> emit sep >> emit " " >> emit_sep_aux as

def emit_sep {α} (l : list α) (f : α → extract_m unit) (sep := ",") : extract_m unit :=
emit_sep_aux f sep l

def emit_var_list (xs : list var) : extract_m unit :=
emit_sep xs emit_var

def emit_template_params (ts : list type) : extract_m unit :=
emit "<" >> emit_sep ts emit_type >> emit ">"

def emit_template_param (t : type) : extract_m unit :=
emit_template_params [t]

def emit_return : list result → extract_m unit
| []  := emit "void"
| [r] := emit_type r.ty
| rs  := emit "std::tuple" >> emit_template_params (rs.map result.ty)

def emit_arg_list (args : list arg) : extract_m unit :=
emit_sep args $ λ a, emit_type a.ty >> emit " " >> emit_var a.n

/-- Emit end-of-statement -/
def emit_eos : extract_m unit :=
emit ";" >> emit_line

def emit_tag (x : var) : extract_m unit :=
emit "lean::cnstr_tag" >> paren(emit_var x)

def emit_return_vars : list var → extract_m unit
| []  := return ()
| [x] := emit_var x
| xs  := emit "std::make_tuple" >> paren(emit_var_list xs)

def emit_cases : list blockid → nat → extract_m unit
| []      n := throw "ill-formed case terminator"
| [b]     n := emit "default: goto " >> emit_blockid b >> emit_eos
| (b::bs) n := emit "case " >> emit n >> emit ": goto " >> emit_blockid b >> emit_eos >> emit_cases bs (n+1)

def emit_case : var → list blockid → extract_m unit
| x [b]     := emit "goto " >> emit_blockid b >> emit_eos
| x [b₁,b₂] := do
     env ← read,
     (match env.ctx.find x with
      | some type.bool   := emit "if (" >> emit_var x >> emit ") goto " >> emit_blockid b₂ >> emit "; else goto " >> emit_blockid b₁
      | some type.uint32 := emit "if (" >> emit_var x >> emit " == 0) goto " >> emit_blockid b₁ >> emit "; else goto " >> emit_blockid b₂
      | _                := emit "if (" >> emit_tag x >> emit " == 0) goto " >> emit_blockid b₁ >> emit "; else goto " >> emit_blockid b₂),
     emit_eos
| x bs      :=  do
    env ← read,
    emit "switch ",
    paren (if env.ctx.find x = some type.uint32 then emit_var x else emit_tag x),
    emit " {" >> emit_line >> emit_cases bs 0 >> emit "}" >> emit_line

def emit_terminator (term : terminator) : extract_m unit :=
term.decorate_error $
match term with
| (terminator.jmp b)     := emit "goto " >> emit_blockid b >> emit_eos
| (terminator.ret xs)    := emit "return " >> emit_return_vars xs >> emit_eos
| (terminator.case x bs) := emit_case x bs

def emit_call_lhs : list var → extract_m unit
| []  := return ()
| [x] := emit_var x >> emit " = "
| xs  := emit "std::tie" >> paren(emit_var_list xs) >> emit " = "

def emit_type_size (ty : type) : extract_m unit :=
emit "sizeof" >> paren(emit_type ty)

/-- Emit `op(x)` -/
def emit_op_x (op : string) (x : var) : extract_m unit :=
emit op >> paren (emit_var x)

/-- Emit `x := y op z` -/
def emit_infix (x y z : var) (op : string) : extract_m unit :=
emit_var x >> emit " = " >> emit_var y >> emit " " >> emit op >> emit " " >> emit_var z

/- Emit `x := big_op(y, z)` -/
def emit_big_binop (x y z : var) (big_op : string) : extract_m unit :=
emit_var x >> emit " = " >> emit big_op >> paren (emit_var y <+> emit_var z)

def emit_arith (t : type) (x y z : var) (op : string) (big_op : string) : extract_m unit :=
match t with
| type.object := emit_big_binop x y z big_op
| _           := emit_infix x y z op

def emit_logical_arith (t : type) (x y z : var) (bool_op : string) (op : string) (big_op : option string) : extract_m unit :=
match t with
| type.bool   := emit_infix x y z bool_op
| type.object :=
  (match big_op with
   | some big_op := emit_big_binop x y z big_op
   | none        := throw "ill-formed binary operator")
| _           := emit_infix x y z op

def emit_binop (x : var) (t : type) (op : binop) (y z : var) : extract_m unit :=
match op with
| binop.add  := emit_arith t x y z "+" "lean::big_add"
| binop.sub  := emit_arith t x y z "-" "lean::big_sub"
| binop.mul  := emit_arith t x y z "*" "lean::big_mul"
| binop.div  := emit_arith t x y z "/" "lean::big_div"
| binop.mod  := emit_arith t x y z "%" "lean::big_mod"
| binop.shl  := emit_infix x y z "<<"
| binop.shr  := emit_infix x y z ">>"
| binop.and  := emit_logical_arith t x y z "&&" "&" (some "lean::bigand")
| binop.or   := emit_logical_arith t x y z "||" "|" (some "lean::bigor")
| binop.xor  := emit_logical_arith t x y z "!=" "^" none
| binop.le   := emit_arith t x y z "<=" "lean::big_le"
| binop.ge   := emit_arith t x y z ">=" "lean::big_ge"
| binop.lt   := emit_arith t x y z "<" "lean::big_lt"
| binop.gt   := emit_arith t x y z ">" "lean::big_gt"
| binop.eq   := emit_arith t x y z "==" "lean::big_eq"
| binop.ne   := emit_arith t x y z "!=" "lean::big_nq"
| binop.array_read :=
  (match t with
   | type.object := emit_var x >> emit " = lean::array_obj" >> paren (emit_var y <+> emit_var z)
   | _           := emit_var x >> emit " = lean::sarray_data" >> emit_template_param t >> paren (emit_var y <+> emit_var z))

/-- Emit `x := op(y)` -/
def emit_x_op_y (x : var) (op : string) (y : var) : extract_m unit :=
emit_var x >> emit " = " >> emit op >> paren(emit_var y)

def unop2cpp (t : type) : unop → string
| unop.not          := if t = type.bool then "!" else "~"
| unop.neg          := if t = type.object then "lean::big_neg" else "-"
| unop.is_scalar    := "lean::is_scalar"
| unop.is_shared    := "lean::is_shared"
| unop.is_null      := "lean::is_null"
| unop.box          := "lean::box"
| unop.unbox        := "lean::unbox"
| unop.cast         := "static_cast<" ++ type2cpp t ++ ">"
| unop.array_copy   := "lean::array_copy"
| unop.sarray_copy  := "lean::sarray_copy"
| unop.array_size   := "lean::array_size"
| unop.sarray_size  := "lean::sarray_size"
| unop.string_len   := "lean::string_len"

def emit_unop (x : var) (t : type) (op : unop) (y : var) : extract_m unit :=
emit_var x >> emit " = " >> emit (unop2cpp t op) >> paren(emit_var y)

def emit_num_suffix : type → extract_m unit
| type.uint32 := emit "u"
| type.uint64 := emit "ull"
| type.int64  := emit "ll"
| _           := return ()

def emit_lit (x : var) (t : type) (l : literal) : extract_m unit :=
match l with
| literal.bool tt := emit_var x >> emit " = true"
| literal.bool ff := emit_var x >> emit " = false"
| literal.str s   := emit_var x >> emit " = lean::mk_string" >> paren(emit (repr s))
| literal.float v := emit_var x >> emit " = " >> emit v
| literal.num v   := emit_var x >> emit " = " >> emit v >> emit_num_suffix t

def unins2cpp : unins → string
| unins.inc            := "lean::inc_ref"
| unins.decs           := "lean::dec_shared_ref"
| unins.dec            := "lean::dec_ref"
| unins.free           := "free"
| unins.dealloc        := "lean::dealloc"
| unins.array_pop      := "lean::array_pop"
| unins.sarray_pop     := "lean::sarray_pop"

def emit_unary (op : unins) (x : var) : extract_m unit :=
emit (unins2cpp op) >> paren(emit_var x)

def emit_apply (x : var) (ys : list var) : extract_m unit :=
match ys with
| (f::as) :=
  let n := as.length in
  if n > closure_max_args
  then emit "{ obj * as[" >> emit n >> emit "] = {" >> emit_var_list as >> emit "}; "
       >> emit_var x >> emit " = apply_m" >> paren(emit_var f <+> emit n <+> emit "as") >> emit "; }"
  else emit_var x >> emit " = apply_" >> emit n >> paren(emit_var_list ys)
| _       := throw "ill-formed apply"

def emit_closure (x : var) (f : fnid) (ys : list var) : extract_m unit :=
do env ← read,
   match env.env f with
   | some d := do
     emit_var x, emit " = lean::alloc_closure(",
     let arity := d.header.args.length,
     fname ← fid2cpp f,
     let fname := if arity > closure_max_args then "uncurry" ++ fname else fname,
     emit "reinterpret_cast<lean::lean_cfun>(" >> emit fname >> emit ")" <+> emit arity <+> emit ys.length,
     emit ")",
     ys.mfoldl (λ i y, emit ";\nlean::set_closure_arg" >> paren (emit_var x <+> emit i <+> emit_var y) >> return (i+1)) 0,
     return ()
   | none   := throw "invalid closure"

def emit_instr (ins : instr) : extract_m unit :=
ins.decorate_error $
(match ins with
 | (instr.lit x t l)         := emit_lit x t l
 | (instr.unop x t op y)     := emit_unop x t op y
 | (instr.binop x t op y z)  := emit_binop x t op y z
 | (instr.call xs f ys)      := emit_call_lhs xs >> emit_fnid f >> paren(emit_var_list ys)
 | (instr.cnstr o t n sz)    := emit_var o >> emit " = lean::alloc_cnstr" >> paren(emit t <+> emit n <+> emit sz)
 | (instr.set o i x)         := emit "lean::set_cnstr_obj" >> paren (emit_var o <+> emit i <+> emit_var x)
 | (instr.get x o i)         := emit_var x >> emit " = lean::cnstr_obj" >> paren(emit_var o <+> emit i)
 | (instr.sset o d x)        := emit "lean::set_cnstr_scalar" >> paren(emit_var o <+> emit d <+> emit_var x)
 | (instr.sget x t o d)      := emit_var x >> emit " = lean::cnstr_scalar" >> emit_template_param t >> paren(emit_var o <+> emit d)
 | (instr.closure x f ys)    := emit_closure x f ys
 | (instr.apply x ys)        := emit_apply x ys
 | (instr.array a sz c)      := emit_var a >> emit " = lean::alloc_array" >> paren(emit_var sz <+> emit_var c)
 | (instr.sarray a t sz c)   := emit_var a >> emit " = lean::alloc_sarray" >> paren(emit_type_size t <+> emit_var sz <+> emit_var c)
 | (instr.array_write a i v) :=
   do env ← read,
      if env.ctx.find v = some type.object
      then emit "lean::set_array_obj" >> paren(emit_var a <+> emit_var i <+> emit_var v)
      else emit "lean::set_sarray_data" >> paren(emit_var a <+> emit_var i <+> emit_var v)
 | (instr.array_push a v) :=
   do env ← read,
      if env.ctx.find v = some type.object
      then emit "lean::array_push" >> paren(emit_var a <+> emit_var v)
      else emit "lean::sarray_push" >> paren(emit_var a <+> emit_var v)
 | (instr.unary op x)        := emit_unary op x)
>> emit_eos

def emit_block (b : block) : extract_m unit :=
   unless b.phis.empty (throw "failed to extract C++ code, definition contains phi nodes")
>> emit_blockid b.id >> emit ":" >> emit_line
>> b.instrs.mfor emit_instr
>> emit_terminator b.term

def emit_header (h : header) : extract_m unit :=
emit_return h.return >> emit " " >> emit_fnid h.n >> paren(emit_arg_list h.args)

def decl_local (x : var) (ty : type) : extract_m unit :=
emit_type ty >> emit " " >> emit_var x >> emit_eos

def decl_locals (args : list arg) : extract_m unit :=
do env ← read,
   env.ctx.mfor $ λ x ty,
     unless (args.any (λ a, a.n = x)) (decl_local x ty)

def need_uncurry (d : decl) : bool :=
d.header.args.length > lean.closure_max_args &&
d.header.return.length = 1 &&
d.header.return.all (λ a, a.ty = type.object) &&
d.header.args.all (λ a, a.ty = type.object)

def emit_uncurry_header (d : decl) : extract_m unit :=
emit "obj* uncurry" >> emit_fnid d.header.n >> emit "(obj** as)"

def emit_uncurry (d : decl) : extract_m unit :=
let nargs := d.header.args.length in
   emit_uncurry_header d >> emit " {\n"
>> emit "return " >> emit_fnid d.header.n >> paren (emit "as[0]" >> (nargs-1).mrepeat (λ i, emit ", " >> emit "as[" >> emit (i+1) >> emit "]")) >> emit_eos
>> emit "}\n"

def emit_def_core (d : decl) : extract_m unit :=
d.decorate_error $
match d with
| (decl.defn h bs)  :=
  emit_header h >> emit " {" >> emit_line >> decl_locals h.args >> bs.mfor emit_block >> emit "}" >> emit_line >>
  when (need_uncurry d) (emit_uncurry d)
| _ := return ()

def emit_def (env : environment) (external_names : fnid → option string) (d : decl) : except_t format (state_t string id) unit :=
do ctx ← monad_lift $ infer_types d env,
   (emit_def_core d).run { external_names := external_names, ctx := ctx, env := env }

def collect_used (d : list decl) : fnid_set :=
d.foldl (λ s d, match d with
  | (decl.defn _ bs) := bs.foldl (λ s b, b.instrs.foldl (λ s ins, match ins with
    | instr.call _ fid _    := s.insert fid
    | instr.closure _ fid _ := s.insert fid
    | _                      := s) s) s
  | _                := s) mk_fnid_set

def emit_used_headers (env : environment) (external_names : fnid → option string) (d : list decl) : except_t format (state_t string id) unit :=
let used := collect_used d in
(used.mfor (λ fid, match env fid with
   | some d := emit_header d.header >> emit ";\n" >> when (need_uncurry d) (emit_uncurry_header d >> emit ";\n")
   | _      := return ())).run { external_names := external_names, ctx := mk_context, env := env }

end cpp

def extract_cpp (env : environment) (cpp_names : fnid → option string) (ds : list decl) : except format string :=
let out := cpp.file_header ++ "\n" in
run (cpp.emit_used_headers env cpp_names ds >> ds.mfor (cpp.emit_def env cpp_names) >> get) out

end ir
end lean
