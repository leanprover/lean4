/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name_mangling
import init.lean.ir.type_check

namespace lean
namespace ir
namespace cpp
def file_header := "#include <lean_obj.h>"

structure extract_env :=
(external_names : fnid → option string)
(ctx            : context)

@[reducible] def extract_m := reader_t extract_env (except_t format (state_t string id))

def emit {α} [has_to_string α] (a : α) : extract_m unit :=
modify (++ (to_string a))

def emit_line : extract_m unit :=
emit "\n"

def emit_var (x : var) : extract_m unit :=
emit $ name.mangle x "_x"

def emit_blockid (b : blockid) : extract_m unit :=
emit $ name.mangle b "_label"

def emit_fnid (fid : fnid) : extract_m unit :=
do env ← read,
   match env.external_names fid with
   | some s := emit s
   | none   := emit (name.mangle fid)

def to_cpp_type : type → string
| type.bool   := "unsigned char"  | type.byte   := "unsigned char"
| type.uint16 := "unsigned short" | type.uint32 := "unsigned"      | type.uint64 := "unsigned long long"  | type.usize  := "size_t"
| type.int16  := "short"          | type.int32  := "int"           | type.int64  := "long long"
| type.float  := "float"          | type.double := "double"
| type.object := "lean_obj*"

def emit_type (ty : type) : extract_m unit :=
emit (to_cpp_type ty)

def emit_sep_aux {α} (f : α → extract_m unit) (sep : string) : list α → extract_m unit
| []      := return ()
| [a]     := f a
| (a::as) := f a >> emit sep >> emit " " >> emit_sep_aux as

def emit_sep {α} (l : list α) (f : α → extract_m unit) (sep := ",") : extract_m unit :=
emit_sep_aux f sep l

def emit_return : list result → extract_m unit
| []  := emit "void"
| [r] := emit_type r.ty
| rs  := emit "std::tuple<" >> emit_sep rs (λ r, emit_type r.ty) >> emit ">"

def emit_arg_list (args : list arg) : extract_m unit :=
emit_sep args $ λ a, emit_type a.ty >> emit " : " >> emit_var a.n

/-- Emit end-of-statement -/
def emit_eos : extract_m unit :=
emit ";" >> emit_line

def emit_tag (x : var) : extract_m unit :=
emit "lean::cnstr_tag(" >> emit_var x >> emit ")"

def emit_return_vars : list var → extract_m unit
| []  := return ()
| [x] := emit_var x
| xs  := emit "std::make_tuple(" >> emit_sep xs emit_var >> emit ")"

def emit_cases : list blockid → nat → extract_m unit
| []      n := throw "ill-formed case terminator"
| [b]     n := emit "default: goto " >> emit_blockid b >> emit_eos
| (b::bs) n := emit "case " >> emit n >> emit ": goto " >> emit_blockid b >> emit_eos >> emit_cases bs (n+1)

def emit_case : var → list blockid → extract_m unit
| x [b]     := emit "goto " >> emit_blockid b >> emit_eos
| x [b₁,b₂] :=
  do env ← read,
     if env.ctx.find x = some type.bool
     then emit "if (" >> emit_var x >> emit ") goto " >> emit_blockid b₂ >> emit "; else goto " >> emit_blockid b₁ >> emit_eos
     else emit "if (" >> emit_tag x >> emit " == 0) goto " >> emit_blockid b₁ >> emit "; else goto " >> emit_blockid b₂ >> emit_eos
| x bs      := emit "switch (" >> emit_tag x >> emit ") {" >> emit_cases bs 0 >> emit "}" >> emit_line

def emit_terminator (term : terminator) : extract_m unit :=
term.decorate_error $
match term with
| (terminator.jmp b)     := emit "goto " >> emit_blockid b >> emit_eos
| (terminator.ret xs)    := emit "return " >> emit_return_vars xs >> emit_eos
| (terminator.case x bs) := emit_case x bs

def emit_call_lhs : list var → extract_m unit
| []  := return ()
| [x] := emit_var x >> emit " := "
| xs  := emit "std::tie(" >> emit_sep xs emit_var >> emit ") := "

def emit_type_size (ty : type) : extract_m unit :=
emit "sizeof(" >> emit_type ty >> emit ")"

def emit_sizet : list (nat × type) → extract_m unit
| []             := emit 0
| ((n, ty)::ss)  := emit n >> emit "*" >> emit_type_size ty >> emit " + " >> emit_sizet ss

/-- Emit `op(x)` -/
def emit_op_x (op : string) (x : var) : extract_m unit :=
emit op >> emit "(" >> emit_var x >> emit ")"

/-- Emit `x := y op z` -/
def emit_infix (x y z : var) (op : string) : extract_m unit :=
emit_var x >> emit " := " >> emit_var y >> emit op >> emit_var z

/- Emit `x := big_op(y, z)` -/
def emit_big_binop (x y z : var) (big_op : string) : extract_m unit :=
emit_var x >> emit " := " >> emit big_op >> emit "(" >> emit_var y >> emit ", " >> emit_var z >> emit ")"

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


/-- Emit `x := op(y)` -/
def emit_x_op_y (x : var) (op : string) (y : var) : extract_m unit :=
emit_var x >> emit " := " >> emit op >> emit "(" >> emit_var y >> emit ")"

def emit_unop (x : var) (t : type) (op : unop) (y : var) : extract_m unit :=
match op with
| unop.not          :=
  (match t with
   | type.bool      := emit_x_op_y x "!" y
   | _              := emit_x_op_y x "~" y)
| unop.neg          :=
  (match t with
   | type.object    := emit_x_op_y x "lean::big_neg" y
   | _              := emit_x_op_y x "-" y)
| unop.scalar       := emit_x_op_y x "lean::is_scalar" y
| unop.shared       := emit_x_op_y x "lean::is_shared" y
| unop.copy_array   := emit_x_op_y x "lean::copy_array" y
| unop.copy_sarray  := emit_x_op_y x "lean::copy_sarray" y
| unop.box          := emit_x_op_y x "lean::box" y
| unop.unbox        := emit_x_op_y x "lean::unbox" y
| unop.cast         := emit_var x >> emit " := static_cast<" >> emit_type t >> emit ">(" >> emit_var y >> emit ")"

def emit_lit (x : var) (t : type) (l : literal) : extract_m unit :=
return () -- TODO

def emit_instr (ins : instr) : extract_m unit :=
ins.decorate_error $
(match ins with
 | (instr.lit x t l)        := emit_lit x t l
 | (instr.unop x t op y)    := emit_unop x t op y
 | (instr.binop x t op y z) := emit_binop x t op y z
 | (instr.call xs f ys)     := emit_call_lhs xs >> emit_fnid f >> emit "(" >> emit_sep ys emit_var >> emit ")"
 | (instr.cnstr o t n sz)   := emit_var o >> emit " := lean::alloc_cnstr(" >> emit t >> emit ", " >> emit n >> emit ", " >> emit_sizet sz >> emit ")"
 | (instr.set o i x)        := emit "lean::set_cnstr_obj(" >> emit_var o >> emit ", " >> emit i >> emit ", " >> emit_var x >> emit ")"
 | (instr.get x o i)        := emit_var x >> emit " := lean::cnstr_obj(" >> emit_var o >> emit ", " >> emit i >> emit ")"
 | (instr.sset o d x)       := emit "lean::set_cnstr_scalar(" >> emit_var o >> emit ", " >> emit_sizet d >> emit ", " >> emit_var x >> emit ")"
 | (instr.sget x t o d)     := emit_var x >> emit " := lean::cnstr_scalar<" >> emit_type t >> emit ">(" >> emit_var o >> emit ", " >> emit_sizet d >> emit ")"
 | (instr.closure x f ys)   := return () -- TODO
 | (instr.apply x ys)       := return () -- TODO
 | (instr.array a sz c)     := emit_var a >> emit " := lean::alloc_array(" >> emit_var sz >> emit ", " >> emit_var c >> emit ")"
 | (instr.write a i v)      := emit "lean::set_array_obj(" >> emit_var a >> emit ", " >> emit_var i >> emit ", " >> emit_var v >> emit ")"
 | (instr.read x a i)       := emit_var x >> emit " := lean::array_obj(" >> emit_var a >> emit ", " >> emit_var i >> emit ")"
 | (instr.sarray a t sz c)  := emit_var a >> emit " := lean::alloc_sarray(" >> emit_type_size t >> emit ", " >> emit_var sz >> emit ", " >> emit_var c >> emit ")"
 | (instr.swrite a i v)     := emit "lean::set_sarray_data(" >> emit_var a >> emit ", " >> emit_var i >> emit ", " >> emit_var v >> emit ")"
 | (instr.sread x t a i)    := emit_var x >> emit " := lean::sarray_data<" >> emit_type t >> emit ">(" >> emit_var a >> emit ", " >> emit_var i >> emit ")"
 | (instr.inc x)            := emit_op_x "lean::inc_ref" x
 | (instr.decs x)           := emit_op_x "lean::dec_shared_ref" x
 | (instr.free x)           := emit_op_x "free" x
 | (instr.dealloc x)        := emit_op_x "lean::dealloc" x
 | (instr.dec x)            := emit_op_x "lean::dec_ref" x)
>> emit_eos

def emit_block (b : block) : extract_m unit :=
   unless b.phis.empty (throw "failed to extract C++ code, definition contains phi nodes")
>> emit_blockid b.id >> emit ":" >> emit_line
>> b.instrs.mfor emit_instr
>> emit_terminator b.term

def emit_header (h : header) : extract_m unit :=
emit_return h.return >> emit " " >> emit_fnid h.n >> emit "(" >> emit_arg_list h.args >> emit ")"

def decl_local (x : var) (ty : type) : extract_m unit :=
emit_var x >> emit_type ty >> emit_eos

def decl_locals (args : list arg) : extract_m unit :=
do env ← read,
   env.ctx.mfor $ λ x ty,
     unless (args.any (λ a, a.n = x)) (decl_local x ty)

def emit_decl_core (d : decl) : extract_m unit :=
d.decorate_error $
match d with
| (decl.defn h bs)  := emit_header h >> emit " {" >> emit_line >> decl_locals h.args >> bs.mfor emit_block >> emit "}" >> emit_line
| (decl.external h) := emit_header h >> emit ";" >> emit_line

def emit_decl (env : environment) (external_names : fnid → option string) (d : decl) : except_t format (state_t string id) unit :=
do ctx ← monad_lift $ infer_types d env,
   (emit_decl_core d).run { external_names := external_names, ctx := ctx }

def emit_decls (env : environment) (cpp_names : fnid → option string) (ds : list decl) : except format string :=
let out := file_header in
run (ds.mfor (emit_decl env cpp_names) >> get) out

end cpp
end ir
end lean
