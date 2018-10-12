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
/--
C++ code extraction configuration object.

- `unit_name`: compilation unit name. The name is used to generate initialization/finalization procedures.
- `unit_deps`: list of compilation units the given unit depends on. This information is also used to generate
   initialization and finalization procedures.
- `runtime_dir` : location of the Lean C++ runtime include files.
- `env`: mapping from declaration name to declaration.
- `external_names`: a mapping s.t. entry `(fid, n)` is in the mapping when we need to use name `n` for
   declaration `fid` when emitting C++ code.
- `main_proc`: name of the main procedure. Initialization and finalization code is inserted for it.
-/
structure extract_cpp_config :=
(unit_name : string := "main")
(unit_deps : list string := [])
(runtime_dir : string := "runtime")
(env : environment := λ _, none)
(external_names : fnid → option string := λ _, none)
(main_proc : option fnid := none)

namespace cpp
def initialize_prefix := "_lean_initialize_"
def finalize_prefix   := "_lean_finalize_"

def file_header (runtime_dir : string) :=
   "#include <" ++ runtime_dir ++ "/object.h>\n"
++ "#include <" ++ runtime_dir ++ "/apply.h>\n"
++ "typedef lean::object obj;"

structure extract_env :=
(cfg : extract_cpp_config)
(ctx : context := mk_context)

@[derive monad monad_except monad_state monad_reader monad_run]
def extract_m := reader_t extract_env (except_t format (state_t string id))

def emit {α} [has_to_string α] (a : α) : extract_m unit :=
modify (++ (to_string a))

def emit_line : extract_m unit :=
emit "\n"

@[inline] def paren {α} (a : extract_m α) : extract_m α :=
emit "(" *> a <* emit ")"

@[inline] def comma (a b : extract_m unit) : extract_m unit :=
a *> emit ", " *> b

local infix ` <+> `:65 := comma

def emit_var (x : var) : extract_m unit :=
emit $ name.mangle x "_x"

def emit_blockid (b : blockid) : extract_m unit :=
emit $ name.mangle b "_lbl"

def fid2cpp (fid : fnid) : extract_m string :=
do env ← read,
   match env.cfg.external_names fid with
   | some s := pure s
   | none   := pure (name.mangle fid)

def emit_fnid (fid : fnid) : extract_m unit :=
fid2cpp fid >>= emit

def is_const (fid : fnid) : extract_m bool :=
do env ← read,
   match env.cfg.env fid with
   | some d := pure d.header.is_const
   | none   := pure ff

def global2cpp (fid : fnid) : extract_m string :=
do s ← fid2cpp fid, pure $ "_g" ++ s

def emit_global (fid : fnid) : extract_m unit :=
global2cpp fid >>= emit

def type2cpp : type → string
| type.bool   := "unsigned char"  | type.byte   := "unsigned char"
| type.uint16 := "unsigned short" | type.uint32 := "unsigned"      | type.uint64 := "unsigned long long"  | type.usize  := "size_t"
| type.int16  := "short"          | type.int32  := "int"           | type.int64  := "long long"
| type.float  := "float"          | type.double := "double"
| type.object := "obj*"

def emit_type (ty : type) : extract_m unit :=
emit (type2cpp ty)

def emit_sep_aux {α} (f : α → extract_m unit) (sep : string) : list α → extract_m unit
| []      := pure ()
| [a]     := f a
| (a::as) := f a *> emit sep *> emit " " *> emit_sep_aux as

def emit_sep {α} (l : list α) (f : α → extract_m unit) (sep := ",") : extract_m unit :=
emit_sep_aux f sep l

def emit_var_list (xs : list var) : extract_m unit :=
emit_sep xs emit_var

def emit_template_params (ts : list type) : extract_m unit :=
emit "<" *> emit_sep ts emit_type *> emit ">"

def emit_template_param (t : type) : extract_m unit :=
emit_template_params [t]

def emit_return : list result → extract_m unit
| []  := emit "void"
| [r] := emit_type r.ty
| rs  := emit "std::tuple" *> emit_template_params (rs.map result.ty)

def emit_arg_list (args : list arg) : extract_m unit :=
emit_sep args $ λ a, emit_type a.ty *> emit " " *> emit_var a.n

/-- Emit end-of-statement -/
def emit_eos : extract_m unit :=
emit ";" *> emit_line

def emit_return_vars : list var → extract_m unit
| []  := pure ()
| [x] := emit_var x
| xs  := emit "std::make_tuple" *> paren(emit_var_list xs)

def emit_cases : list blockid → nat → extract_m unit
| []      n := throw "ill-formed case terminator"
| [b]     n := emit "default: goto " *> emit_blockid b *> emit_eos
| (b::bs) n := emit "case " *> emit n *> emit ": goto " *> emit_blockid b *> emit_eos *> emit_cases bs (n+1)

def emit_case : var → list blockid → extract_m unit
| x [b]     := emit "goto " *> emit_blockid b *> emit_eos
| x [b₁,b₂] := do
     env ← read,
     (match env.ctx.find x with
      | some type.bool   := emit "if (" *> emit_var x *> emit ") goto " *> emit_blockid b₂ *> emit "; else goto " *> emit_blockid b₁
      | some type.uint32 := emit "if (" *> emit_var x *> emit " == 0) goto " *> emit_blockid b₁ *> emit "; else goto " *> emit_blockid b₂
      | _                := throw "ill-formed case"),
     emit_eos
| x bs      :=  do
    env ← read,
    emit "switch ",
    paren (emit_var x),
    emit " {" *> emit_line *> emit_cases bs 0 *> emit "}" *> emit_line

def emit_terminator (term : terminator) : extract_m unit :=
term.decorate_error $
match term with
| (terminator.jmp b)     := emit "goto " *> emit_blockid b *> emit_eos
| (terminator.ret xs)    := emit "return " *> emit_return_vars xs *> emit_eos
| (terminator.case x bs) := emit_case x bs

def emit_call_lhs : list var → extract_m unit
| []  := pure ()
| [x] := emit_var x *> emit " = "
| xs  := emit "std::tie" *> paren(emit_var_list xs) *> emit " = "

def emit_type_size (ty : type) : extract_m unit :=
emit "sizeof" *> paren(emit_type ty)

/-- Emit `op(x)` -/
def emit_op_x (op : string) (x : var) : extract_m unit :=
emit op *> paren (emit_var x)

/-- Emit `x := y op z` -/
def emit_infix (x y z : var) (op : string) : extract_m unit :=
emit_var x *> emit " = " *> emit_var y *> emit " " *> emit op *> emit " " *> emit_var z

/- Emit `x := big_op(y, z)` -/
def emit_big_binop (x y z : var) (big_op : string) : extract_m unit :=
emit_var x *> emit " = " *> emit big_op *> paren (emit_var y <+> emit_var z)

def emit_arith (t : type) (x y z : var) (op : string) (big_op : string) : extract_m unit :=
match t with
| type.object := emit_big_binop x y z big_op
| _           := emit_infix x y z op

def emit_logical_arith (t : type) (x y z : var) (bool_op : string) (op : string) (big_op : string) : extract_m unit :=
match t with
| type.bool   := emit_infix x y z bool_op
| type.object := emit_big_binop x y z big_op
| _           := emit_infix x y z op

def emit_assign_binop (x : var) (t : type) (op : assign_binop) (y z : var) : extract_m unit :=
match op with
| assign_binop.add  := emit_arith t x y z "+" "lean::nat_add"
| assign_binop.sub  := emit_arith t x y z "-" "lean::nat_sub"
| assign_binop.mul  := emit_arith t x y z "*" "lean::nat_mul"
| assign_binop.div  := emit_arith t x y z "/" "lean::nat_div"
| assign_binop.mod  := emit_arith t x y z "%" "lean::nat_mod"
| assign_binop.iadd := emit_big_binop x y z "lean::int_add"
| assign_binop.isub := emit_big_binop x y z "lean::int_sub"
| assign_binop.imul := emit_big_binop x y z "lean::int_mul"
| assign_binop.idiv := emit_big_binop x y z "lean::int_div"
| assign_binop.imod := emit_big_binop x y z "lean::int_mod"
| assign_binop.shl  := emit_infix x y z "<<"
| assign_binop.shr  := emit_infix x y z ">>"
| assign_binop.and  := emit_logical_arith t x y z "&&" "&" "lean::nat_land"
| assign_binop.or   := emit_logical_arith t x y z "||" "|" "lean::nat_lor"
| assign_binop.xor  := emit_logical_arith t x y z "!=" "^" "lean::nat_lxor"
| assign_binop.le   := emit_arith t x y z "<=" "lean::nat_le"
| assign_binop.lt   := emit_arith t x y z "<"  "lean::nat_lt"
| assign_binop.eq   := emit_arith t x y z "==" "lean::nat_eq"
| assign_binop.ne   := emit_arith t x y z "!=" "lean::nat_ne"
| assign_binop.ile  := emit_big_binop x y z "lean::int_le"
| assign_binop.ilt  := emit_big_binop x y z "lean::int_lt"
| assign_binop.ieq  := emit_big_binop x y z "lean::int_eq"
| assign_binop.ine  := emit_big_binop x y z "lean::int_ne"
| assign_binop.array_read :=
  (match t with
   | type.object := emit_var x *> emit " = lean::array_obj" *> paren (emit_var y <+> emit_var z)
   | _           := emit_var x *> emit " = lean::sarray_data" *> emit_template_param t *> paren (emit_var y <+> emit_var z))
| assign_binop.array_push :=
  do env ← read, emit_var x, emit " = ",
     if env.ctx.find z = some type.object then emit "lean::array_push" else emit "lean::sarray_push",
     paren(emit_var y <+> emit_var z)
| assign_binop.string_push   := emit_var x *> emit " = lean::string_push" *> paren (emit_var y <+> emit_var z)
| assign_binop.string_append := emit_var x *> emit " = lean::string_append" *> paren (emit_var y <+> emit_var z)

/-- Emit `x := op(y)` -/
def emit_x_op_y (x : var) (op : string) (y : var) : extract_m unit :=
emit_var x *> emit " = " *> emit op *> paren(emit_var y)

def assign_unop2cpp (t : type) : assign_unop → string
| assign_unop.not          := if t = type.bool then "!" else "~"
| assign_unop.neg          := "-"
| assign_unop.ineg         := "lean::int_neg"
| assign_unop.nat2int      := "lean::nat2int"
| assign_unop.is_scalar    := "lean::is_scalar"
| assign_unop.is_shared    := "lean::is_shared"
| assign_unop.is_null      := "lean::is_null"
| assign_unop.box          := "lean::box"
| assign_unop.unbox        := "lean::unbox"
| assign_unop.cast         := "static_cast<" ++ type2cpp t ++ ">"
| assign_unop.array_copy   := "lean::array_copy"
| assign_unop.sarray_copy  := "lean::sarray_copy"
| assign_unop.array_size   := "lean::array_size"
| assign_unop.sarray_size  := "lean::sarray_size"
| assign_unop.string_len   := "lean::string_len"
| assign_unop.succ         := "lean::nat_succ"
| assign_unop.tag_ref      := "lean::cnstr_tag"
| assign_unop.tag          := "lean::obj_tag"

def emit_assign_unop (x : var) (t : type) (op : assign_unop) (y : var) : extract_m unit :=
emit_var x *> emit " = " *> emit (assign_unop2cpp t op) *> paren(emit_var y)

def emit_num_suffix : type → extract_m unit
| type.uint32 := emit "u"
| type.uint64 := emit "ull"
| type.int64  := emit "ll"
| _           := pure ()

def emit_assign_lit (x : var) (t : type) (l : literal) : extract_m unit :=
match l with
| literal.bool tt := emit_var x *> emit " = true"
| literal.bool ff := emit_var x *> emit " = false"
| literal.str s   := emit_var x *> emit " = lean::mk_string" *> paren(emit (repr s))
| literal.float v := emit_var x *> emit " = " *> emit v
| literal.num v   :=
  match t with
  | type.object :=
    emit_var x *> emit " = " *>
    if v < uint32_sz then emit "lean::mk_nat_obj" *> paren(emit v *> emit "u")
    else emit "lean::mk_mpz_core(lean::mpz(\"" *> emit v *> emit "\"))"
  | _           := emit_var x *> emit " = " *> emit v *> emit_num_suffix t

def unop2cpp : unop → string
| unop.inc_ref        := "lean::inc_ref"
| unop.dec_ref        := "lean::dec_ref"
| unop.dec_sref       := "lean::dec_shared_ref"
| unop.inc            := "lean::inc"
| unop.dec            := "lean::dec"
| unop.free           := "free"
| unop.dealloc        := "lean::dealloc"
| unop.array_pop      := "lean::array_pop"
| unop.sarray_pop     := "lean::sarray_pop"

def emit_unop (op : unop) (x : var) : extract_m unit :=
emit (unop2cpp op) *> paren(emit_var x)

def emit_apply (x : var) (ys : list var) : extract_m unit :=
match ys with
| (f::as) :=
  let n := as.length in
  if n > closure_max_args
  then emit "{ obj * as[" *> emit n *> emit "] = {" *> emit_var_list as *> emit "}; "
       *> emit_var x *> emit " = apply_m" *> paren(emit_var f <+> emit n <+> emit "as") *> emit "; }"
  else emit_var x *> emit " = apply_" *> emit n *> paren(emit_var_list ys)
| _       := throw "ill-formed apply"

def emit_closure (x : var) (f : fnid) (ys : list var) : extract_m unit :=
do env ← read,
   match env.cfg.env f with
   | some d := do
     emit_var x, emit " = lean::alloc_closure(",
     let arity := d.header.args.length,
     fname ← fid2cpp f,
     let fname := if arity > closure_max_args then "uncurry" ++ fname else fname,
     emit "reinterpret_cast<lean::lean_cfun>(" *> emit fname *> emit ")" <+> emit arity <+> emit ys.length,
     emit ")",
     ys.mfoldl (λ i y, emit ";\nlean::closure_set_arg" *> paren (emit_var x <+> emit i <+> emit_var y) *> pure (i+1)) 0,
     pure ()
   | none   := throw "invalid closure"

def emit_instr (ins : instr) : extract_m unit :=
ins.decorate_error $
(match ins with
 | (instr.assign x t y)             := emit_var x *> emit " = " *> emit_var y
 | (instr.assign_lit x t l)         := emit_assign_lit x t l
 | (instr.assign_unop x t op y)     := emit_assign_unop x t op y
 | (instr.assign_binop x t op y z)  := emit_assign_binop x t op y z
 | (instr.unop op x)                := emit_unop op x
 | (instr.call xs f ys)      := do
   emit_call_lhs xs, c ← is_const f,
   if c then emit_global f
   else (emit_fnid f *> paren(emit_var_list ys))
 | (instr.cnstr o t n sz)    := emit_var o *> emit " = lean::alloc_cnstr" *> paren(emit t <+> emit n <+> emit sz)
 | (instr.set o i x)         := emit "lean::cnstr_set_obj" *> paren (emit_var o <+> emit i <+> emit_var x)
 | (instr.get x o i)         := emit_var x *> emit " = lean::cnstr_obj" *> paren(emit_var o <+> emit i)
 | (instr.sset o d x)        := emit "lean::cnstr_set_scalar" *> paren(emit_var o <+> emit d <+> emit_var x)
 | (instr.sget x t o d)      := emit_var x *> emit " = lean::cnstr_scalar" *> emit_template_param t *> paren(emit_var o <+> emit d)
 | (instr.closure x f ys)    := emit_closure x f ys
 | (instr.apply x ys)        := emit_apply x ys
 | (instr.array a sz c)      := emit_var a *> emit " = lean::alloc_array" *> paren(emit_var sz <+> emit_var c)
 | (instr.sarray a t sz c)   := emit_var a *> emit " = lean::alloc_sarray" *> paren(emit_type_size t <+> emit_var sz <+> emit_var c)
 | (instr.array_write a i v) :=
   do env ← read,
      if env.ctx.find v = some type.object
      then emit "lean::array_set_obj" *> paren(emit_var a <+> emit_var i <+> emit_var v)
      else emit "lean::sarray_set_data" *> paren(emit_var a <+> emit_var i <+> emit_var v))
*> emit_eos

def emit_block (b : block) : extract_m unit :=
   unless b.phis.empty (throw "failed to extract C++ code, definition contains phi nodes")
*> emit_blockid b.id *> emit ":" *> emit_line
*> b.instrs.mfor emit_instr
*> emit_terminator b.term

def emit_header (h : header) : extract_m unit :=
emit_return h.return *> emit " " *> emit_fnid h.name *> paren(emit_arg_list h.args)

def decl_local (x : var) (ty : type) : extract_m unit :=
emit_type ty *> emit " " *> emit_var x *> emit_eos

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
emit "obj* uncurry" *> emit_fnid d.header.name *> emit "(obj** as)"

def emit_uncurry (d : decl) : extract_m unit :=
let nargs := d.header.args.length in
   emit_uncurry_header d *> emit " {\n"
*> emit "return " *> emit_fnid d.header.name *> paren (emit "as[0]" *> (nargs-1).mrepeat (λ i, emit ", " *> emit "as[" *> emit (i+1) *> emit "]")) *> emit_eos
*> emit "}\n"

def emit_def_core (d : decl) : extract_m unit :=
d.decorate_error $
match d with
| (decl.defn h bs)  :=
  emit_header h *> emit " {" *> emit_line
  *> decl_locals h.args *> bs.mfor emit_block
  *> emit "}" *> emit_line *>
  when (need_uncurry d) (emit_uncurry d)
| _ := pure ()

section
local attribute [reducible] extract_m
def emit_def (d : decl) : extract_m unit :=
do env ← read,
   ctx ← monad_lift $ infer_types d env.cfg.env,
   adapt_reader (λ env : extract_env, {ctx := ctx, ..env}) $
     emit_def_core d
end

def collect_used (d : list decl) : fnid_set :=
d.foldl (λ s d, match d with
  | decl.defn _ bs := bs.foldl (λ s b, b.instrs.foldl (λ s ins, match ins with
    | instr.call _ fid _    := s.insert fid
    | instr.closure _ fid _ := s.insert fid
    | _                     := s) s) s
  | _                := s) mk_fnid_set

def emit_used_headers (ds : list decl) : extract_m unit :=
let used := collect_used ds in
do env ← read,
used.mfor (λ fid, match env.cfg.env fid with
 | some d := do
   unless (env.cfg.external_names fid = none) (emit "extern \"C\" "),
   emit_header d.header *> emit ";\n" *> when (need_uncurry d) (emit_uncurry_header d *> emit ";\n")
 | _      := pure ())

def emit_global_var_decls (ds : list decl) : extract_m unit :=
ds.mfor $ λ d, when d.header.is_const $
  emit_type d.header.return.head.ty *> emit " " *> emit_global d.header.name *> emit ";\n"

def emit_initialize_proc (ds : list decl) : extract_m unit :=
do env ← read,
   emit "void ", emit initialize_prefix, emit env.cfg.unit_name, emit "() {\n",
   emit "if (_G_initialized) return;\n",
   emit "_G_initialized = true;\n",
   env.cfg.unit_deps.mfor $ λ dep, emit initialize_prefix *> emit dep *> emit "();\n",
   ds.mfor $ λ d, when d.header.is_const $
     emit_global d.header.name *> emit " = " *> emit_fnid d.header.name *> emit "();\n",
   emit "}\n"

def emit_finalize_proc (ds : list decl) : extract_m unit :=
do env ← read,
   emit "void ", emit finalize_prefix, emit env.cfg.unit_name, emit "() {\n",
   emit "if (_G_finalized) return;\n",
   emit "_G_finalized = true;\n",
   env.cfg.unit_deps.mfor $ λ dep, emit finalize_prefix *> emit dep *> emit "();\n",
   ds.mfor $ λ d, when (d.header.is_const && d.header.return.head.ty = type.object) $
     emit "if (!is_scalar(" *> emit_global d.header.name *> emit ")) lean::dec_ref(" *> emit_global d.header.name *> emit ");\n",
   emit "}\n"

def emit_main_proc : extract_m unit :=
do env ← read,
   match env.cfg.main_proc with
   | some fid :=
     (match env.cfg.env fid with
      | some d :=
        unless (d.header.args.length = 0) (throw $ "invalid main function '" ++ to_string fid ++ "', it must not take any arguments")
        *> unless (d.header.return.length = 1 && d.header.return.head.ty = type.int32) (throw $ "invalid main function '" ++ to_string fid ++ "', return type must be int32")
        *> emit "int main() {\n"
        *> emit initialize_prefix *> emit env.cfg.unit_name *> emit "();\n"
        *> emit "int r = " *> emit_fnid fid *> emit "();\n"
        *> emit finalize_prefix *> emit env.cfg.unit_name *> emit "();\n"
        *> emit "return r;\n}\n"
      | none := throw ("unknown main function '" ++ to_string fid ++ "'"))
   | none := pure ()

end cpp

open cpp

def extract_cpp (ds : list decl) (cfg : extract_cpp_config := {}) : except format string :=
let out := file_header cfg.runtime_dir ++ "\n" in
run (emit_used_headers ds
     *> emit "static bool _G_initialized = false;\n"
     *> emit "static bool _G_finalized = false;\n"
     *> emit_global_var_decls ds
     *> emit_initialize_proc ds
     *> emit_finalize_proc ds
     *> ds.mfor emit_def
     *> emit_main_proc
     *> get)
{cfg := cfg} out

end ir
end lean
