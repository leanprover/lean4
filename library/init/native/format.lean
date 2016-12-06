/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.name
import init.meta.format
import init.function

import init.native.ir

def intersperse {A : Type} (elem : A) : list A → list A
| [] := []
| (x :: []) := [x]
| (x :: xs) := x :: elem :: intersperse xs

meta def format_concat : list format → format
| [] := format.nil
| (f :: fs) := f ++ format_concat fs

meta def comma_sep (items : list format) : format :=
format_concat
  (intersperse (format.of_string "," ++ format.space) items)

namespace format_cpp

meta def mangle_name (n : name) : format :=
    to_fmt $ name.to_string_with_sep "_" n

private meta def mk_constructor_args : list name → list format
| [] := []
| (n :: ns) := mangle_name n :: mk_constructor_args ns

private meta def mk_constructor
  (arity : nat)
  (fs : list name) : format :=
  "lean::mk_vm_constructor(" ++ to_fmt arity ++ "," ++
  (format.bracket "{" "}" (comma_sep $ mk_constructor_args fs)) ++ ")"

private meta def mk_call (symbol : name) (args : list name) : format :=
  mangle_name symbol ++ (format.bracket "(" ")" (comma_sep $ list.map mangle_name args))

meta def literal : ir.literal → format
| (ir.literal.nat n) := to_fmt "lean::mk_vm_nat(" ++ to_fmt n ++ ")"

meta def format_local (n : name) : format :=
  to_fmt (name.to_string_with_sep "_" n)

meta def string_lit (s : string) : format :=
  format.bracket "\"" "\"" (to_fmt s)

meta def block (body : format) : format :=
format.bracket "{" "}" (format.nest 4 (format.line ++ body) ++ format.line)

meta def expr' (action : ir.stmt → format) : ir.expr → format
| (ir.expr.call f xs) := mk_call f xs
| (ir.expr.mk_object n fs) :=
  if n = 0
  -- Over time I should remove these special case functions,
  -- and just use the def language of the IR.
  then to_fmt "lean::mk_vm_simple(0)"
  else mk_constructor n fs
| (ir.expr.global n) :=
  mk_call n []
| (ir.expr.locl n) :=
  mangle_name n
| (ir.expr.lit l) :=
   literal l
| (ir.expr.block s) :=
  block (action s)
-- project really should only work for like fields/primtive arrays, this is a temporary hack
| (ir.expr.project obj n) :=
  "cfield(" ++ (mangle_name obj) ++ ", " ++ (to_fmt n) ++ ")"
| (ir.expr.panic err_msg) :=
  to_fmt "throw std::runtime_error(" ++ string_lit err_msg ++ ");"
| (ir.expr.mk_native_closure n args) :=
"lean::mk_native_closure(*g_env, lean::name({\"" ++ name.to_string_with_sep "\", \"" n ++ "\"})" ++ "," ++
   format.bracket "{" "}" (comma_sep (list.map format_local args)) ++ ")"
 | (ir.expr.invoke n args) :=
 "lean::invoke(" ++ name.to_string_with_sep "_" n ++ ", " ++
 (comma_sep (list.map format_local args)) ++ ")"
 | (ir.expr.uninitialized) := ";"
 | (ir.expr.assign n val) := mangle_name n ++ " = " ++ expr' val
 | (ir.expr.constructor _ _) := "NYI"
 | (ir.expr.address_of e) := "& " ++ mangle_name e ++ ";"
 | (ir.expr.equals e1 e2) := expr' e1 ++ " == " ++ expr' e2
 | (ir.expr.raw_int n) := to_string n
 | (ir.expr.sub e1 e2) :=
   expr' e1 ++ " - " ++ expr' e2

meta def default_case (body : format) : format :=
  to_fmt "default:" ++ block body

meta def case (action : ir.stmt → format) : (nat × ir.stmt) → format
| (n, s) := "case " ++ to_fmt n ++ ":" ++ block (action s ++ format.line ++ "break;" ++ format.line)

meta def cases (action : ir.stmt → format) : list (nat × ir.stmt) → format
| [] := format.nil
| (c :: cs) := case action c ++ cases cs

meta def ty : ir.ty → format
| ir.ty.object := format.of_string "lean::vm_obj "
| (ir.ty.ref T) := ty T ++ format.of_string " const & "
| (ir.ty.mut_ref T) := ty T ++ format.of_string " &"
| (ir.ty.tag _ _) := format.of_string "an_error"
| (ir.ty.int) := "int "
| (ir.ty.object_buffer) := "lean::buffer<lean::vm_obj> "
| (ir.ty.name n) := to_fmt n ++ format.space

meta def parens (inner : format) : format :=
  format.bracket "(" ")" inner

meta def stmt : ir.stmt → format
| (ir.stmt.e e) := expr' stmt e ++ ";"
| (ir.stmt.return e) :=
  format.of_string "return"  ++
  format.space ++
  expr' stmt e ++ format.of_string ";"
| (ir.stmt.letb n t ir.expr.uninitialized nop) :=
  ty t ++ (mangle_name n) ++ to_fmt ";" ++ format.line
  -- type checking should establish that these two types are equal
| (ir.stmt.letb n t (ir.expr.constructor ty_name args) nop) :=
  -- temporary hack, need to think about how to model this better
  if ty_name = "lean::name"
  then let ctor_args := comma_sep (list.map (string_lit ∘ to_string) args) in
    ty t ++ (mangle_name n) ++ " = lean::name({" ++ ctor_args ++ "})" ++ to_fmt ";" ++ format.line
  else let ctor_args := parens $ comma_sep (list.map mangle_name args) in
       ty t ++ (mangle_name n) ++ ctor_args ++ to_fmt ";" ++ format.line
| (ir.stmt.letb n t v body) :=
  ty t ++ (mangle_name n) ++ (to_fmt " = ") ++ (expr' stmt v) ++ to_fmt ";" ++
  format.line ++ stmt body
| (ir.stmt.switch scrut cs default) :=
  (to_fmt "switch (") ++ (mangle_name scrut) ++ (to_fmt ")") ++
  (block (format.line ++ cases stmt cs ++ default_case (stmt default)))
| ir.stmt.nop := format.of_string ";"
| (ir.stmt.ite cond tbranch fbranch) :=
  "if (" ++ mangle_name cond ++ ") {" ++ format.line ++
    stmt tbranch ++ format.line ++
  "} else {" ++ format.line ++
    stmt fbranch ++ format.line ++
  "}" ++ format.line
| (ir.stmt.seq cs) :=
  format_concat (list.map (fun c, stmt c ++ format.line) cs)

meta def expr := expr' stmt

meta def format_param (param : name × ir.ty) :=
ty (prod.snd param) ++
format.space ++
to_fmt (name.to_string_with_sep "_" (mk_str_name "_$local$_" (name.to_string_with_sep "_" (prod.fst param))))

meta def format_argument_list (tys : list (name × ir.ty)) : format :=
  format.bracket "(" ")" (comma_sep (list.map format_param tys))

-- meta_def format_prototypes ()
meta def defn (d : ir.defn) : format :=
  match d with
  | ir.defn.mk n arg_tys ret_ty body :=
    let body := stmt body in
    (ty ret_ty) ++ format.space ++ (mangle_name n) ++
    (format_argument_list arg_tys) ++ format.space ++
    (format.bracket "{" "}" $ format.nest 4 (format.line ++ body) ++ format.line)
  end

end format_cpp
