import init.lean.config init.io
open io

@[reducible] def m := reader_t handle io

def m.run (a : m unit) (out : option string := none) : io unit :=
match out with
| some out := do
   h ← mk_file_handle out io.mode.write,
   a.run h,
   fs.close h
| none := stdout >>= a.run

def emit (s : string) : m unit :=
⟨λ h, fs.write h s⟩

def mk_typedef_fn (i : nat) : m unit :=
let args := string.join $ (list.repeat "obj*" i).intersperse ", " in
do emit $ sformat! "typedef obj* (*fn{i})({args}); // NOLINT\n",
   emit $ sformat! "#define FN{i}(f) reinterpret_cast<fn{i}>(closure_fun(f))\n"

-- Make string: "obj* a1, obj* a2, ..., obj* an"
def mk_arg_decls (n : nat) : string :=
string.join $ (n.repeat (λ i r, r ++ [sformat! "obj* a{i+1}"]) []).intersperse ", "

-- Make string: "a1, a2, ..., a{n}"
def mk_args (n : nat) : string :=
string.join $ (n.repeat (λ i r, r ++ [sformat! "a{i+1}"]) []).intersperse ", "

-- Make string: "a{s}, a{s+1}, ..., a{n}"
def mk_args_from (s n : nat) : string :=
string.join $ ((n-s).repeat (λ i r, r ++ [sformat! "a{s+i+1}"]) []).intersperse ", "

-- Make string: "as[0], as[1], ..., as[n-1]"
def mk_as_args (n : nat) : string :=
string.join $ (n.repeat (λ i r, r ++ [sformat! "as[{i}]"]) []).intersperse ", "

-- Make string: "fx(0), ..., fx(n-1)"
def mk_fs_args (n : nat) : string :=
string.join $ (n.repeat (λ i r, r ++ [sformat! "fx({i})"]) []).intersperse ", "

-- Make string: "inc(fx(0)); ...; inc(fx(n-1))"
def mk_inc_fs (n : nat) : string :=
string.join $ (n.repeat (λ i r, r ++ [sformat! "inc(fx({i})); "]) [])


def mk_apply_i (n : nat) (max : nat) : m unit :=
let arg_decls := mk_arg_decls n in
let args := mk_args n in
do emit $ sformat! "obj* apply_{n}(obj* f, {arg_decls}) {{\n",
   emit "unsigned arity = closure_arity(f);\n",
   emit "unsigned fixed = closure_num_fixed(f);\n",
   emit $ sformat! "if (arity == fixed + {n}) {{\n",
     emit $ sformat! "  if (is_exclusive(f)) {{\n",
     emit $ sformat! "    switch (arity) {{\n",
     max.mrepeat $ λ i, do {
       let j := i + 1,
       when (j ≥ n) $
         let fs := mk_fs_args (j - n) in
         let sep := if j = n then "" else ", " in
         emit $ sformat! "    case {j}: {{ obj* r = FN{j}(f)({fs}{sep}{args}); free_closure_obj(f); return r; }\n"
     },
     emit "    }\n",
     emit "  }\n",
     emit $ sformat! "  switch (arity) {{\n",
     max.mrepeat $ λ i, do {
       let j := i + 1,
       when (j ≥ n) $
         let incfs := mk_inc_fs (j - n) in
         let fs := mk_fs_args (j - n) in
         let sep := if j = n then "" else ", " in
         emit $ sformat! "  case {j}: {{ {incfs}obj* r = FN{j}(f)({fs}{sep}{args}); dec_ref(f); return r; }\n"
     },
     emit "  default:\n",
       emit $ sformat! "    lean_assert(arity > {max});\n",
       emit $ sformat! "    obj * as[{n}] = {{ {args} };\n",
       emit "    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT\n",
       emit "    for (unsigned i = 0; i < fixed; i++) { inc(fx(i)); args[i] = fx(i); }\n",
       emit $ sformat! "    for (unsigned i = 0; i < {n}; i++) args[fixed+i] = as[i];\n",
       emit "    obj * r = FNN(f)(args);\n",
       emit "    dec_ref(f);\n",
       emit "    return r;\n",
     emit "  }\n",
   emit $ sformat! "} else if (arity < fixed + {n}) {{\n",
     if n ≥ 2 then do
       emit $ sformat! "  obj * as[{n}] = {{ {args} };\n",
       emit "  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT\n",
       emit "  for (unsigned i = 0; i < fixed; i++) { inc(fx(i)); args[i] = fx(i); }\n",
       emit "  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];\n",
       emit "  obj * new_f = curry(f, arity, args);\n",
       emit "  dec_ref(f);\n",
       emit $ sformat! "  return apply_n(new_f, {n}+fixed-arity, as+arity-fixed);\n"
     else emit "  lean_assert(fixed < arity);\n  lean_unreachable();\n",
   emit "} else {\n",
     emit $ sformat! "  return fix_args(f, {{{args}});\n",
   emit "}\n",
   emit "}\n"

def mk_curry (max : nat) : m unit :=
do emit "static obj* curry(void* f, unsigned n, obj** as) {\n",
   emit "switch (n) {\n",
   emit "case 0: lean_unreachable();\n",
   max.mrepeat $ λ i,
     let as := mk_as_args (i+1) in
     emit $ sformat! "case {i+1}: return reinterpret_cast<fn{i+1}>(f)({as});\n",
   emit "default: return reinterpret_cast<fnn>(f)(as);\n",
   emit "}\n",
   emit "}\n",
   emit "static obj* curry(obj* f, unsigned n, obj** as) { return curry(closure_fun(f), n, as); }\n"

def mk_apply_n (max : nat) : m unit :=
do emit "obj* apply_n(obj* f, unsigned n, obj** as) {\n",
   emit "switch (n) {\n",
   emit "case 0: lean_unreachable();\n",
   max.mrepeat $ λ i,
     let as := mk_as_args (i+1) in
     emit $ sformat! "case {i+1}: return apply_{i+1}(f, {as});\n",
   emit "default: return apply_m(f, n, as);\n",
   emit "}\n",
   emit "}\n"

def mk_apply_m (max : nat) : m unit :=
do emit "obj* apply_m(obj* f, unsigned n, obj** as) {\n",
   emit $ sformat! "lean_assert(n > {max});\n",
   emit "unsigned arity = closure_arity(f);\n",
   emit "unsigned fixed = closure_num_fixed(f);\n",
   emit $ sformat! "if (arity == fixed + n) {{\n",
     emit "  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT\n",
     emit "  for (unsigned i = 0; i < fixed; i++) { inc(fx(i)); args[i] = fx(i); }\n",
     emit "  for (unsigned i = 0; i < n; i++) args[fixed+i] = as[i];\n",
     emit "  obj * r = FNN(f)(args);\n",
     emit "  dec_ref(f);\n",
     emit "  return r;\n",
   emit $ sformat! "} else if (arity < fixed + n) {{\n",
     emit "  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT\n",
     emit "  for (unsigned i = 0; i < fixed; i++) { inc(fx(i)); args[i] = fx(i); }\n",
     emit "  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];\n",
     emit "  obj * new_f = FNN(f)(args);\n",
     emit "  dec_ref(f);\n",
     emit "  return apply_n(new_f, n+fixed-arity, as+arity-fixed);\n",
   emit "} else {\n",
     emit "  return fix_args(f, n, as);\n",
   emit "}\n",
   emit "}\n"

def mk_fix_args : m unit :=
emit "
static obj* fix_args(obj* f, unsigned n, obj*const* as) {
    unsigned arity = closure_arity(f);
    unsigned fixed = closure_num_fixed(f);
    unsigned new_fixed = fixed + n;
    lean_assert(new_fixed < arity);
    obj * r = alloc_closure(closure_fun(f), arity, new_fixed);
    obj ** source = closure_arg_cptr(f);
    obj ** target = closure_arg_cptr(r);
    if (!is_exclusive(f)) {
      for (unsigned i = 0; i < fixed; i++, source++, target++) {
          *target = *source;
          inc(*target);
      }
      dec_ref(f);
    } else {
      for (unsigned i = 0; i < fixed; i++, source++, target++) {
          *target = *source;
      }
      free_closure_obj(f);
    }
    for (unsigned i = 0; i < n; i++, as++, target++) {
        *target = *as;
    }
    return r;
}

static inline obj* fix_args(obj* f, std::initializer_list<obj*> const & l) {
    return fix_args(f, l.size(), l.begin());
}
"

def mk_copyright : m unit :=
emit
"/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
"

def mk_apply_cpp (max : nat) : m unit :=
do mk_copyright,
   emit "// DO NOT EDIT, this is an automatically generated file\n",
   emit "// Generated using script: ../../gen/apply.lean\n",
   emit "#include \"runtime/apply.h\"\n",
   emit "namespace lean {\n",
   emit "#define obj object\n",
   emit "#define fx(i) closure_arg_cptr(f)[i]\n",
   mk_fix_args,
   max.mrepeat $ λ i, mk_typedef_fn (i+1),
   emit "typedef obj* (*fnn)(obj**); // NOLINT\n",
   emit "#define FNN(f) reinterpret_cast<fnn>(closure_fun(f))\n",
   mk_curry max,
   emit "obj* apply_n(obj*, unsigned, obj**);\n",
   max.mrepeat $ λ i, do { mk_apply_i (i+1) max },
   mk_apply_m max,
   mk_apply_n max,
   emit "}\n"

-- Make string: "object* a1, object* a2, ..., object** an"
def mk_arg_decls' (n : nat) : string :=
string.join $ (n.repeat (λ i r, r ++ [sformat! "object* a{i+1}"]) []).intersperse ", "

def mk_apply_h (max : nat) : m unit :=
do mk_copyright,
   emit "// DO NOT EDIT, this is an automatically generated file\n",
   emit "// Generated using script: ../../gen/apply.lean\n",
   emit "#pragma once\n",
   emit "#include \"runtime/object.h\"\n",
   emit $ sformat! "#define LEAN_CLOSURE_MAX_ARGS {max}"
   emit "namespace lean {\n",
   max.mrepeat $ λ i,
     let args := mk_arg_decls' (i+1) in
     emit $ sformat! "object* apply_{i+1}(object* f, {args});\n",
   emit "object* apply_n(object* f, unsigned n, object** args);\n",
   emit $ sformat! "// pre: n > {max}\n",
   emit "object* apply_m(object* f, unsigned n, object** args);\n",
   emit "}\n"

-- #eval (mk_apply_cpp 4).run none

#eval (mk_apply_cpp lean.closure_max_args).run "..//src//runtime//apply.cpp"
#eval (mk_apply_h lean.closure_max_args).run "..//src//runtime//apply.h"
