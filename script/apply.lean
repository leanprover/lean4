import Lean.Runtime

abbrev M := ReaderT IO.FS.Stream IO

def M.run (a : M Unit) (out? : Option String := none) : IO Unit :=
  match out? with
  | some out => do
    IO.FS.withFile out .write (ReaderT.run a ∘ .ofHandle)
  | none => IO.getStdout >>= (ReaderT.run a)

def emit (s : String) : M Unit := do
  (← read).putStr s

def mkTypedefFn (i : Nat) : M Unit := do
  let args := (List.replicate i "obj*").intersperse ", " |> String.join
  emit s!"typedef obj* (*fn{i})({args}); // NOLINT\n"
  emit s!"#define FN{i}(f) reinterpret_cast<fn{i}>(closure_fun(f))\n"

def genSeq (n : Nat) (f : Nat → String) (sep := ", ") : String := 
  List.range n |>.map f |>.intersperse sep |> .join

-- make string: "obj* a1, obj* a2, ..., obj* an"
def mkArgDecls (n : Nat) : String :=
  genSeq n (s!"obj* a{·+1}")

-- make string: "a{s+1}, ..., a{n}"
def mkArgsFrom (s n : Nat) : String :=
  genSeq (n-s) (s!"a{s+·+1}")

-- make string: "a1, a2, ..., a{n}"
def mkArgs (n : Nat) : String := mkArgsFrom 0 n

-- make string: "as[0], as[1], ..., as[n-1]"
def mkAsArgs (n : Nat) : String :=
  genSeq n (s!"a[{·}]")

-- make string: "fx(0), ..., fx(n-1)"
def mkFsArgs (n : Nat) : String :=
  genSeq n (s!"fx({·})")

-- make string: "inc(fx(0)); ...; inc(fx(n-1))"
def mkIncFs (n : Nat) : String :=
  genSeq n (s!"inc(fx({·}))") (sep := "; ")

def mkApplyI (n : Nat) (max : Nat) : M Unit := do
  let argDecls := mkArgDecls n
  let args := mkArgs n
  emit s!"obj* apply_{n}(obj* f, {argDecls}) \{
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + {n}) \{
  if (is_exclusive(f)) \{
    switch (arity) \{\n"
  for j in [n:max + 1] do
    let fs := mkFsArgs (j - n)
    let sep := if j = n then "" else ", "
    emit s!"    case {j}: \{ obj* r = FN{j}(f)({fs}{sep}{args}); free_closure_obj(f); return r; }\n"
  emit "    }
  }
  switch (arity) {\n"
  for j in [n:max + 1] do
    let incfs := mkIncFs (j - n)
    let fs := mkFsArgs (j - n)
    let sep := if j = n then "" else ", "
    emit  s!"  case {j}: \{ {incfs}obj* r = FN{j}(f)({fs}{sep}{args}); dec_ref(f); return r; }\n"
  emit s!"  default:
    lean_assert(arity > {max});
    obj * as[{n}] = \{ {args} };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) \{ inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < {n}; i++) args[fixed+i] = as[i];
    obj * r = FNN(f)(args);
    dec_ref(f);
    return r;
  }
} else if (arity < fixed + {n}) \{\n"
  if n ≥ 2 then do
    emit  s!"  obj * as[{n}] = \{ {args} };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) \{ inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  dec_ref(f);
  return apply_n(new_f, {n}+fixed-arity, as+arity-fixed);\n"
  else emit s!"  lean_assert(fixed < arity);
  lean_unreachable();
} else \{
  return fix_args(f, \{{args}});
}
}\n"

def mkCurry (max : Nat) : M Unit := do
  emit "static obj* curry(void* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();\n"
  for i in [0:max] do
    let as := mkAsArgs (i+1)
    emit  s!"case {i+1}: return reinterpret_cast<fn{i+1}>(f)({as});
default: return reinterpret_cast<fnn>(f)(as);
}
}
static obj* curry(obj* f, unsigned n, obj** as) \{ return curry(closure_fun(f), n, as); }\n"

def mkApplyN (max : Nat) : M Unit := do
  emit "obj* apply_n(obj* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();\n"
  for i in [0:max] do
    let as := mkAsArgs (i+1)
    emit  s!"case {i+1}: return apply_{i+1}(f, {as});
default: return apply_m(f, n, as);
}
}\n"

def mkApplyM (max : Nat) : M Unit :=
  emit s!"obj* apply_m(obj* f, unsigned n, obj** as) \{
lean_assert(n > {max});
unsigned arity = closure_arity(f);
unsigned fixed = closure_num_fixed(f);
if (arity == fixed + n) \{
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) \{ inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < n; i++) args[fixed+i] = as[i];
  obj * r = FNN(f)(args);
  dec_ref(f);
  return r;
} else if (arity < fixed + n) \{
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) \{ inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = FNN(f)(args);
  dec_ref(f);
  return apply_n(new_f, n+fixed-arity, as+arity-fixed);
} else \{
  return fix_args(f, n, as);
}
}\n"

def mkFixArgs : M Unit := emit "
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

def mkCopyright : M Unit := emit "/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
"

def mkApplyCpp (max : Nat) : M Unit := do
  mkCopyright
  emit "// DO NOT EDIT, this is an automatically generated file
// Generated using script: ../../gen/apply.lean
#include \"runtime/apply.h\"
namespace lean {
#define obj object
#define fx(i) closure_arg_cptr(f)[i]\n"
  mkFixArgs
  for i in [0:max] do mkTypedefFn (i+1)
  emit "typedef obj* (*fnn)(obj**); // NOLINT
#define FNN(f) reinterpret_cast<fnn>(closure_fun(f))\n"
  mkCurry max
  emit "obj* apply_n(obj*, unsigned, obj**);\n"
  for i in [0:max] do mkApplyI (i+1) max
  mkApplyM max
  mkApplyN max
  emit "}\n"

-- make string: "object* a1, object* a2, ..., object** an"
def mkArgDecls' (n : Nat) : String :=
  genSeq n (s!"object* a{·+1}")

def mkApplyH (max : Nat) : M Unit := do
  mkCopyright
  emit "// DO NOT EDIT, this is an automatically generated file
// Generated using script: ../../gen/apply.lean
#pragma once
#include \"runtime/object.h\"
#define LEAN_CLOSURE_MAX_ARGS {max}"
  emit "namespace lean {\n"
  for i in [0:max] do
    let args := mkArgDecls' (i+1)
    emit  s!"object* apply_{i+1}(object* f, {args});
object* apply_n(object* f, unsigned n, object** args);
// pre: n > {max}
object* apply_m(object* f, unsigned n, object** args);
}\n"

-- #eval (mkApplyCpp 4).run none

#eval (mkApplyCpp Lean.closureMaxArgs).run "../src/runtime/apply.cpp"
#eval (mkApplyH Lean.closureMaxArgs).run "../src/runtime/apply.h"
