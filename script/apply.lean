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
  emit s!"#define FN{i}(f) reinterpret_cast<fn{i}>(lean_closure_fun(f))\n"

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
  genSeq n (s!"as[{·}]")

-- make string: "fx(0), ..., fx(n-1)"
def mkFsArgs (n : Nat) : String :=
  genSeq n (s!"fx({·})")

-- make string: "lean_inc(fx(0)); ...; lean_inc(fx(n-1))"
def mkIncFs (n : Nat) : String :=
  genSeq n (s!"lean_inc(fx({·})); ") (sep := "")

def mkApplyI (n : Nat) (max : Nat) : M Unit := do
  let argDecls := mkArgDecls n
  let args := mkArgs n
  emit s!"extern \"C\" LEAN_EXPORT obj* lean_apply_{n}(obj* f, {argDecls}) \{
if (lean_is_scalar(f)) \{ {genSeq n (s!"lean_dec(a{·+1}); ") (sep := "")}return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + {n}) \{
  if (lean_is_exclusive(f)) \{
    switch (arity) \{\n"
  for j in [n:max + 1] do
    let fs := mkFsArgs (j - n)
    let sep := if j = n then "" else ", "
    emit s!"    case {j}: \{ obj* r = FN{j}(f)({fs}{sep}{args}); lean_free_small_object(f); return r; }\n"
  emit "    }
  }
  switch (arity) {\n"
  for j in [n:max + 1] do
    let lean_incfs := mkIncFs (j - n)
    let fs := mkFsArgs (j - n)
    let sep := if j = n then "" else ", "
    emit  s!"  case {j}: \{ {lean_incfs}obj* r = FN{j}(f)({fs}{sep}{args}); lean_dec_ref(f); return r; }\n"
  emit s!"  default:
    lean_assert(arity > {max});
    obj * as[{n}] = \{ {args} };
    obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
    for (unsigned i = 0; i < fixed; i++) \{ lean_inc(fx(i)); args[i] = fx(i); }
    for (unsigned i = 0; i < {n}; i++) args[fixed+i] = as[i];
    obj * r = FNN(f)(args);
    lean_dec_ref(f);
    return r;
  }
} else if (arity < fixed + {n}) \{\n"
  if n ≥ 2 then do
    emit  s!"  obj * as[{n}] = \{ {args} };
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) \{ lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = curry(f, arity, args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, {n}+fixed-arity, &as[arity-fixed]);\n"
  else emit s!"  lean_assert(fixed < arity);
  lean_unreachable();\n"
  emit s!"} else \{
  return fix_args(f, \{{args}});
}
}\n"

def mkCurry (max : Nat) : M Unit := do
  emit "obj* curry(void* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();\n"
  for i in [0:max] do
    let as := mkAsArgs (i+1)
    emit  s!"case {i+1}: return reinterpret_cast<fn{i+1}>(f)({as});\n"
  emit "default: return reinterpret_cast<fnn>(f)(as);
}
}
static obj* curry(obj* f, unsigned n, obj** as) { return curry(lean_closure_fun(f), n, as); }\n"

def mkApplyN (max : Nat) : M Unit := do
  emit "extern \"C\" LEAN_EXPORT obj* lean_apply_n(obj* f, unsigned n, obj** as) {
switch (n) {
case 0: lean_unreachable();\n"
  for i in [0:max] do
    let as := mkAsArgs (i+1)
    emit  s!"case {i+1}: return lean_apply_{i+1}(f, {as});\n"
  emit "default: return lean_apply_m(f, n, as);
}
}\n"

def mkApplyM (max : Nat) : M Unit :=
  emit s!"extern \"C\" LEAN_EXPORT obj* lean_apply_m(obj* f, unsigned n, obj** as) \{
lean_assert(n > {max});
if (lean_is_scalar(f)) \{ for (unsigned i = 0; i < n; i++) \{ lean_dec(as[i]); } return f; } // f is an erased proof
unsigned arity = lean_closure_arity(f);
unsigned fixed = lean_closure_num_fixed(f);
if (arity == fixed + n) \{
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) \{ lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < n; i++) args[fixed+i] = as[i];
  obj * r = FNN(f)(args);
  lean_dec_ref(f);
  return r;
} else if (arity < fixed + n) \{
  obj ** args = static_cast<obj**>(LEAN_ALLOCA(arity*sizeof(obj*))); // NOLINT
  for (unsigned i = 0; i < fixed; i++) \{ lean_inc(fx(i)); args[i] = fx(i); }
  for (unsigned i = 0; i < arity-fixed; i++) args[fixed+i] = as[i];
  obj * new_f = FNN(f)(args);
  lean_dec_ref(f);
  return lean_apply_n(new_f, n+fixed-arity, &as[arity-fixed]);
} else \{
  return fix_args(f, n, as);
}
}\n"

def mkFixArgs : M Unit := emit "
static obj* fix_args(obj* f, unsigned n, obj*const* as) {
    unsigned arity = lean_closure_arity(f);
    unsigned fixed = lean_closure_num_fixed(f);
    unsigned new_fixed = fixed + n;
    lean_assert(new_fixed < arity);
    obj * r = lean_alloc_closure(lean_closure_fun(f), arity, new_fixed);
    obj ** source = lean_closure_arg_cptr(f);
    obj ** target = lean_closure_arg_cptr(r);
    if (!lean_is_exclusive(f)) {
      for (unsigned i = 0; i < fixed; i++, source++, target++) {
          *target = *source;
          lean_inc(*target);
      }
      lean_dec_ref(f);
    } else {
      for (unsigned i = 0; i < fixed; i++, source++, target++) {
          *target = *source;
      }
      lean_free_small_object(f);
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
#define obj lean_object
#define fx(i) lean_closure_arg_cptr(f)[i]\n"
  mkFixArgs
  for i in [0:max] do mkTypedefFn (i+1)
  emit "typedef obj* (*fnn)(obj**); // NOLINT
#define FNN(f) reinterpret_cast<fnn>(lean_closure_fun(f))\n"
  mkCurry max
  emit "extern \"C\" obj* lean_apply_n(obj*, unsigned, obj**);\n"
  for i in [0:max] do mkApplyI (i+1) max
  mkApplyM max
  mkApplyN max
  emit "}\n"

-- #eval (mkApplyCpp 4).run none

#eval (mkApplyCpp Lean.closureMaxArgs).run "src/runtime/apply.cpp"
