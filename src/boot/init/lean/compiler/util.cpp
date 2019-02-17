// Lean compiler output
// Module: init.lean.compiler.util
// Imports: init.lean.expr
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_compiler_mk__lc__proof___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_compiler_object__type;
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_lean_compiler_void__type;
obj* l_lean_compiler_mk__lc__proof(obj*);
obj* l_lean_compiler_neutral__expr;
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_lean_compiler_unreachable__expr;
obj* _init_l_lean_compiler_neutral__expr() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_neutral");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean_expr_mk_const(x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_compiler_unreachable__expr() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_unreachable");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean_expr_mk_const(x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_compiler_object__type() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_obj");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean_expr_mk_const(x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_compiler_void__type() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_void");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean_expr_mk_const(x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_compiler_mk__lc__proof___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lc_proof");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean_expr_mk_const(x_2, x_0);
return x_3;
}
}
obj* l_lean_compiler_mk__lc__proof(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_compiler_mk__lc__proof___closed__1;
lean::inc(x_1);
x_3 = lean_expr_mk_app(x_1, x_0);
return x_3;
}
}
void initialize_init_lean_expr();
static bool _G_initialized = false;
void initialize_init_lean_compiler_util() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_expr();
 l_lean_compiler_neutral__expr = _init_l_lean_compiler_neutral__expr();
lean::mark_persistent(l_lean_compiler_neutral__expr);
 l_lean_compiler_unreachable__expr = _init_l_lean_compiler_unreachable__expr();
lean::mark_persistent(l_lean_compiler_unreachable__expr);
 l_lean_compiler_object__type = _init_l_lean_compiler_object__type();
lean::mark_persistent(l_lean_compiler_object__type);
 l_lean_compiler_void__type = _init_l_lean_compiler_void__type();
lean::mark_persistent(l_lean_compiler_void__type);
 l_lean_compiler_mk__lc__proof___closed__1 = _init_l_lean_compiler_mk__lc__proof___closed__1();
lean::mark_persistent(l_lean_compiler_mk__lc__proof___closed__1);
}
