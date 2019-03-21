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
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Compiler_mkLcProof(obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Compiler_objectType;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Compiler_voidType;
obj* l_Lean_Compiler_mkLcProof___closed__1;
obj* l_Lean_Compiler_neutralExpr;
obj* l_Lean_Compiler_unreachableExpr;
obj* _init_l_Lean_Compiler_neutralExpr() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_neutral");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_unreachableExpr() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_unreachable");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_objectType() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_obj");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_voidType() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_void");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Compiler_mkLcProof___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lcProof");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Compiler_mkLcProof(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Compiler_mkLcProof___closed__1;
x_2 = lean_expr_mk_app(x_1, x_0);
return x_2;
}
}
obj* initialize_init_lean_expr(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_util(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
 l_Lean_Compiler_neutralExpr = _init_l_Lean_Compiler_neutralExpr();
lean::mark_persistent(l_Lean_Compiler_neutralExpr);
 l_Lean_Compiler_unreachableExpr = _init_l_Lean_Compiler_unreachableExpr();
lean::mark_persistent(l_Lean_Compiler_unreachableExpr);
 l_Lean_Compiler_objectType = _init_l_Lean_Compiler_objectType();
lean::mark_persistent(l_Lean_Compiler_objectType);
 l_Lean_Compiler_voidType = _init_l_Lean_Compiler_voidType();
lean::mark_persistent(l_Lean_Compiler_voidType);
 l_Lean_Compiler_mkLcProof___closed__1 = _init_l_Lean_Compiler_mkLcProof___closed__1();
lean::mark_persistent(l_Lean_Compiler_mkLcProof___closed__1);
return w;
}
