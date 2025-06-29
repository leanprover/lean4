// Lean compiler output
// Module: Lean.Compiler.BorrowedAnnotation
// Imports: Lean.Expr
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lean_markBorrowed___closed__1;
LEAN_EXPORT uint8_t lean_is_marked_borrowed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_markBorrowed(lean_object*);
static lean_object* l_Lean_markBorrowed___closed__0;
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isMarkedBorrowed___boxed(lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* _init_l_Lean_markBorrowed___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("borrowed", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_markBorrowed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_markBorrowed___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_markBorrowed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_markBorrowed___closed__1;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_is_marked_borrowed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_markBorrowed___closed__1;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isMarkedBorrowed___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_marked_borrowed(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_markBorrowed___closed__0 = _init_l_Lean_markBorrowed___closed__0();
lean_mark_persistent(l_Lean_markBorrowed___closed__0);
l_Lean_markBorrowed___closed__1 = _init_l_Lean_markBorrowed___closed__1();
lean_mark_persistent(l_Lean_markBorrowed___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
