// Lean compiler output
// Module: Lean.Compiler.BorrowedAnnotation
// Imports: public import Lean.Expr
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
static const lean_string_object l_Lean_markBorrowed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "borrowed"};
static const lean_object* l_Lean_markBorrowed___closed__0 = (const lean_object*)&l_Lean_markBorrowed___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_markBorrowed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_markBorrowed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 236, 131, 74, 166, 247, 60, 76)}};
static const lean_object* l_Lean_markBorrowed___closed__1 = (const lean_object*)&l_Lean_markBorrowed___closed__1_value;
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_markBorrowed(lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isMarkedBorrowed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isMarkedBorrowed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_markBorrowed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_markBorrowed___closed__1));
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isMarkedBorrowed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_markBorrowed___closed__1));
x_3 = l_Lean_annotation_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isMarkedBorrowed___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isMarkedBorrowed(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
