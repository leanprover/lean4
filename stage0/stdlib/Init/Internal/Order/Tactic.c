// Lean compiler output
// Module: Init.Internal.Order.Tactic
// Imports: Init.Notation
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Order_monotonicity;
static lean_object* l_Lean_Order_monotonicity___closed__5;
static lean_object* l_Lean_Order_monotonicity___closed__0;
static lean_object* l_Lean_Order_monotonicity___closed__3;
static lean_object* l_Lean_Order_monotonicity___closed__1;
static lean_object* l_Lean_Order_monotonicity___closed__2;
static lean_object* l_Lean_Order_monotonicity___closed__4;
static lean_object* _init_l_Lean_Order_monotonicity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Order_monotonicity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Order", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Order_monotonicity___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("monotonicity", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Order_monotonicity___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Order_monotonicity___closed__2;
x_2 = l_Lean_Order_monotonicity___closed__1;
x_3 = l_Lean_Order_monotonicity___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Order_monotonicity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Order_monotonicity___closed__2;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lean_Order_monotonicity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Order_monotonicity___closed__4;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Order_monotonicity___closed__3;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Order_monotonicity() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Order_monotonicity___closed__5;
return x_1;
}
}
lean_object* initialize_Init_Notation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Internal_Order_Tactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Order_monotonicity___closed__0 = _init_l_Lean_Order_monotonicity___closed__0();
lean_mark_persistent(l_Lean_Order_monotonicity___closed__0);
l_Lean_Order_monotonicity___closed__1 = _init_l_Lean_Order_monotonicity___closed__1();
lean_mark_persistent(l_Lean_Order_monotonicity___closed__1);
l_Lean_Order_monotonicity___closed__2 = _init_l_Lean_Order_monotonicity___closed__2();
lean_mark_persistent(l_Lean_Order_monotonicity___closed__2);
l_Lean_Order_monotonicity___closed__3 = _init_l_Lean_Order_monotonicity___closed__3();
lean_mark_persistent(l_Lean_Order_monotonicity___closed__3);
l_Lean_Order_monotonicity___closed__4 = _init_l_Lean_Order_monotonicity___closed__4();
lean_mark_persistent(l_Lean_Order_monotonicity___closed__4);
l_Lean_Order_monotonicity___closed__5 = _init_l_Lean_Order_monotonicity___closed__5();
lean_mark_persistent(l_Lean_Order_monotonicity___closed__5);
l_Lean_Order_monotonicity = _init_l_Lean_Order_monotonicity();
lean_mark_persistent(l_Lean_Order_monotonicity);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
