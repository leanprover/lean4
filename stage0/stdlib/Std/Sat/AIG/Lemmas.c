// Lean compiler output
// Module: Std.Sat.AIG.Lemmas
// Imports: Std.Sat.AIG.Basic Std.Sat.AIG.LawfulOperator
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_2, x_6, lean_box(0));
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
lean_dec(x_1);
x_14 = lean_box(x_12);
x_15 = lean_box(x_13);
x_16 = lean_apply_5(x_4, x_10, x_11, x_14, x_15, lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_2(x_3, x_1, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
