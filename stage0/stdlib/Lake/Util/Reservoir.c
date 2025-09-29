// Lean compiler output
// Module: Lake.Util.Reservoir
// Imports: Init.Prelude Init.Data.Array.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__0;
LEAN_EXPORT lean_object* l_Lake_Reservoir_lakeHeaders;
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__1;
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__3;
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__2;
static lean_object* l_Lake_Reservoir_lakeHeaders___closed__4;
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("X-Reservoir-Api-Version:1.0.0", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("X-Lake-Registry-Api-Version:0.1.0", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__0;
x_2 = l_Lake_Reservoir_lakeHeaders___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__1;
x_2 = l_Lake_Reservoir_lakeHeaders___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Reservoir_lakeHeaders() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Reservoir_lakeHeaders___closed__4;
return x_1;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Reservoir_lakeHeaders___closed__0 = _init_l_Lake_Reservoir_lakeHeaders___closed__0();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__0);
l_Lake_Reservoir_lakeHeaders___closed__1 = _init_l_Lake_Reservoir_lakeHeaders___closed__1();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__1);
l_Lake_Reservoir_lakeHeaders___closed__2 = _init_l_Lake_Reservoir_lakeHeaders___closed__2();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__2);
l_Lake_Reservoir_lakeHeaders___closed__3 = _init_l_Lake_Reservoir_lakeHeaders___closed__3();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__3);
l_Lake_Reservoir_lakeHeaders___closed__4 = _init_l_Lake_Reservoir_lakeHeaders___closed__4();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders___closed__4);
l_Lake_Reservoir_lakeHeaders = _init_l_Lake_Reservoir_lakeHeaders();
lean_mark_persistent(l_Lake_Reservoir_lakeHeaders);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
