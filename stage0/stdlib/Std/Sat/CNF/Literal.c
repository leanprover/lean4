// Lean compiler output
// Module: Std.Sat.CNF.Literal
// Imports: Init.Data.Hashable Init.Data.ToString
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
static lean_object* l_Std_Sat_Literal_dimacs___rarg___closed__1;
static lean_object* l_Std_Sat_Literal_dimacs___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate___rarg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_unbox(x_2);
lean_dec(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = 1;
x_7 = lean_box(x_6);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_1, 1, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_Literal_negate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_Literal_negate___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_Literal_dimacs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_Literal_dimacs___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
x_7 = l_Std_Sat_Literal_dimacs___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Std_Sat_Literal_dimacs___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_1(x_1, x_11);
x_13 = l_Std_Sat_Literal_dimacs___rarg___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_Literal_dimacs___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Literal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_Literal_dimacs___rarg___closed__1 = _init_l_Std_Sat_Literal_dimacs___rarg___closed__1();
lean_mark_persistent(l_Std_Sat_Literal_dimacs___rarg___closed__1);
l_Std_Sat_Literal_dimacs___rarg___closed__2 = _init_l_Std_Sat_Literal_dimacs___rarg___closed__2();
lean_mark_persistent(l_Std_Sat_Literal_dimacs___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
