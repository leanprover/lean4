// Lean compiler output
// Module: Init.Data.String.Stream
// Imports: public import Init.Data.String.Basic public import Init.Data.Stream
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
LEAN_EXPORT lean_object* l_instStreamRawChar;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instStreamRawChar___lam__0(lean_object*);
static lean_object* l_instStreamRawChar___closed__0;
LEAN_EXPORT lean_object* l_instStreamRawChar___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_string_utf8_get(x_3, x_4);
x_9 = lean_string_utf8_next(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_9);
x_10 = lean_box_uint32(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
x_17 = lean_box(0);
return x_17;
}
else
{
uint32_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_string_utf8_get(x_13, x_14);
x_19 = lean_string_utf8_next(x_13, x_14);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_15);
x_21 = lean_box_uint32(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_instStreamRawChar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instStreamRawChar___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instStreamRawChar() {
_start:
{
lean_object* x_1; 
x_1 = l_instStreamRawChar___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Stream(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instStreamRawChar___closed__0 = _init_l_instStreamRawChar___closed__0();
lean_mark_persistent(l_instStreamRawChar___closed__0);
l_instStreamRawChar = _init_l_instStreamRawChar();
lean_mark_persistent(l_instStreamRawChar);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
