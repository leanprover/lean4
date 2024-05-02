// Lean compiler output
// Module: Lake.Util.Newline
// Imports: Init
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_crlf2lf___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_crlf2lf_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_crlf2lf(lean_object*);
static lean_object* l_Lake_crlf2lf___closed__1;
LEAN_EXPORT lean_object* l_Lake_crlf2lf_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_crlf2lf_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get_fast(x_1, x_4);
x_7 = lean_string_utf8_next_fast(x_1, x_4);
x_8 = 13;
x_9 = lean_uint32_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_1, x_7);
x_12 = 10;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_string_append(x_2, x_15);
lean_dec(x_15);
x_17 = lean_string_utf8_next(x_1, x_7);
x_2 = x_16;
x_3 = x_7;
x_4 = x_17;
goto _start;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_string_append(x_2, x_21);
lean_dec(x_21);
return x_22;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_crlf2lf_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_crlf2lf_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_crlf2lf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_crlf2lf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_crlf2lf___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lake_crlf2lf_go(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_crlf2lf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_crlf2lf(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Newline(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_crlf2lf___closed__1 = _init_l_Lake_crlf2lf___closed__1();
lean_mark_persistent(l_Lake_crlf2lf___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
