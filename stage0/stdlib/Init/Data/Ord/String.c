// Lean compiler output
// Module: Init.Data.Ord.String
// Imports: public import Init.Data.Order.Ord public import Init.Data.String.Lemmas
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
LEAN_EXPORT uint8_t l_String_instOrd___lam__0(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instOrd;
LEAN_EXPORT lean_object* l_String_instOrd___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_String_instOrd___closed__0;
LEAN_EXPORT uint8_t l_String_instOrd___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_String_instOrd___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instOrd___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_String_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_instOrd___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_String_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instOrd___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instOrd___closed__0 = _init_l_String_instOrd___closed__0();
lean_mark_persistent(l_String_instOrd___closed__0);
l_String_instOrd = _init_l_String_instOrd();
lean_mark_persistent(l_String_instOrd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
