// Lean compiler output
// Module: Init.Data.Char.Ordinal
// Imports: public import Init.Data.Fin.OverflowAware public import Init.Data.Function import Init.Data.Char.Lemmas import Init.Data.Char.Order import Init.Grind public import Init.Data.Char.Basic import Init.ByCases import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Linear import Init.Data.Nat.Simproc import Init.Data.Option.Lemmas import Init.Data.UInt.Lemmas
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
LEAN_EXPORT lean_object* l_Char_numSurrogates;
LEAN_EXPORT lean_object* l_Char_numCodePoints;
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_ordinal(uint32_t);
LEAN_EXPORT lean_object* l_Char_ordinal___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint32_t l_Char_ofOrdinal(lean_object*);
LEAN_EXPORT lean_object* l_Char_ofOrdinal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_succ_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l_Char_succ_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_succ_x3f___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_succ_x3f(uint32_t);
LEAN_EXPORT lean_object* l_Char_succ_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_succMany_x3f(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Char_succMany_x3f___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Char_numSurrogates(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2048u);
return x_1;
}
}
static lean_object* _init_l_Char_numCodePoints(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1112064u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Char_ordinal(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 55296;
x_3 = lean_uint32_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_uint32_to_nat(x_1);
x_5 = lean_unsigned_to_nat(2048u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_uint32_to_nat(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Char_ordinal___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_ordinal(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Char_ofOrdinal(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(55296u);
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; 
x_4 = lean_unsigned_to_nat(2048u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = lean_uint32_of_nat(x_5);
lean_dec(x_5);
return x_6;
}
else
{
uint32_t x_7; 
x_7 = lean_uint32_of_nat(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Char_ofOrdinal___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Char_ofOrdinal(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static lean_object* _init_l_Char_succ_x3f___closed__0___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 57344;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Char_succ_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_succ_x3f___closed__0___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Char_succ_x3f(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 55295;
x_3 = lean_uint32_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint32_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 1114111;
x_6 = lean_uint32_dec_lt(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint32_t x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = lean_uint32_add(x_1, x_8);
x_10 = lean_box_uint32(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_obj_once(&l_Char_succ_x3f___closed__0, &l_Char_succ_x3f___closed__0_once, _init_l_Char_succ_x3f___closed__0);
return x_12;
}
}
else
{
uint32_t x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 1;
x_14 = lean_uint32_add(x_1, x_13);
x_15 = lean_box_uint32(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Char_succ_x3f___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_succ_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Char_succMany_x3f(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1112064u);
x_4 = l_Char_ordinal(x_2);
x_5 = lean_nat_add(x_4, x_1);
lean_dec(x_4);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Char_ofOrdinal(x_5);
lean_dec(x_5);
x_9 = lean_box_uint32(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Char_succMany_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Char_succMany_x3f(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Data_Fin_OverflowAware(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Order(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Ordinal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_OverflowAware(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_numSurrogates = _init_l_Char_numSurrogates();
lean_mark_persistent(l_Char_numSurrogates);
l_Char_numCodePoints = _init_l_Char_numCodePoints();
lean_mark_persistent(l_Char_numCodePoints);
l_Char_succ_x3f___closed__0___boxed__const__1 = _init_l_Char_succ_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_Char_succ_x3f___closed__0___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
