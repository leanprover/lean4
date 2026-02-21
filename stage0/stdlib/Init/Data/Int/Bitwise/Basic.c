// Lean compiler output
// Module: Init.Data.Int.Bitwise.Basic
// Imports: public import Init.Data.Int.Basic public import Init.Data.Nat.Bitwise.Basic
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Int_not___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_not___closed__0;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_not(lean_object*);
LEAN_EXPORT lean_object* l_Int_not___boxed(lean_object*);
static const lean_closure_object l_Int_instComplement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_not___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instComplement___closed__0 = (const lean_object*)&l_Int_instComplement___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instComplement = (const lean_object*)&l_Int_instComplement___closed__0_value;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_shiftRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instHShiftRightNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instHShiftRightNat___closed__0 = (const lean_object*)&l_Int_instHShiftRightNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instHShiftRightNat = (const lean_object*)&l_Int_instHShiftRightNat___closed__0_value;
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_shiftLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_shiftLeft___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instHShiftLeftNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instHShiftLeftNat___closed__0 = (const lean_object*)&l_Int_instHShiftLeftNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instHShiftLeftNat = (const lean_object*)&l_Int_instHShiftLeftNat___closed__0_value;
static lean_object* _init_l_Int_not___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_not(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&l_Int_not___closed__0, &l_Int_not___closed__0_once, _init_l_Int_not___closed__0);
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = lean_int_neg_succ_of_nat(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_to_int(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Int_not___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_not(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_shiftRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_obj_once(&l_Int_not___closed__0, &l_Int_not___closed__0_once, _init_l_Int_not___closed__0);
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_nat_shiftr(x_5, x_2);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_nat_shiftr(x_10, x_2);
lean_dec(x_10);
x_12 = lean_int_neg_succ_of_nat(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Int_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_shiftRight(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_shiftLeft(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_obj_once(&l_Int_not___closed__0, &l_Int_not___closed__0_once, _init_l_Int_not___closed__0);
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_nat_shiftl(x_5, x_2);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_nat_add(x_10, x_9);
lean_dec(x_10);
x_12 = lean_nat_shiftl(x_11, x_2);
lean_dec(x_11);
x_13 = lean_nat_sub(x_12, x_9);
lean_dec(x_12);
x_14 = lean_int_neg_succ_of_nat(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Int_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_shiftLeft(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
