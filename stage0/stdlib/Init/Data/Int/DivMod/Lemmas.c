// Lean compiler output
// Module: Init.Data.Int.DivMod.Lemmas
// Imports: Init.Data.Int.DivMod.Bootstrap Init.Data.Nat.Lemmas Init.Data.Nat.Div.Lemmas Init.Data.Int.Order Init.Data.Int.Lemmas Init.Data.Nat.Dvd Init.RCases
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
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_decidableDvd___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_decidableDvd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_int_emod(x_2, x_1);
x_4 = l_Int_decidableDvd___closed__1;
x_5 = lean_int_dec_eq(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_decidableDvd(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int_decidableDvd___closed__1;
x_6 = lean_int_dec_lt(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_nat_abs(x_1);
x_8 = lean_apply_2(x_3, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_9 = lean_nat_abs(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = lean_apply_2(x_4, x_11, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Int_decidableDvd___closed__1;
x_8 = lean_int_dec_lt(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_nat_abs(x_1);
x_10 = lean_int_dec_lt(x_2, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_nat_abs(x_2);
x_12 = lean_apply_2(x_3, x_9, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = lean_nat_abs(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_apply_2(x_4, x_9, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_nat_abs(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_int_dec_lt(x_2, x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_nat_abs(x_2);
x_22 = lean_apply_2(x_5, x_19, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_23 = lean_nat_abs(x_2);
x_24 = lean_nat_sub(x_23, x_18);
lean_dec(x_23);
x_25 = lean_apply_2(x_6, x_19, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Int_decidableDvd___closed__1;
x_10 = lean_int_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_nat_abs(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
x_16 = lean_int_dec_lt(x_2, x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_5);
x_17 = lean_nat_abs(x_2);
lean_dec(x_2);
x_18 = lean_apply_3(x_4, x_11, x_17, lean_box(0));
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_4);
x_19 = lean_nat_abs(x_2);
lean_dec(x_2);
x_20 = lean_nat_sub(x_19, x_14);
lean_dec(x_19);
x_21 = lean_apply_2(x_5, x_15, x_20);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_nat_abs(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = lean_int_dec_lt(x_2, x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_8);
x_27 = lean_nat_abs(x_2);
lean_dec(x_2);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_30 = lean_nat_sub(x_27, x_24);
lean_dec(x_27);
x_31 = lean_apply_2(x_7, x_25, x_30);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_7);
x_32 = lean_apply_1(x_6, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
lean_dec(x_6);
x_33 = lean_nat_abs(x_2);
lean_dec(x_2);
x_34 = lean_nat_sub(x_33, x_24);
lean_dec(x_33);
x_35 = lean_apply_2(x_8, x_25, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Int_decidableDvd___closed__1;
x_9 = lean_int_dec_lt(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_nat_abs(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
x_15 = lean_int_dec_lt(x_2, x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_5);
x_16 = lean_nat_abs(x_2);
lean_dec(x_2);
x_17 = lean_apply_3(x_4, x_10, x_16, lean_box(0));
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_4);
x_18 = lean_nat_abs(x_2);
lean_dec(x_2);
x_19 = lean_nat_sub(x_18, x_13);
lean_dec(x_18);
x_20 = lean_apply_2(x_5, x_14, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_apply_1(x_3, x_2);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_nat_abs(x_1);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
lean_dec(x_22);
x_25 = lean_int_dec_lt(x_2, x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_26 = lean_nat_abs(x_2);
lean_dec(x_2);
x_27 = lean_apply_2(x_6, x_24, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
x_28 = lean_nat_abs(x_2);
lean_dec(x_2);
x_29 = lean_nat_sub(x_28, x_23);
lean_dec(x_28);
x_30 = lean_apply_2(x_7, x_24, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin, lean_object*);
lean_object* initialize_Init_RCases(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_decidableDvd___closed__1 = _init_l_Int_decidableDvd___closed__1();
lean_mark_persistent(l_Int_decidableDvd___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
