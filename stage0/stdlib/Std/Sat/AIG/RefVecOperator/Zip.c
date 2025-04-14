// Lean compiler output
// Module: Std.Sat.AIG.RefVecOperator.Zip
// Imports: Std.Sat.AIG.RefVec Std.Sat.AIG.LawfulVecOperator
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_5, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
x_52 = lean_array_fget(x_8, x_5);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_div(x_52, x_53);
x_55 = lean_nat_land(x_15, x_52);
lean_dec(x_52);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
uint8_t x_58; lean_object* x_59; 
x_58 = 1;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_17 = x_59;
x_18 = x_9;
goto block_51;
}
else
{
uint8_t x_60; lean_object* x_61; 
x_60 = 0;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_17 = x_61;
x_18 = x_9;
goto block_51;
}
block_51:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_array_fget(x_18, x_5);
lean_dec(x_5);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_div(x_19, x_20);
x_22 = lean_nat_land(x_15, x_19);
lean_dec(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = 1;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_10);
x_28 = lean_apply_2(x_10, x_4, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
x_33 = lean_nat_mul(x_31, x_20);
lean_dec(x_31);
x_34 = l_Bool_toNat(x_32);
x_35 = lean_nat_lor(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
x_36 = lean_array_push(x_6, x_35);
x_4 = x_29;
x_5 = x_16;
x_6 = x_36;
x_7 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_box(0);
goto _start;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = 0;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_10);
x_41 = lean_apply_2(x_10, x_4, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
lean_dec(x_43);
x_46 = lean_nat_mul(x_44, x_20);
lean_dec(x_44);
x_47 = l_Bool_toNat(x_45);
x_48 = lean_nat_lor(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
x_49 = lean_array_push(x_6, x_48);
x_4 = x_42;
x_5 = x_16;
x_6 = x_49;
x_7 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_box(0);
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_RefVec_zip_go___rarg___boxed), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Sat_AIG_RefVec_zip_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_empty_array_with_capacity(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_Sat_AIG_RefVec_zip_go___rarg(x_1, x_2, x_3, x_4, x_11, x_6, lean_box(0), x_8, x_9, x_10, lean_box(0), lean_box(0));
lean_dec(x_9);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_RefVec_zip___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_zip___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_RefVec_zip___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Std_Sat_AIG_RefVec(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_RefVecOperator_Zip(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_RefVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
