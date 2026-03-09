// Lean compiler output
// Module: Std.Sat.AIG.If
// Imports: public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_64; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
lean_inc_ref(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_64 = !lean_is_exclusive(x_9);
if (x_64 == 0)
{
x_12 = x_9;
x_13 = x_64;
goto block_63;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_62; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_62 = !lean_is_exclusive(x_5);
if (x_62 == 0)
{
x_16 = x_5;
x_17 = x_62;
goto block_61;
}
else
{
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_60; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_60 = !lean_is_exclusive(x_7);
if (x_60 == 0)
{
x_20 = x_7;
x_21 = x_60;
goto block_59;
}
else
{
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_box(0);
x_21 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_22; lean_object* x_23; 
if (x_15 == 0)
{
uint8_t x_51; lean_object* x_52; 
x_51 = 1;
if (x_17 == 0)
{
x_52 = x_16;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_14);
x_52 = x_54;
goto block_53;
}
block_53:
{
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_22 = x_10;
x_23 = x_52;
goto block_50;
}
}
else
{
uint8_t x_55; lean_object* x_56; 
x_55 = 0;
if (x_17 == 0)
{
x_56 = x_16;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_14);
x_56 = x_58;
goto block_57;
}
block_57:
{
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_22 = x_10;
x_23 = x_56;
goto block_50;
}
}
block_50:
{
lean_object* x_24; 
if (x_21 == 0)
{
x_24 = x_20;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_19);
x_24 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_25; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_23);
x_25 = x_12;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_24);
x_25 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_45; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_26 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_22, x_25);
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_ctor_get(x_26, 1);
x_45 = !lean_is_exclusive(x_26);
if (x_45 == 0)
{
x_29 = x_26;
x_30 = x_45;
goto block_44;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
x_33 = x_11;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_32);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_35);
x_36 = x_29;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_28);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_27, x_36);
return x_37;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkIfCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_36; lean_object* x_37; 
x_36 = lean_nat_dec_lt(x_5, x_3);
if (x_36 == 0)
{
lean_object* x_48; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_9);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_array_fget_borrowed(x_7, x_5);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_shiftr(x_49, x_50);
x_52 = lean_nat_land(x_50, x_49);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_36);
x_37 = x_55;
goto block_47;
}
else
{
uint8_t x_56; lean_object* x_57; 
x_56 = 0;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_37 = x_57;
goto block_47;
}
}
block_35:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_34; 
lean_inc_ref(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l_Std_Sat_AIG_mkIfCached___redArg(x_1, x_2, x_4, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec_ref(x_6);
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
x_20 = x_14;
x_21 = x_34;
goto block_33;
}
else
{
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_16);
x_22 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_16);
x_22 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_17);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_mul(x_18, x_25);
lean_dec(x_18);
x_27 = l_Bool_toNat(x_19);
x_28 = lean_nat_lor(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = lean_array_push(x_9, x_28);
x_4 = x_15;
x_5 = x_24;
x_6 = x_22;
x_9 = x_29;
goto _start;
}
}
}
block_47:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_array_fget_borrowed(x_8, x_5);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_shiftr(x_38, x_39);
x_41 = lean_nat_land(x_39, x_38);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_36);
x_10 = x_37;
x_11 = x_44;
goto block_35;
}
else
{
uint8_t x_45; lean_object* x_46; 
x_45 = 0;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_10 = x_37;
x_11 = x_46;
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Sat_AIG_RefVec_ite_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_RefVec_ite_go___redArg(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_RefVec_ite_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_3);
x_11 = l_Std_Sat_AIG_RefVec_ite_go___redArg(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8, x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_RefVec_ite___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_RefVec_ite(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_If(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_If(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_If(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_If(builtin);
}
#ifdef __cplusplus
}
#endif
