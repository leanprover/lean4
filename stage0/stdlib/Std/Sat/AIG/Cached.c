// Lean compiler output
// Module: Std.Sat.AIG.Cached
// Imports: Std.Sat.AIG.Basic Std.Sat.AIG.Lemmas
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_49____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t);
static lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_75_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_75_(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_49____boxed), 3, 2);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_1);
x_11 = l_instBEqOfDecidableEq___redArg(x_8);
lean_inc_ref(x_9);
lean_inc_ref(x_10);
lean_inc_ref(x_11);
x_12 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_11, x_10, x_7, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_get_size(x_6);
lean_inc(x_13);
lean_inc_ref(x_9);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_11, x_10, x_7, x_9, x_13);
x_15 = lean_array_push(x_6, x_9);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_15);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec_ref(x_12);
x_20 = 0;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_25, 0, x_2);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_4);
x_27 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_49____boxed), 3, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_1);
x_28 = l_instBEqOfDecidableEq___redArg(x_25);
lean_inc_ref(x_26);
lean_inc_ref(x_27);
lean_inc_ref(x_28);
x_29 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_28, x_27, x_24, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_array_get_size(x_23);
lean_inc(x_30);
lean_inc_ref(x_26);
x_31 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_28, x_27, x_24, x_26, x_30);
x_32 = lean_array_push(x_23, x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = 0;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec_ref(x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkAtomCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Sat_AIG_mkConstCached___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Std_Sat_AIG_mkConstCached(x_1, x_2, x_3, x_4, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_15 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_mul(x_11, x_16);
x_18 = l_Bool_toNat(x_12);
x_19 = lean_nat_lor(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_nat_mul(x_13, x_16);
x_21 = l_Bool_toNat(x_14);
x_22 = lean_nat_lor(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 1, x_22);
lean_ctor_set(x_4, 0, x_19);
x_23 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_49____boxed), 3, 2);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, x_1);
x_24 = l_instBEqOfDecidableEq___redArg(x_15);
lean_inc_ref(x_4);
lean_inc_ref(x_23);
lean_inc_ref(x_24);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_24, x_23, x_10, x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_29; uint8_t x_34; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_13);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_41 = l_Std_Sat_AIG_getConstant___redArg(x_3, x_7);
lean_dec_ref(x_7);
x_42 = l_Std_Sat_AIG_getConstant___redArg(x_3, x_8);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_8, 0);
lean_dec(x_44);
if (lean_obj_tag(x_41) == 0)
{
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_45; 
x_45 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_13);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_3);
lean_dec(x_11);
x_46 = lean_array_get_size(x_9);
lean_inc(x_46);
lean_inc_ref(x_4);
x_47 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_24, x_23, x_10, x_4, x_46);
x_48 = lean_array_push(x_9, x_4);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_8, 0, x_46);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_8);
return x_50;
}
else
{
lean_free_object(x_8);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_4);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
if (x_12 == 0)
{
if (x_14 == 0)
{
x_34 = x_45;
goto block_37;
}
else
{
lean_dec(x_11);
x_29 = x_12;
goto block_33;
}
}
else
{
x_34 = x_14;
goto block_37;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_4);
lean_dec(x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec_ref(x_42);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_free_object(x_8);
lean_dec(x_11);
goto block_40;
}
else
{
lean_object* x_53; 
lean_ctor_set(x_8, 0, x_11);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_12);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_8);
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_free_object(x_8);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_4);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec_ref(x_41);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_dec(x_42);
lean_dec(x_13);
goto block_40;
}
else
{
if (lean_obj_tag(x_42) == 0)
{
goto block_28;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
lean_dec_ref(x_42);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_dec(x_13);
goto block_40;
}
else
{
goto block_28;
}
}
}
}
}
else
{
lean_dec(x_8);
if (lean_obj_tag(x_41) == 0)
{
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_58; 
x_58 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_13);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_3);
lean_dec(x_11);
x_59 = lean_array_get_size(x_9);
lean_inc(x_59);
lean_inc_ref(x_4);
x_60 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_24, x_23, x_10, x_4, x_59);
x_61 = lean_array_push(x_9, x_4);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_58);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_4);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
if (x_12 == 0)
{
if (x_14 == 0)
{
x_34 = x_58;
goto block_37;
}
else
{
lean_dec(x_11);
x_29 = x_12;
goto block_33;
}
}
else
{
x_34 = x_14;
goto block_37;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_4);
lean_dec(x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
lean_dec_ref(x_42);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_dec(x_11);
goto block_40;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_11);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_12);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_4);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_69 = lean_ctor_get(x_41, 0);
lean_inc(x_69);
lean_dec_ref(x_41);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_dec(x_42);
lean_dec(x_13);
goto block_40;
}
else
{
if (lean_obj_tag(x_42) == 0)
{
goto block_28;
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_42, 0);
lean_inc(x_71);
lean_dec_ref(x_42);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_13);
goto block_40;
}
else
{
goto block_28;
}
}
}
}
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
block_33:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
block_37:
{
if (x_34 == 0)
{
lean_dec(x_11);
x_29 = x_34;
goto block_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_12);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_4);
lean_dec(x_11);
lean_dec_ref(x_7);
x_73 = !lean_is_exclusive(x_8);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_8, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_25, 0);
lean_inc(x_75);
lean_dec_ref(x_25);
x_76 = 0;
lean_ctor_set(x_8, 0, x_75);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_3);
lean_ctor_set(x_77, 1, x_8);
return x_77;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
x_78 = lean_ctor_get(x_25, 0);
lean_inc(x_78);
lean_dec_ref(x_25);
x_79 = 0;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_3);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_82 = lean_ctor_get(x_4, 0);
x_83 = lean_ctor_get(x_4, 1);
x_84 = lean_ctor_get(x_3, 0);
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_3);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_82, sizeof(void*)*1);
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
x_90 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_90, 0, x_2);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_mul(x_86, x_91);
x_93 = l_Bool_toNat(x_87);
x_94 = lean_nat_lor(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
x_95 = lean_nat_mul(x_88, x_91);
x_96 = l_Bool_toNat(x_89);
x_97 = lean_nat_lor(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 1, x_97);
lean_ctor_set(x_4, 0, x_94);
x_98 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_49____boxed), 3, 2);
lean_closure_set(x_98, 0, lean_box(0));
lean_closure_set(x_98, 1, x_1);
x_99 = l_instBEqOfDecidableEq___redArg(x_90);
lean_inc_ref(x_4);
lean_inc_ref(x_98);
lean_inc_ref(x_99);
x_100 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_99, x_98, x_85, x_4);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_105; uint8_t x_110; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_inc(x_88);
lean_inc_ref(x_85);
lean_inc_ref(x_84);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_84);
lean_ctor_set(x_101, 1, x_85);
x_117 = l_Std_Sat_AIG_getConstant___redArg(x_101, x_82);
lean_dec_ref(x_82);
x_118 = l_Std_Sat_AIG_getConstant___redArg(x_101, x_83);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_119 = x_83;
} else {
 lean_dec_ref(x_83);
 x_119 = lean_box(0);
}
if (lean_obj_tag(x_117) == 0)
{
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_120; 
x_120 = lean_nat_dec_eq(x_86, x_88);
lean_dec(x_88);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_101);
lean_dec(x_86);
x_121 = lean_array_get_size(x_84);
lean_inc(x_121);
lean_inc_ref(x_4);
x_122 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_99, x_98, x_85, x_4, x_121);
x_123 = lean_array_push(x_84, x_4);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
if (lean_is_scalar(x_119)) {
 x_125 = lean_alloc_ctor(0, 1, 1);
} else {
 x_125 = x_119;
}
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_120);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
else
{
lean_dec(x_119);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_4);
lean_dec_ref(x_85);
lean_dec_ref(x_84);
if (x_87 == 0)
{
if (x_89 == 0)
{
x_110 = x_120;
goto block_113;
}
else
{
lean_dec(x_86);
x_105 = x_87;
goto block_109;
}
}
else
{
x_110 = x_89;
goto block_113;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; 
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_4);
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec_ref(x_84);
x_127 = lean_ctor_get(x_118, 0);
lean_inc(x_127);
lean_dec_ref(x_118);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_dec(x_119);
lean_dec(x_86);
goto block_116;
}
else
{
lean_object* x_129; lean_object* x_130; 
if (lean_is_scalar(x_119)) {
 x_129 = lean_alloc_ctor(0, 1, 1);
} else {
 x_129 = x_119;
}
lean_ctor_set(x_129, 0, x_86);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_87);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_101);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; uint8_t x_132; 
lean_dec(x_119);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_4);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_84);
x_131 = lean_ctor_get(x_117, 0);
lean_inc(x_131);
lean_dec_ref(x_117);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_dec(x_118);
lean_dec(x_88);
goto block_116;
}
else
{
if (lean_obj_tag(x_118) == 0)
{
goto block_104;
}
else
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_118, 0);
lean_inc(x_133);
lean_dec_ref(x_118);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_dec(x_88);
goto block_116;
}
else
{
goto block_104;
}
}
}
}
block_104:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_88);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_89);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
block_109:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
block_113:
{
if (x_110 == 0)
{
lean_dec(x_86);
x_105 = x_110;
goto block_109;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_86);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_87);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
block_116:
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_101);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_4);
lean_dec(x_86);
lean_dec_ref(x_82);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_135 = x_83;
} else {
 lean_dec_ref(x_83);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_100, 0);
lean_inc(x_136);
lean_dec_ref(x_100);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_84);
lean_ctor_set(x_137, 1, x_85);
x_138 = 0;
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 1, 1);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_141 = lean_ctor_get(x_4, 0);
x_142 = lean_ctor_get(x_4, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_4);
x_143 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_144);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_145 = x_3;
} else {
 lean_dec_ref(x_3);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
x_148 = lean_ctor_get(x_142, 0);
x_149 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
x_150 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_150, 0, x_2);
x_151 = lean_unsigned_to_nat(2u);
x_152 = lean_nat_mul(x_146, x_151);
x_153 = l_Bool_toNat(x_147);
x_154 = lean_nat_lor(x_152, x_153);
lean_dec(x_153);
lean_dec(x_152);
x_155 = lean_nat_mul(x_148, x_151);
x_156 = l_Bool_toNat(x_149);
x_157 = lean_nat_lor(x_155, x_156);
lean_dec(x_156);
lean_dec(x_155);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic_1021782049____hygCtx___hyg_49____boxed), 3, 2);
lean_closure_set(x_159, 0, lean_box(0));
lean_closure_set(x_159, 1, x_1);
x_160 = l_instBEqOfDecidableEq___redArg(x_150);
lean_inc_ref(x_158);
lean_inc_ref(x_159);
lean_inc_ref(x_160);
x_161 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_160, x_159, x_144, x_158);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_166; uint8_t x_171; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_inc(x_148);
lean_inc_ref(x_144);
lean_inc_ref(x_143);
if (lean_is_scalar(x_145)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_145;
}
lean_ctor_set(x_162, 0, x_143);
lean_ctor_set(x_162, 1, x_144);
x_178 = l_Std_Sat_AIG_getConstant___redArg(x_162, x_141);
lean_dec_ref(x_141);
x_179 = l_Std_Sat_AIG_getConstant___redArg(x_162, x_142);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_180 = x_142;
} else {
 lean_dec_ref(x_142);
 x_180 = lean_box(0);
}
if (lean_obj_tag(x_178) == 0)
{
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_181; 
x_181 = lean_nat_dec_eq(x_146, x_148);
lean_dec(x_148);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec_ref(x_162);
lean_dec(x_146);
x_182 = lean_array_get_size(x_143);
lean_inc(x_182);
lean_inc_ref(x_158);
x_183 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_160, x_159, x_144, x_158, x_182);
x_184 = lean_array_push(x_143, x_158);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
if (lean_is_scalar(x_180)) {
 x_186 = lean_alloc_ctor(0, 1, 1);
} else {
 x_186 = x_180;
}
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_181);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
else
{
lean_dec(x_180);
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_144);
lean_dec_ref(x_143);
if (x_147 == 0)
{
if (x_149 == 0)
{
x_171 = x_181;
goto block_174;
}
else
{
lean_dec(x_146);
x_166 = x_147;
goto block_170;
}
}
else
{
x_171 = x_149;
goto block_174;
}
}
}
else
{
lean_object* x_188; uint8_t x_189; 
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec(x_148);
lean_dec_ref(x_144);
lean_dec_ref(x_143);
x_188 = lean_ctor_get(x_179, 0);
lean_inc(x_188);
lean_dec_ref(x_179);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_dec(x_180);
lean_dec(x_146);
goto block_177;
}
else
{
lean_object* x_190; lean_object* x_191; 
if (lean_is_scalar(x_180)) {
 x_190 = lean_alloc_ctor(0, 1, 1);
} else {
 x_190 = x_180;
}
lean_ctor_set(x_190, 0, x_146);
lean_ctor_set_uint8(x_190, sizeof(void*)*1, x_147);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_162);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; uint8_t x_193; 
lean_dec(x_180);
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec(x_146);
lean_dec_ref(x_144);
lean_dec_ref(x_143);
x_192 = lean_ctor_get(x_178, 0);
lean_inc(x_192);
lean_dec_ref(x_178);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_dec(x_179);
lean_dec(x_148);
goto block_177;
}
else
{
if (lean_obj_tag(x_179) == 0)
{
goto block_165;
}
else
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_179, 0);
lean_inc(x_194);
lean_dec_ref(x_179);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_dec(x_148);
goto block_177;
}
else
{
goto block_165;
}
}
}
}
block_165:
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_148);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_149);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
block_170:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_162);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
block_174:
{
if (x_171 == 0)
{
lean_dec(x_146);
x_166 = x_171;
goto block_170;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_172, 0, x_146);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_147);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_162);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_158);
lean_dec(x_146);
lean_dec_ref(x_141);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_196 = x_142;
} else {
 lean_dec_ref(x_142);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_161, 0);
lean_inc(x_197);
lean_dec_ref(x_161);
if (lean_is_scalar(x_145)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_145;
}
lean_ctor_set(x_198, 0, x_143);
lean_ctor_set(x_198, 1, x_144);
x_199 = 0;
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 1, 1);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set(x_4, 1, x_6);
lean_ctor_set(x_4, 0, x_7);
x_11 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_13);
x_19 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
x_21 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0 = _init_l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0();
lean_mark_persistent(l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
