// Lean compiler output
// Module: Std.Sat.AIG.Cached
// Imports: public import Std.Sat.AIG.Lemmas import Init.Omega
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
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0_value;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(x_1, x_2, x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_31; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
x_7 = x_3;
x_8 = x_31;
goto block_30;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_1);
x_12 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc_ref(x_10);
lean_inc_ref(x_11);
lean_inc_ref(x_12);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_12, x_11, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_get_size(x_5);
lean_inc_ref(x_10);
x_15 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_12, x_11, x_6, x_10, x_14);
x_16 = lean_array_push(x_5, x_10);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_16);
x_17 = x_7;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_15);
x_17 = x_22;
goto block_21;
}
block_21:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec_ref(x_13);
if (x_8 == 0)
{
x_24 = x_7;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_6);
x_24 = x_29;
goto block_28;
}
block_28:
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Sat_AIG_mkConstCached___redArg(x_2);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_92; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_92 = !lean_is_exclusive(x_4);
if (x_92 == 0)
{
x_7 = x_4;
x_8 = x_92;
goto block_91;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_90; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_90 = !lean_is_exclusive(x_3);
if (x_90 == 0)
{
x_11 = x_3;
x_12 = x_90;
goto block_89;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_17 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_mul(x_13, x_18);
x_20 = l_Bool_toNat(x_14);
x_21 = lean_nat_lor(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_nat_mul(x_15, x_18);
x_23 = l_Bool_toNat(x_16);
x_24 = lean_nat_lor(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_24);
lean_ctor_set(x_7, 0, x_21);
x_25 = x_7;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_21);
lean_ctor_set(x_88, 1, x_24);
x_25 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, x_1);
x_27 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_27, 0, x_17);
lean_inc_ref(x_25);
lean_inc_ref(x_26);
lean_inc_ref(x_27);
x_28 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_27, x_26, x_10, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_inc(x_15);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
if (x_12 == 0)
{
x_29 = x_11;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_9);
lean_ctor_set(x_72, 1, x_10);
x_29 = x_72;
goto block_71;
}
block_71:
{
uint8_t x_30; uint8_t x_35; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_69; 
x_45 = l_Std_Sat_AIG_getConstant___redArg(x_29, x_5);
lean_dec_ref(x_5);
x_46 = l_Std_Sat_AIG_getConstant___redArg(x_29, x_6);
x_69 = !lean_is_exclusive(x_6);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_6, 0);
lean_dec(x_70);
x_47 = x_6;
x_48 = x_69;
goto block_68;
}
else
{
lean_dec(x_6);
x_47 = lean_box(0);
x_48 = x_69;
goto block_68;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
block_38:
{
if (x_35 == 0)
{
lean_dec(x_13);
x_30 = x_35;
goto block_34;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_14);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_16);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
block_44:
{
lean_object* x_42; lean_object* x_43; 
x_42 = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0));
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
block_68:
{
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_49; uint8_t x_50; 
lean_del_object(x_47);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec_ref(x_45);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_46);
lean_dec(x_15);
goto block_44;
}
else
{
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec_ref(x_46);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_dec(x_15);
goto block_44;
}
else
{
goto block_41;
}
}
else
{
lean_dec(x_46);
goto block_41;
}
}
}
else
{
lean_dec(x_45);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_53; uint8_t x_54; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_15);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec_ref(x_46);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_del_object(x_47);
lean_dec(x_13);
goto block_44;
}
else
{
lean_object* x_55; 
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_13);
x_55 = x_47;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_13);
x_55 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_56; 
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_14);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_29);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_46);
x_59 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_15);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_29);
lean_dec(x_13);
x_60 = lean_array_get_size(x_9);
lean_inc_ref(x_25);
x_61 = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(x_27, x_26, x_10, x_25, x_60);
x_62 = lean_array_push(x_9, x_25);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_60);
x_64 = x_47;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_60);
x_64 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_65; 
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_del_object(x_47);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
if (x_14 == 0)
{
if (x_16 == 0)
{
x_35 = x_59;
goto block_38;
}
else
{
lean_dec(x_13);
x_30 = x_14;
goto block_34;
}
}
else
{
x_35 = x_16;
goto block_38;
}
}
}
}
}
}
}
else
{
lean_object* x_73; uint8_t x_74; uint8_t x_85; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_13);
lean_dec_ref(x_5);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_6, 0);
lean_dec(x_86);
x_73 = x_6;
x_74 = x_85;
goto block_84;
}
else
{
lean_dec(x_6);
x_73 = lean_box(0);
x_74 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_28, 0);
lean_inc(x_75);
lean_dec_ref(x_28);
if (x_12 == 0)
{
x_76 = x_11;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_9);
lean_ctor_set(x_83, 1, x_10);
x_76 = x_83;
goto block_82;
}
block_82:
{
uint8_t x_77; lean_object* x_78; 
x_77 = 0;
if (x_74 == 0)
{
lean_ctor_set(x_73, 0, x_75);
x_78 = x_73;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_75);
x_78 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_79; 
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_21; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
x_7 = x_4;
x_8 = x_21;
goto block_20;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_6);
x_12 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_5);
x_12 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_12);
return x_13;
}
}
else
{
lean_object* x_16; 
if (x_8 == 0)
{
x_16 = x_7;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_16);
return x_17;
}
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
lean_object* runtime_initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_Cached(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin)
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
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_Cached(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_Cached(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_Cached(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_Cached(builtin);
}
#ifdef __cplusplus
}
#endif
