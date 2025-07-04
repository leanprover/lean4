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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
uint8_t l_Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_807_(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t);
static lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_807_(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_array_get_size(x_9);
lean_inc(x_12);
lean_inc(x_1);
x_14 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_12);
x_15 = 32;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = 16;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = 1;
x_24 = lean_usize_sub(x_22, x_23);
x_25 = lean_usize_land(x_21, x_24);
x_26 = lean_array_uget(x_9, x_25);
lean_inc(x_26);
lean_inc(x_12);
lean_inc(x_11);
x_27 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_11, x_12, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_40; 
x_29 = lean_ctor_get(x_5, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 0);
lean_dec(x_30);
x_31 = lean_array_get_size(x_6);
lean_inc(x_26);
lean_inc(x_12);
lean_inc(x_11);
x_40 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_11, x_12, x_26);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_8, x_41);
lean_dec(x_8);
lean_inc(x_31);
lean_inc(x_12);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_26);
x_44 = lean_array_uset(x_9, x_25, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_51, 0, lean_box(0));
lean_closure_set(x_51, 1, x_1);
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_51, x_44);
lean_ctor_set(x_5, 1, x_52);
lean_ctor_set(x_5, 0, x_42);
x_32 = x_5;
goto block_39;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_44);
lean_ctor_set(x_5, 0, x_42);
x_32 = x_5;
goto block_39;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_array_uset(x_9, x_25, x_53);
lean_inc(x_31);
lean_inc(x_12);
x_55 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_11, x_12, x_31, x_26);
x_56 = lean_array_uset(x_54, x_25, x_55);
lean_ctor_set(x_5, 1, x_56);
x_32 = x_5;
goto block_39;
}
block_39:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_33 = lean_array_push(x_6, x_12);
if (lean_is_scalar(x_7)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_7;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_31);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_66; 
lean_dec(x_5);
x_57 = lean_array_get_size(x_6);
lean_inc(x_26);
lean_inc(x_12);
lean_inc(x_11);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_11, x_12, x_26);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_11);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_8, x_67);
lean_dec(x_8);
lean_inc(x_57);
lean_inc(x_12);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_57);
lean_ctor_set(x_69, 2, x_26);
x_70 = lean_array_uset(x_9, x_25, x_69);
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_nat_mul(x_68, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_div(x_72, x_73);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_77, 0, lean_box(0));
lean_closure_set(x_77, 1, x_1);
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_77, x_70);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_78);
x_58 = x_79;
goto block_65;
}
else
{
lean_object* x_80; 
lean_dec(x_1);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_70);
x_58 = x_80;
goto block_65;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_array_uset(x_9, x_25, x_81);
lean_inc(x_57);
lean_inc(x_12);
x_83 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_11, x_12, x_57, x_26);
x_84 = lean_array_uset(x_82, x_25, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_58 = x_85;
goto block_65;
}
block_65:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_59 = lean_array_push(x_6, x_12);
if (lean_is_scalar(x_7)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_7;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_57);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_86 = lean_ctor_get(x_27, 0);
lean_inc(x_86);
lean_dec(x_27);
if (lean_is_scalar(x_7)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_7;
}
lean_ctor_set(x_87, 0, x_6);
lean_ctor_set(x_87, 1, x_5);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_86);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_89);
return x_91;
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
lean_dec(x_1);
x_3 = l_Std_Sat_AIG_mkConstCached___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Std_Sat_AIG_mkConstCached(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_18 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_mul(x_14, x_20);
x_22 = l_Bool_toNat(x_15);
x_23 = lean_nat_lor(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_nat_mul(x_16, x_20);
x_25 = l_Bool_toNat(x_17);
x_26 = lean_nat_lor(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_23);
x_27 = lean_array_get_size(x_13);
lean_inc(x_4);
lean_inc(x_1);
x_28 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_4);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_13, x_39);
lean_inc(x_40);
lean_inc(x_4);
lean_inc(x_19);
x_41 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_19, x_4, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_46; uint8_t x_51; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_5);
lean_inc(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_42 = x_5;
} else {
 lean_dec_ref(x_5);
 x_42 = lean_box(0);
}
x_58 = l_Std_Sat_AIG_getConstant___redArg(x_3, x_8);
lean_dec(x_8);
x_59 = l_Std_Sat_AIG_getConstant___redArg(x_3, x_9);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_60 = x_9;
} else {
 lean_dec_ref(x_9);
 x_60 = lean_box(0);
}
if (lean_obj_tag(x_58) == 0)
{
lean_dec(x_42);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_61; 
x_61 = lean_nat_dec_eq(x_14, x_16);
lean_dec(x_16);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_69; 
lean_dec(x_3);
lean_dec(x_14);
x_62 = lean_array_get_size(x_10);
lean_inc(x_40);
lean_inc(x_4);
lean_inc(x_19);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_19, x_4, x_40);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_19);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_12, x_70);
lean_dec(x_12);
lean_inc(x_62);
lean_inc(x_4);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_62);
lean_ctor_set(x_72, 2, x_40);
x_73 = lean_array_uset(x_13, x_39, x_72);
x_74 = lean_unsigned_to_nat(4u);
x_75 = lean_nat_mul(x_71, x_74);
x_76 = lean_unsigned_to_nat(3u);
x_77 = lean_nat_div(x_75, x_76);
lean_dec(x_75);
x_78 = lean_array_get_size(x_73);
x_79 = lean_nat_dec_le(x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_80, 0, lean_box(0));
lean_closure_set(x_80, 1, x_1);
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_80, x_73);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_81);
x_63 = x_82;
goto block_68;
}
else
{
lean_object* x_83; 
lean_dec(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_73);
x_63 = x_83;
goto block_68;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_array_uset(x_13, x_39, x_84);
lean_inc(x_62);
lean_inc(x_4);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_19, x_4, x_62, x_40);
x_87 = lean_array_uset(x_85, x_39, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_87);
x_63 = x_88;
goto block_68;
}
block_68:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_array_push(x_10, x_4);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 1, 1);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
if (x_15 == 0)
{
if (x_17 == 0)
{
x_51 = x_61;
goto block_54;
}
else
{
lean_dec(x_14);
x_46 = x_15;
goto block_50;
}
}
else
{
x_51 = x_17;
goto block_54;
}
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_89 = lean_ctor_get(x_59, 0);
lean_inc(x_89);
lean_dec(x_59);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_dec(x_60);
lean_dec(x_14);
goto block_57;
}
else
{
lean_object* x_91; lean_object* x_92; 
if (lean_is_scalar(x_60)) {
 x_91 = lean_alloc_ctor(0, 1, 1);
} else {
 x_91 = x_60;
}
lean_ctor_set(x_91, 0, x_14);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_15);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; 
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_93 = lean_ctor_get(x_58, 0);
lean_inc(x_93);
lean_dec(x_58);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_dec(x_59);
lean_dec(x_42);
lean_dec(x_16);
goto block_57;
}
else
{
if (lean_obj_tag(x_59) == 0)
{
goto block_45;
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_59, 0);
lean_inc(x_95);
lean_dec(x_59);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_dec(x_42);
lean_dec(x_16);
goto block_57;
}
else
{
goto block_45;
}
}
}
}
block_45:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
block_50:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
block_54:
{
if (x_51 == 0)
{
lean_dec(x_14);
x_46 = x_51;
goto block_50;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_15);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
block_57:
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_97; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_9);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_9, 0);
lean_dec(x_98);
x_99 = lean_ctor_get(x_41, 0);
lean_inc(x_99);
lean_dec(x_41);
lean_inc(x_5);
x_100 = !lean_is_exclusive(x_5);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_5, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_5, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_9, 0, x_99);
x_104 = lean_unbox(x_103);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_104);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; 
lean_dec(x_5);
x_105 = lean_box(0);
lean_ctor_set(x_9, 0, x_99);
x_106 = lean_unbox(x_105);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_3);
lean_ctor_set(x_107, 1, x_9);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
lean_dec(x_9);
x_108 = lean_ctor_get(x_41, 0);
lean_inc(x_108);
lean_dec(x_41);
lean_inc(x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_109 = x_5;
} else {
 lean_dec_ref(x_5);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_108);
x_112 = lean_unbox(x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_112);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_3);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; size_t x_140; size_t x_141; size_t x_142; size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; 
x_114 = lean_ctor_get(x_4, 0);
x_115 = lean_ctor_get(x_4, 1);
x_116 = lean_ctor_get(x_3, 0);
lean_inc(x_116);
lean_dec(x_3);
x_117 = lean_ctor_get(x_5, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_5, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_114, sizeof(void*)*1);
x_121 = lean_ctor_get(x_115, 0);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_115, sizeof(void*)*1);
x_123 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_123, 0, x_2);
x_124 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_124, 0, x_123);
x_125 = lean_unsigned_to_nat(2u);
x_126 = lean_nat_mul(x_119, x_125);
x_127 = l_Bool_toNat(x_120);
x_128 = lean_nat_lor(x_126, x_127);
lean_dec(x_127);
lean_dec(x_126);
x_129 = lean_nat_mul(x_121, x_125);
x_130 = l_Bool_toNat(x_122);
x_131 = lean_nat_lor(x_129, x_130);
lean_dec(x_130);
lean_dec(x_129);
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 1, x_131);
lean_ctor_set(x_4, 0, x_128);
x_132 = lean_array_get_size(x_118);
lean_inc(x_4);
lean_inc(x_1);
x_133 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_4);
x_134 = 32;
x_135 = lean_uint64_shift_right(x_133, x_134);
x_136 = lean_uint64_xor(x_133, x_135);
x_137 = 16;
x_138 = lean_uint64_shift_right(x_136, x_137);
x_139 = lean_uint64_xor(x_136, x_138);
x_140 = lean_uint64_to_usize(x_139);
x_141 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_142 = 1;
x_143 = lean_usize_sub(x_141, x_142);
x_144 = lean_usize_land(x_140, x_143);
x_145 = lean_array_uget(x_118, x_144);
lean_inc(x_145);
lean_inc(x_4);
lean_inc(x_124);
x_146 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_124, x_4, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_152; uint8_t x_157; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc(x_5);
lean_inc(x_116);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_116);
lean_ctor_set(x_147, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_148 = x_5;
} else {
 lean_dec_ref(x_5);
 x_148 = lean_box(0);
}
x_164 = l_Std_Sat_AIG_getConstant___redArg(x_147, x_114);
lean_dec(x_114);
x_165 = l_Std_Sat_AIG_getConstant___redArg(x_147, x_115);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_166 = x_115;
} else {
 lean_dec_ref(x_115);
 x_166 = lean_box(0);
}
if (lean_obj_tag(x_164) == 0)
{
lean_dec(x_148);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_167; 
x_167 = lean_nat_dec_eq(x_119, x_121);
lean_dec(x_121);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_175; 
lean_dec(x_147);
lean_dec(x_119);
x_168 = lean_array_get_size(x_116);
lean_inc(x_145);
lean_inc(x_4);
lean_inc(x_124);
x_175 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_124, x_4, x_145);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_124);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_add(x_117, x_176);
lean_dec(x_117);
lean_inc(x_168);
lean_inc(x_4);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_4);
lean_ctor_set(x_178, 1, x_168);
lean_ctor_set(x_178, 2, x_145);
x_179 = lean_array_uset(x_118, x_144, x_178);
x_180 = lean_unsigned_to_nat(4u);
x_181 = lean_nat_mul(x_177, x_180);
x_182 = lean_unsigned_to_nat(3u);
x_183 = lean_nat_div(x_181, x_182);
lean_dec(x_181);
x_184 = lean_array_get_size(x_179);
x_185 = lean_nat_dec_le(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_186, 0, lean_box(0));
lean_closure_set(x_186, 1, x_1);
x_187 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_186, x_179);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_177);
lean_ctor_set(x_188, 1, x_187);
x_169 = x_188;
goto block_174;
}
else
{
lean_object* x_189; 
lean_dec(x_1);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_177);
lean_ctor_set(x_189, 1, x_179);
x_169 = x_189;
goto block_174;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_1);
x_190 = lean_box(0);
x_191 = lean_array_uset(x_118, x_144, x_190);
lean_inc(x_168);
lean_inc(x_4);
x_192 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_124, x_4, x_168, x_145);
x_193 = lean_array_uset(x_191, x_144, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_117);
lean_ctor_set(x_194, 1, x_193);
x_169 = x_194;
goto block_174;
}
block_174:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_array_push(x_116, x_4);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
if (lean_is_scalar(x_166)) {
 x_172 = lean_alloc_ctor(0, 1, 1);
} else {
 x_172 = x_166;
}
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_167);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
else
{
lean_dec(x_166);
lean_dec(x_145);
lean_dec(x_4);
lean_dec(x_124);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_1);
if (x_120 == 0)
{
if (x_122 == 0)
{
x_157 = x_167;
goto block_160;
}
else
{
lean_dec(x_119);
x_152 = x_120;
goto block_156;
}
}
else
{
x_157 = x_122;
goto block_160;
}
}
}
else
{
lean_object* x_195; uint8_t x_196; 
lean_dec(x_145);
lean_dec(x_4);
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_1);
x_195 = lean_ctor_get(x_165, 0);
lean_inc(x_195);
lean_dec(x_165);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_dec(x_166);
lean_dec(x_119);
goto block_163;
}
else
{
lean_object* x_197; lean_object* x_198; 
if (lean_is_scalar(x_166)) {
 x_197 = lean_alloc_ctor(0, 1, 1);
} else {
 x_197 = x_166;
}
lean_ctor_set(x_197, 0, x_119);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_120);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_147);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; uint8_t x_200; 
lean_dec(x_166);
lean_dec(x_145);
lean_dec(x_4);
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_1);
x_199 = lean_ctor_get(x_164, 0);
lean_inc(x_199);
lean_dec(x_164);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_dec(x_165);
lean_dec(x_148);
lean_dec(x_121);
goto block_163;
}
else
{
if (lean_obj_tag(x_165) == 0)
{
goto block_151;
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_165, 0);
lean_inc(x_201);
lean_dec(x_165);
x_202 = lean_unbox(x_201);
lean_dec(x_201);
if (x_202 == 0)
{
lean_dec(x_148);
lean_dec(x_121);
goto block_163;
}
else
{
goto block_151;
}
}
}
}
block_151:
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_121);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_122);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
block_156:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_unsigned_to_nat(0u);
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_152);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_147);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
block_160:
{
if (x_157 == 0)
{
lean_dec(x_119);
x_152 = x_157;
goto block_156;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_158, 0, x_119);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_120);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_147);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
block_163:
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; 
lean_dec(x_145);
lean_dec(x_4);
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_1);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_203 = x_115;
} else {
 lean_dec_ref(x_115);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_146, 0);
lean_inc(x_204);
lean_dec(x_146);
lean_inc(x_5);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_116);
lean_ctor_set(x_205, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_206 = x_5;
} else {
 lean_dec_ref(x_5);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(0, 1, 1);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_204);
x_209 = lean_unbox(x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*1, x_209);
if (lean_is_scalar(x_206)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_206;
}
lean_ctor_set(x_210, 0, x_205);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; size_t x_239; size_t x_240; size_t x_241; size_t x_242; size_t x_243; lean_object* x_244; lean_object* x_245; 
x_211 = lean_ctor_get(x_4, 0);
x_212 = lean_ctor_get(x_4, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_4);
x_213 = lean_ctor_get(x_3, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_214 = x_3;
} else {
 lean_dec_ref(x_3);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_5, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_5, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_211, 0);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_211, sizeof(void*)*1);
x_219 = lean_ctor_get(x_212, 0);
lean_inc(x_219);
x_220 = lean_ctor_get_uint8(x_212, sizeof(void*)*1);
x_221 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_221, 0, x_2);
x_222 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_222, 0, x_221);
x_223 = lean_unsigned_to_nat(2u);
x_224 = lean_nat_mul(x_217, x_223);
x_225 = l_Bool_toNat(x_218);
x_226 = lean_nat_lor(x_224, x_225);
lean_dec(x_225);
lean_dec(x_224);
x_227 = lean_nat_mul(x_219, x_223);
x_228 = l_Bool_toNat(x_220);
x_229 = lean_nat_lor(x_227, x_228);
lean_dec(x_228);
lean_dec(x_227);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_array_get_size(x_216);
lean_inc(x_230);
lean_inc(x_1);
x_232 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_230);
x_233 = 32;
x_234 = lean_uint64_shift_right(x_232, x_233);
x_235 = lean_uint64_xor(x_232, x_234);
x_236 = 16;
x_237 = lean_uint64_shift_right(x_235, x_236);
x_238 = lean_uint64_xor(x_235, x_237);
x_239 = lean_uint64_to_usize(x_238);
x_240 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_241 = 1;
x_242 = lean_usize_sub(x_240, x_241);
x_243 = lean_usize_land(x_239, x_242);
x_244 = lean_array_uget(x_216, x_243);
lean_inc(x_244);
lean_inc(x_230);
lean_inc(x_222);
x_245 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_222, x_230, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_251; uint8_t x_256; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_inc(x_5);
lean_inc(x_213);
if (lean_is_scalar(x_214)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_214;
}
lean_ctor_set(x_246, 0, x_213);
lean_ctor_set(x_246, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_247 = x_5;
} else {
 lean_dec_ref(x_5);
 x_247 = lean_box(0);
}
x_263 = l_Std_Sat_AIG_getConstant___redArg(x_246, x_211);
lean_dec(x_211);
x_264 = l_Std_Sat_AIG_getConstant___redArg(x_246, x_212);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_265 = x_212;
} else {
 lean_dec_ref(x_212);
 x_265 = lean_box(0);
}
if (lean_obj_tag(x_263) == 0)
{
lean_dec(x_247);
if (lean_obj_tag(x_264) == 0)
{
uint8_t x_266; 
x_266 = lean_nat_dec_eq(x_217, x_219);
lean_dec(x_219);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; uint8_t x_274; 
lean_dec(x_246);
lean_dec(x_217);
x_267 = lean_array_get_size(x_213);
lean_inc(x_244);
lean_inc(x_230);
lean_inc(x_222);
x_274 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_222, x_230, x_244);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_222);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_add(x_215, x_275);
lean_dec(x_215);
lean_inc(x_267);
lean_inc(x_230);
x_277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_277, 0, x_230);
lean_ctor_set(x_277, 1, x_267);
lean_ctor_set(x_277, 2, x_244);
x_278 = lean_array_uset(x_216, x_243, x_277);
x_279 = lean_unsigned_to_nat(4u);
x_280 = lean_nat_mul(x_276, x_279);
x_281 = lean_unsigned_to_nat(3u);
x_282 = lean_nat_div(x_280, x_281);
lean_dec(x_280);
x_283 = lean_array_get_size(x_278);
x_284 = lean_nat_dec_le(x_282, x_283);
lean_dec(x_283);
lean_dec(x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_285, 0, lean_box(0));
lean_closure_set(x_285, 1, x_1);
x_286 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_285, x_278);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_276);
lean_ctor_set(x_287, 1, x_286);
x_268 = x_287;
goto block_273;
}
else
{
lean_object* x_288; 
lean_dec(x_1);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_276);
lean_ctor_set(x_288, 1, x_278);
x_268 = x_288;
goto block_273;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_1);
x_289 = lean_box(0);
x_290 = lean_array_uset(x_216, x_243, x_289);
lean_inc(x_267);
lean_inc(x_230);
x_291 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_222, x_230, x_267, x_244);
x_292 = lean_array_uset(x_290, x_243, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_215);
lean_ctor_set(x_293, 1, x_292);
x_268 = x_293;
goto block_273;
}
block_273:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_array_push(x_213, x_230);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
if (lean_is_scalar(x_265)) {
 x_271 = lean_alloc_ctor(0, 1, 1);
} else {
 x_271 = x_265;
}
lean_ctor_set(x_271, 0, x_267);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_266);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
else
{
lean_dec(x_265);
lean_dec(x_244);
lean_dec(x_230);
lean_dec(x_222);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_1);
if (x_218 == 0)
{
if (x_220 == 0)
{
x_256 = x_266;
goto block_259;
}
else
{
lean_dec(x_217);
x_251 = x_218;
goto block_255;
}
}
else
{
x_256 = x_220;
goto block_259;
}
}
}
else
{
lean_object* x_294; uint8_t x_295; 
lean_dec(x_244);
lean_dec(x_230);
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_1);
x_294 = lean_ctor_get(x_264, 0);
lean_inc(x_294);
lean_dec(x_264);
x_295 = lean_unbox(x_294);
lean_dec(x_294);
if (x_295 == 0)
{
lean_dec(x_265);
lean_dec(x_217);
goto block_262;
}
else
{
lean_object* x_296; lean_object* x_297; 
if (lean_is_scalar(x_265)) {
 x_296 = lean_alloc_ctor(0, 1, 1);
} else {
 x_296 = x_265;
}
lean_ctor_set(x_296, 0, x_217);
lean_ctor_set_uint8(x_296, sizeof(void*)*1, x_218);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_246);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
else
{
lean_object* x_298; uint8_t x_299; 
lean_dec(x_265);
lean_dec(x_244);
lean_dec(x_230);
lean_dec(x_222);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_1);
x_298 = lean_ctor_get(x_263, 0);
lean_inc(x_298);
lean_dec(x_263);
x_299 = lean_unbox(x_298);
lean_dec(x_298);
if (x_299 == 0)
{
lean_dec(x_264);
lean_dec(x_247);
lean_dec(x_219);
goto block_262;
}
else
{
if (lean_obj_tag(x_264) == 0)
{
goto block_250;
}
else
{
lean_object* x_300; uint8_t x_301; 
x_300 = lean_ctor_get(x_264, 0);
lean_inc(x_300);
lean_dec(x_264);
x_301 = lean_unbox(x_300);
lean_dec(x_300);
if (x_301 == 0)
{
lean_dec(x_247);
lean_dec(x_219);
goto block_262;
}
else
{
goto block_250;
}
}
}
}
block_250:
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_248, 0, x_219);
lean_ctor_set_uint8(x_248, sizeof(void*)*1, x_220);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
block_255:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_unsigned_to_nat(0u);
x_253 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_251);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
block_259:
{
if (x_256 == 0)
{
lean_dec(x_217);
x_251 = x_256;
goto block_255;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_257, 0, x_217);
lean_ctor_set_uint8(x_257, sizeof(void*)*1, x_218);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_246);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
block_262:
{
lean_object* x_260; lean_object* x_261; 
x_260 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_246);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; 
lean_dec(x_244);
lean_dec(x_230);
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_211);
lean_dec(x_1);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_302 = x_212;
} else {
 lean_dec_ref(x_212);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_245, 0);
lean_inc(x_303);
lean_dec(x_245);
lean_inc(x_5);
if (lean_is_scalar(x_214)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_214;
}
lean_ctor_set(x_304, 0, x_213);
lean_ctor_set(x_304, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_305 = x_5;
} else {
 lean_dec_ref(x_5);
 x_305 = lean_box(0);
}
x_306 = lean_box(0);
if (lean_is_scalar(x_302)) {
 x_307 = lean_alloc_ctor(0, 1, 1);
} else {
 x_307 = x_302;
}
lean_ctor_set(x_307, 0, x_303);
x_308 = lean_unbox(x_306);
lean_ctor_set_uint8(x_307, sizeof(void*)*1, x_308);
if (lean_is_scalar(x_305)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_305;
}
lean_ctor_set(x_309, 0, x_304);
lean_ctor_set(x_309, 1, x_307);
return x_309;
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
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
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
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
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
