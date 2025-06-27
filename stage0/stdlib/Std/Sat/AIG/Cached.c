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
lean_object* x_89; 
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_89 = lean_box(0);
if (x_15 == 0)
{
if (x_17 == 0)
{
x_51 = x_61;
goto block_54;
}
else
{
uint8_t x_90; 
lean_dec(x_14);
x_90 = lean_unbox(x_89);
x_46 = x_90;
goto block_50;
}
}
else
{
if (x_17 == 0)
{
uint8_t x_91; 
lean_dec(x_14);
x_91 = lean_unbox(x_89);
x_46 = x_91;
goto block_50;
}
else
{
x_51 = x_61;
goto block_54;
}
}
}
}
else
{
lean_object* x_92; uint8_t x_93; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_92 = lean_ctor_get(x_59, 0);
lean_inc(x_92);
lean_dec(x_59);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_dec(x_60);
lean_dec(x_14);
goto block_57;
}
else
{
lean_object* x_94; lean_object* x_95; 
if (lean_is_scalar(x_60)) {
 x_94 = lean_alloc_ctor(0, 1, 1);
} else {
 x_94 = x_60;
}
lean_ctor_set(x_94, 0, x_14);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_15);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_3);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; 
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_96 = lean_ctor_get(x_58, 0);
lean_inc(x_96);
lean_dec(x_58);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
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
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_59, 0);
lean_inc(x_98);
lean_dec(x_59);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
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
uint8_t x_100; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_9);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_9, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_41, 0);
lean_inc(x_102);
lean_dec(x_41);
lean_inc(x_5);
x_103 = !lean_is_exclusive(x_5);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_5, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_5, 0);
lean_dec(x_105);
x_106 = lean_box(0);
lean_ctor_set(x_9, 0, x_102);
x_107 = lean_unbox(x_106);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_107);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; 
lean_dec(x_5);
x_108 = lean_box(0);
lean_ctor_set(x_9, 0, x_102);
x_109 = lean_unbox(x_108);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_109);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_3);
lean_ctor_set(x_110, 1, x_9);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
lean_dec(x_9);
x_111 = lean_ctor_get(x_41, 0);
lean_inc(x_111);
lean_dec(x_41);
lean_inc(x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_112 = x_5;
} else {
 lean_dec_ref(x_5);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_111);
x_115 = lean_unbox(x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_115);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_3);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; size_t x_143; size_t x_144; size_t x_145; size_t x_146; size_t x_147; lean_object* x_148; lean_object* x_149; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
x_119 = lean_ctor_get(x_3, 0);
lean_inc(x_119);
lean_dec(x_3);
x_120 = lean_ctor_get(x_5, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_5, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
x_126 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_126, 0, x_2);
x_127 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_127, 0, x_126);
x_128 = lean_unsigned_to_nat(2u);
x_129 = lean_nat_mul(x_122, x_128);
x_130 = l_Bool_toNat(x_123);
x_131 = lean_nat_lor(x_129, x_130);
lean_dec(x_130);
lean_dec(x_129);
x_132 = lean_nat_mul(x_124, x_128);
x_133 = l_Bool_toNat(x_125);
x_134 = lean_nat_lor(x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 1, x_134);
lean_ctor_set(x_4, 0, x_131);
x_135 = lean_array_get_size(x_121);
lean_inc(x_4);
lean_inc(x_1);
x_136 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_4);
x_137 = 32;
x_138 = lean_uint64_shift_right(x_136, x_137);
x_139 = lean_uint64_xor(x_136, x_138);
x_140 = 16;
x_141 = lean_uint64_shift_right(x_139, x_140);
x_142 = lean_uint64_xor(x_139, x_141);
x_143 = lean_uint64_to_usize(x_142);
x_144 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_145 = 1;
x_146 = lean_usize_sub(x_144, x_145);
x_147 = lean_usize_land(x_143, x_146);
x_148 = lean_array_uget(x_121, x_147);
lean_inc(x_148);
lean_inc(x_4);
lean_inc(x_127);
x_149 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_127, x_4, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_155; uint8_t x_160; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_inc(x_5);
lean_inc(x_119);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_119);
lean_ctor_set(x_150, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_151 = x_5;
} else {
 lean_dec_ref(x_5);
 x_151 = lean_box(0);
}
x_167 = l_Std_Sat_AIG_getConstant___redArg(x_150, x_117);
lean_dec(x_117);
x_168 = l_Std_Sat_AIG_getConstant___redArg(x_150, x_118);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_169 = x_118;
} else {
 lean_dec_ref(x_118);
 x_169 = lean_box(0);
}
if (lean_obj_tag(x_167) == 0)
{
lean_dec(x_151);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_170; 
x_170 = lean_nat_dec_eq(x_122, x_124);
lean_dec(x_124);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_178; 
lean_dec(x_150);
lean_dec(x_122);
x_171 = lean_array_get_size(x_119);
lean_inc(x_148);
lean_inc(x_4);
lean_inc(x_127);
x_178 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_127, x_4, x_148);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_127);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_nat_add(x_120, x_179);
lean_dec(x_120);
lean_inc(x_171);
lean_inc(x_4);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_4);
lean_ctor_set(x_181, 1, x_171);
lean_ctor_set(x_181, 2, x_148);
x_182 = lean_array_uset(x_121, x_147, x_181);
x_183 = lean_unsigned_to_nat(4u);
x_184 = lean_nat_mul(x_180, x_183);
x_185 = lean_unsigned_to_nat(3u);
x_186 = lean_nat_div(x_184, x_185);
lean_dec(x_184);
x_187 = lean_array_get_size(x_182);
x_188 = lean_nat_dec_le(x_186, x_187);
lean_dec(x_187);
lean_dec(x_186);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_189, 0, lean_box(0));
lean_closure_set(x_189, 1, x_1);
x_190 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_189, x_182);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_180);
lean_ctor_set(x_191, 1, x_190);
x_172 = x_191;
goto block_177;
}
else
{
lean_object* x_192; 
lean_dec(x_1);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_182);
x_172 = x_192;
goto block_177;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_1);
x_193 = lean_box(0);
x_194 = lean_array_uset(x_121, x_147, x_193);
lean_inc(x_171);
lean_inc(x_4);
x_195 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_127, x_4, x_171, x_148);
x_196 = lean_array_uset(x_194, x_147, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_120);
lean_ctor_set(x_197, 1, x_196);
x_172 = x_197;
goto block_177;
}
block_177:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_array_push(x_119, x_4);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
if (lean_is_scalar(x_169)) {
 x_175 = lean_alloc_ctor(0, 1, 1);
} else {
 x_175 = x_169;
}
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_170);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
lean_object* x_198; 
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_4);
lean_dec(x_127);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_1);
x_198 = lean_box(0);
if (x_123 == 0)
{
if (x_125 == 0)
{
x_160 = x_170;
goto block_163;
}
else
{
uint8_t x_199; 
lean_dec(x_122);
x_199 = lean_unbox(x_198);
x_155 = x_199;
goto block_159;
}
}
else
{
if (x_125 == 0)
{
uint8_t x_200; 
lean_dec(x_122);
x_200 = lean_unbox(x_198);
x_155 = x_200;
goto block_159;
}
else
{
x_160 = x_170;
goto block_163;
}
}
}
}
else
{
lean_object* x_201; uint8_t x_202; 
lean_dec(x_148);
lean_dec(x_4);
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_1);
x_201 = lean_ctor_get(x_168, 0);
lean_inc(x_201);
lean_dec(x_168);
x_202 = lean_unbox(x_201);
lean_dec(x_201);
if (x_202 == 0)
{
lean_dec(x_169);
lean_dec(x_122);
goto block_166;
}
else
{
lean_object* x_203; lean_object* x_204; 
if (lean_is_scalar(x_169)) {
 x_203 = lean_alloc_ctor(0, 1, 1);
} else {
 x_203 = x_169;
}
lean_ctor_set(x_203, 0, x_122);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_123);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_150);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
lean_object* x_205; uint8_t x_206; 
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_4);
lean_dec(x_127);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_1);
x_205 = lean_ctor_get(x_167, 0);
lean_inc(x_205);
lean_dec(x_167);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
lean_dec(x_168);
lean_dec(x_151);
lean_dec(x_124);
goto block_166;
}
else
{
if (lean_obj_tag(x_168) == 0)
{
goto block_154;
}
else
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_168, 0);
lean_inc(x_207);
lean_dec(x_168);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_dec(x_151);
lean_dec(x_124);
goto block_166;
}
else
{
goto block_154;
}
}
}
}
block_154:
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_124);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_125);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
block_159:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
block_163:
{
if (x_160 == 0)
{
lean_dec(x_122);
x_155 = x_160;
goto block_159;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_161, 0, x_122);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_123);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_150);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
block_166:
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_150);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
lean_dec(x_148);
lean_dec(x_4);
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_1);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_209 = x_118;
} else {
 lean_dec_ref(x_118);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_149, 0);
lean_inc(x_210);
lean_dec(x_149);
lean_inc(x_5);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_119);
lean_ctor_set(x_211, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_212 = x_5;
} else {
 lean_dec_ref(x_5);
 x_212 = lean_box(0);
}
x_213 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_214 = lean_alloc_ctor(0, 1, 1);
} else {
 x_214 = x_209;
}
lean_ctor_set(x_214, 0, x_210);
x_215 = lean_unbox(x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_215);
if (lean_is_scalar(x_212)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_212;
}
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint64_t x_238; uint64_t x_239; uint64_t x_240; uint64_t x_241; uint64_t x_242; uint64_t x_243; uint64_t x_244; size_t x_245; size_t x_246; size_t x_247; size_t x_248; size_t x_249; lean_object* x_250; lean_object* x_251; 
x_217 = lean_ctor_get(x_4, 0);
x_218 = lean_ctor_get(x_4, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_4);
x_219 = lean_ctor_get(x_3, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_220 = x_3;
} else {
 lean_dec_ref(x_3);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_5, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_5, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 0);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_217, sizeof(void*)*1);
x_225 = lean_ctor_get(x_218, 0);
lean_inc(x_225);
x_226 = lean_ctor_get_uint8(x_218, sizeof(void*)*1);
x_227 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_227, 0, x_2);
x_228 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_228, 0, x_227);
x_229 = lean_unsigned_to_nat(2u);
x_230 = lean_nat_mul(x_223, x_229);
x_231 = l_Bool_toNat(x_224);
x_232 = lean_nat_lor(x_230, x_231);
lean_dec(x_231);
lean_dec(x_230);
x_233 = lean_nat_mul(x_225, x_229);
x_234 = l_Bool_toNat(x_226);
x_235 = lean_nat_lor(x_233, x_234);
lean_dec(x_234);
lean_dec(x_233);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_232);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_array_get_size(x_222);
lean_inc(x_236);
lean_inc(x_1);
x_238 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_236);
x_239 = 32;
x_240 = lean_uint64_shift_right(x_238, x_239);
x_241 = lean_uint64_xor(x_238, x_240);
x_242 = 16;
x_243 = lean_uint64_shift_right(x_241, x_242);
x_244 = lean_uint64_xor(x_241, x_243);
x_245 = lean_uint64_to_usize(x_244);
x_246 = lean_usize_of_nat(x_237);
lean_dec(x_237);
x_247 = 1;
x_248 = lean_usize_sub(x_246, x_247);
x_249 = lean_usize_land(x_245, x_248);
x_250 = lean_array_uget(x_222, x_249);
lean_inc(x_250);
lean_inc(x_236);
lean_inc(x_228);
x_251 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_228, x_236, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_257; uint8_t x_262; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_inc(x_5);
lean_inc(x_219);
if (lean_is_scalar(x_220)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_220;
}
lean_ctor_set(x_252, 0, x_219);
lean_ctor_set(x_252, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_253 = x_5;
} else {
 lean_dec_ref(x_5);
 x_253 = lean_box(0);
}
x_269 = l_Std_Sat_AIG_getConstant___redArg(x_252, x_217);
lean_dec(x_217);
x_270 = l_Std_Sat_AIG_getConstant___redArg(x_252, x_218);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_271 = x_218;
} else {
 lean_dec_ref(x_218);
 x_271 = lean_box(0);
}
if (lean_obj_tag(x_269) == 0)
{
lean_dec(x_253);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_272; 
x_272 = lean_nat_dec_eq(x_223, x_225);
lean_dec(x_225);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_280; 
lean_dec(x_252);
lean_dec(x_223);
x_273 = lean_array_get_size(x_219);
lean_inc(x_250);
lean_inc(x_236);
lean_inc(x_228);
x_280 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_228, x_236, x_250);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
lean_dec(x_228);
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_nat_add(x_221, x_281);
lean_dec(x_221);
lean_inc(x_273);
lean_inc(x_236);
x_283 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_283, 0, x_236);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set(x_283, 2, x_250);
x_284 = lean_array_uset(x_222, x_249, x_283);
x_285 = lean_unsigned_to_nat(4u);
x_286 = lean_nat_mul(x_282, x_285);
x_287 = lean_unsigned_to_nat(3u);
x_288 = lean_nat_div(x_286, x_287);
lean_dec(x_286);
x_289 = lean_array_get_size(x_284);
x_290 = lean_nat_dec_le(x_288, x_289);
lean_dec(x_289);
lean_dec(x_288);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_291, 0, lean_box(0));
lean_closure_set(x_291, 1, x_1);
x_292 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_291, x_284);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_282);
lean_ctor_set(x_293, 1, x_292);
x_274 = x_293;
goto block_279;
}
else
{
lean_object* x_294; 
lean_dec(x_1);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_282);
lean_ctor_set(x_294, 1, x_284);
x_274 = x_294;
goto block_279;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_1);
x_295 = lean_box(0);
x_296 = lean_array_uset(x_222, x_249, x_295);
lean_inc(x_273);
lean_inc(x_236);
x_297 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_228, x_236, x_273, x_250);
x_298 = lean_array_uset(x_296, x_249, x_297);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_221);
lean_ctor_set(x_299, 1, x_298);
x_274 = x_299;
goto block_279;
}
block_279:
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_array_push(x_219, x_236);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
if (lean_is_scalar(x_271)) {
 x_277 = lean_alloc_ctor(0, 1, 1);
} else {
 x_277 = x_271;
}
lean_ctor_set(x_277, 0, x_273);
lean_ctor_set_uint8(x_277, sizeof(void*)*1, x_272);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
else
{
lean_object* x_300; 
lean_dec(x_271);
lean_dec(x_250);
lean_dec(x_236);
lean_dec(x_228);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_1);
x_300 = lean_box(0);
if (x_224 == 0)
{
if (x_226 == 0)
{
x_262 = x_272;
goto block_265;
}
else
{
uint8_t x_301; 
lean_dec(x_223);
x_301 = lean_unbox(x_300);
x_257 = x_301;
goto block_261;
}
}
else
{
if (x_226 == 0)
{
uint8_t x_302; 
lean_dec(x_223);
x_302 = lean_unbox(x_300);
x_257 = x_302;
goto block_261;
}
else
{
x_262 = x_272;
goto block_265;
}
}
}
}
else
{
lean_object* x_303; uint8_t x_304; 
lean_dec(x_250);
lean_dec(x_236);
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_1);
x_303 = lean_ctor_get(x_270, 0);
lean_inc(x_303);
lean_dec(x_270);
x_304 = lean_unbox(x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_dec(x_271);
lean_dec(x_223);
goto block_268;
}
else
{
lean_object* x_305; lean_object* x_306; 
if (lean_is_scalar(x_271)) {
 x_305 = lean_alloc_ctor(0, 1, 1);
} else {
 x_305 = x_271;
}
lean_ctor_set(x_305, 0, x_223);
lean_ctor_set_uint8(x_305, sizeof(void*)*1, x_224);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_252);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
else
{
lean_object* x_307; uint8_t x_308; 
lean_dec(x_271);
lean_dec(x_250);
lean_dec(x_236);
lean_dec(x_228);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_1);
x_307 = lean_ctor_get(x_269, 0);
lean_inc(x_307);
lean_dec(x_269);
x_308 = lean_unbox(x_307);
lean_dec(x_307);
if (x_308 == 0)
{
lean_dec(x_270);
lean_dec(x_253);
lean_dec(x_225);
goto block_268;
}
else
{
if (lean_obj_tag(x_270) == 0)
{
goto block_256;
}
else
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_270, 0);
lean_inc(x_309);
lean_dec(x_270);
x_310 = lean_unbox(x_309);
lean_dec(x_309);
if (x_310 == 0)
{
lean_dec(x_253);
lean_dec(x_225);
goto block_268;
}
else
{
goto block_256;
}
}
}
}
block_256:
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_254, 0, x_225);
lean_ctor_set_uint8(x_254, sizeof(void*)*1, x_226);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
block_261:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_unsigned_to_nat(0u);
x_259 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_257);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
block_265:
{
if (x_262 == 0)
{
lean_dec(x_223);
x_257 = x_262;
goto block_261;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_263, 0, x_223);
lean_ctor_set_uint8(x_263, sizeof(void*)*1, x_224);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_252);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
block_268:
{
lean_object* x_266; lean_object* x_267; 
x_266 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_252);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; 
lean_dec(x_250);
lean_dec(x_236);
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_217);
lean_dec(x_1);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_311 = x_218;
} else {
 lean_dec_ref(x_218);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_251, 0);
lean_inc(x_312);
lean_dec(x_251);
lean_inc(x_5);
if (lean_is_scalar(x_220)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_220;
}
lean_ctor_set(x_313, 0, x_219);
lean_ctor_set(x_313, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_314 = x_5;
} else {
 lean_dec_ref(x_5);
 x_314 = lean_box(0);
}
x_315 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_316 = lean_alloc_ctor(0, 1, 1);
} else {
 x_316 = x_311;
}
lean_ctor_set(x_316, 0, x_312);
x_317 = lean_unbox(x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*1, x_317);
if (lean_is_scalar(x_314)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_314;
}
lean_ctor_set(x_318, 0, x_313);
lean_ctor_set(x_318, 1, x_316);
return x_318;
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
