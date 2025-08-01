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
lean_object* l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_540____boxed(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_540_(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_800_(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_800_(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
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
lean_inc_ref(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_array_get_size(x_9);
lean_inc_ref(x_12);
lean_inc_ref(x_1);
x_14 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_540_(x_1, x_12);
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
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_27 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_11, x_12, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_39; 
x_29 = lean_ctor_get(x_5, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 0);
lean_dec(x_30);
x_31 = lean_array_get_size(x_6);
lean_inc(x_26);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_11, x_12, x_26);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_11);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_8, x_40);
lean_dec(x_8);
lean_inc(x_31);
lean_inc_ref(x_12);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_26);
x_43 = lean_array_uset(x_9, x_25, x_42);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_nat_mul(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_540____boxed), 3, 2);
lean_closure_set(x_50, 0, lean_box(0));
lean_closure_set(x_50, 1, x_1);
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_50, x_43);
lean_ctor_set(x_5, 1, x_51);
lean_ctor_set(x_5, 0, x_41);
x_32 = x_5;
goto block_38;
}
else
{
lean_dec_ref(x_1);
lean_ctor_set(x_5, 1, x_43);
lean_ctor_set(x_5, 0, x_41);
x_32 = x_5;
goto block_38;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_1);
x_52 = lean_box(0);
x_53 = lean_array_uset(x_9, x_25, x_52);
lean_inc(x_31);
lean_inc_ref(x_12);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_11, x_12, x_31, x_26);
x_55 = lean_array_uset(x_53, x_25, x_54);
lean_ctor_set(x_5, 1, x_55);
x_32 = x_5;
goto block_38;
}
block_38:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_array_push(x_6, x_12);
if (lean_is_scalar(x_7)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_7;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = 0;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_64; 
lean_dec(x_5);
x_56 = lean_array_get_size(x_6);
lean_inc(x_26);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_11, x_12, x_26);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec_ref(x_11);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_8, x_65);
lean_dec(x_8);
lean_inc(x_56);
lean_inc_ref(x_12);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_26);
x_68 = lean_array_uset(x_9, x_25, x_67);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_mul(x_66, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = lean_array_get_size(x_68);
x_74 = lean_nat_dec_le(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_540____boxed), 3, 2);
lean_closure_set(x_75, 0, lean_box(0));
lean_closure_set(x_75, 1, x_1);
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_75, x_68);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
x_57 = x_77;
goto block_63;
}
else
{
lean_object* x_78; 
lean_dec_ref(x_1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_68);
x_57 = x_78;
goto block_63;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_1);
x_79 = lean_box(0);
x_80 = lean_array_uset(x_9, x_25, x_79);
lean_inc(x_56);
lean_inc_ref(x_12);
x_81 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_11, x_12, x_56, x_26);
x_82 = lean_array_uset(x_80, x_25, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_8);
lean_ctor_set(x_83, 1, x_82);
x_57 = x_83;
goto block_63;
}
block_63:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_array_push(x_6, x_12);
if (lean_is_scalar(x_7)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_7;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = 0;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_26);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_27, 0);
lean_inc(x_84);
lean_dec_ref(x_27);
if (lean_is_scalar(x_7)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_7;
}
lean_ctor_set(x_85, 0, x_6);
lean_ctor_set(x_85, 1, x_5);
x_86 = 0;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
return x_88;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_5);
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
lean_inc_ref(x_13);
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
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_28 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_540_(x_1, x_4);
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
lean_inc_ref(x_4);
lean_inc_ref(x_19);
x_41 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_19, x_4, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_46; uint8_t x_51; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc_ref(x_5);
lean_inc_ref(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_42 = x_5;
} else {
 lean_dec_ref(x_5);
 x_42 = lean_box(0);
}
x_58 = l_Std_Sat_AIG_getConstant___redArg(x_3, x_8);
lean_dec_ref(x_8);
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
lean_dec_ref(x_3);
lean_dec(x_14);
x_62 = lean_array_get_size(x_10);
lean_inc(x_40);
lean_inc_ref(x_4);
lean_inc_ref(x_19);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_19, x_4, x_40);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec_ref(x_19);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_12, x_70);
lean_dec(x_12);
lean_inc(x_62);
lean_inc_ref(x_4);
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
x_80 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_540____boxed), 3, 2);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_84 = lean_box(0);
x_85 = lean_array_uset(x_13, x_39, x_84);
lean_inc(x_62);
lean_inc_ref(x_4);
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
lean_dec_ref(x_4);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_59, 0);
lean_inc(x_89);
lean_dec_ref(x_59);
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
lean_dec_ref(x_4);
lean_dec_ref(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_58, 0);
lean_inc(x_93);
lean_dec_ref(x_58);
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
lean_dec_ref(x_59);
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
lean_dec_ref(x_4);
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_97 = !lean_is_exclusive(x_9);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_9, 0);
lean_dec(x_98);
x_99 = lean_ctor_get(x_41, 0);
lean_inc(x_99);
lean_dec_ref(x_41);
lean_inc_ref(x_5);
x_100 = !lean_is_exclusive(x_5);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_5, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_5, 0);
lean_dec(x_102);
x_103 = 0;
lean_ctor_set(x_9, 0, x_99);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_103);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
uint8_t x_104; lean_object* x_105; 
lean_dec(x_5);
x_104 = 0;
lean_ctor_set(x_9, 0, x_99);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_104);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_3);
lean_ctor_set(x_105, 1, x_9);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_9);
x_106 = lean_ctor_get(x_41, 0);
lean_inc(x_106);
lean_dec_ref(x_41);
lean_inc_ref(x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_107 = x_5;
} else {
 lean_dec_ref(x_5);
 x_107 = lean_box(0);
}
x_108 = 0;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_3);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; size_t x_137; size_t x_138; size_t x_139; size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; 
x_111 = lean_ctor_get(x_4, 0);
x_112 = lean_ctor_get(x_4, 1);
x_113 = lean_ctor_get(x_3, 0);
lean_inc(x_113);
lean_dec(x_3);
x_114 = lean_ctor_get(x_5, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_111, sizeof(void*)*1);
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_112, sizeof(void*)*1);
x_120 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_120, 0, x_2);
x_121 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_121, 0, x_120);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_mul(x_116, x_122);
x_124 = l_Bool_toNat(x_117);
x_125 = lean_nat_lor(x_123, x_124);
lean_dec(x_124);
lean_dec(x_123);
x_126 = lean_nat_mul(x_118, x_122);
x_127 = l_Bool_toNat(x_119);
x_128 = lean_nat_lor(x_126, x_127);
lean_dec(x_127);
lean_dec(x_126);
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 1, x_128);
lean_ctor_set(x_4, 0, x_125);
x_129 = lean_array_get_size(x_115);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_130 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_540_(x_1, x_4);
x_131 = 32;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = 16;
x_135 = lean_uint64_shift_right(x_133, x_134);
x_136 = lean_uint64_xor(x_133, x_135);
x_137 = lean_uint64_to_usize(x_136);
x_138 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_139 = 1;
x_140 = lean_usize_sub(x_138, x_139);
x_141 = lean_usize_land(x_137, x_140);
x_142 = lean_array_uget(x_115, x_141);
lean_inc(x_142);
lean_inc_ref(x_4);
lean_inc_ref(x_121);
x_143 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_121, x_4, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_149; uint8_t x_154; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_inc_ref(x_5);
lean_inc_ref(x_113);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_113);
lean_ctor_set(x_144, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_145 = x_5;
} else {
 lean_dec_ref(x_5);
 x_145 = lean_box(0);
}
x_161 = l_Std_Sat_AIG_getConstant___redArg(x_144, x_111);
lean_dec_ref(x_111);
x_162 = l_Std_Sat_AIG_getConstant___redArg(x_144, x_112);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_163 = x_112;
} else {
 lean_dec_ref(x_112);
 x_163 = lean_box(0);
}
if (lean_obj_tag(x_161) == 0)
{
lean_dec(x_145);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_164; 
x_164 = lean_nat_dec_eq(x_116, x_118);
lean_dec(x_118);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_172; 
lean_dec_ref(x_144);
lean_dec(x_116);
x_165 = lean_array_get_size(x_113);
lean_inc(x_142);
lean_inc_ref(x_4);
lean_inc_ref(x_121);
x_172 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_121, x_4, x_142);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec_ref(x_121);
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_nat_add(x_114, x_173);
lean_dec(x_114);
lean_inc(x_165);
lean_inc_ref(x_4);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_4);
lean_ctor_set(x_175, 1, x_165);
lean_ctor_set(x_175, 2, x_142);
x_176 = lean_array_uset(x_115, x_141, x_175);
x_177 = lean_unsigned_to_nat(4u);
x_178 = lean_nat_mul(x_174, x_177);
x_179 = lean_unsigned_to_nat(3u);
x_180 = lean_nat_div(x_178, x_179);
lean_dec(x_178);
x_181 = lean_array_get_size(x_176);
x_182 = lean_nat_dec_le(x_180, x_181);
lean_dec(x_181);
lean_dec(x_180);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_540____boxed), 3, 2);
lean_closure_set(x_183, 0, lean_box(0));
lean_closure_set(x_183, 1, x_1);
x_184 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_183, x_176);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_174);
lean_ctor_set(x_185, 1, x_184);
x_166 = x_185;
goto block_171;
}
else
{
lean_object* x_186; 
lean_dec_ref(x_1);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_174);
lean_ctor_set(x_186, 1, x_176);
x_166 = x_186;
goto block_171;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_1);
x_187 = lean_box(0);
x_188 = lean_array_uset(x_115, x_141, x_187);
lean_inc(x_165);
lean_inc_ref(x_4);
x_189 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_121, x_4, x_165, x_142);
x_190 = lean_array_uset(x_188, x_141, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_114);
lean_ctor_set(x_191, 1, x_190);
x_166 = x_191;
goto block_171;
}
block_171:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_array_push(x_113, x_4);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
if (lean_is_scalar(x_163)) {
 x_169 = lean_alloc_ctor(0, 1, 1);
} else {
 x_169 = x_163;
}
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_164);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_dec(x_163);
lean_dec(x_142);
lean_dec_ref(x_4);
lean_dec_ref(x_121);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_1);
if (x_117 == 0)
{
if (x_119 == 0)
{
x_154 = x_164;
goto block_157;
}
else
{
lean_dec(x_116);
x_149 = x_117;
goto block_153;
}
}
else
{
x_154 = x_119;
goto block_157;
}
}
}
else
{
lean_object* x_192; uint8_t x_193; 
lean_dec(x_142);
lean_dec_ref(x_4);
lean_dec_ref(x_121);
lean_dec(x_118);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_1);
x_192 = lean_ctor_get(x_162, 0);
lean_inc(x_192);
lean_dec_ref(x_162);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_dec(x_163);
lean_dec(x_116);
goto block_160;
}
else
{
lean_object* x_194; lean_object* x_195; 
if (lean_is_scalar(x_163)) {
 x_194 = lean_alloc_ctor(0, 1, 1);
} else {
 x_194 = x_163;
}
lean_ctor_set(x_194, 0, x_116);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_117);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_144);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; uint8_t x_197; 
lean_dec(x_163);
lean_dec(x_142);
lean_dec_ref(x_4);
lean_dec_ref(x_121);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_1);
x_196 = lean_ctor_get(x_161, 0);
lean_inc(x_196);
lean_dec_ref(x_161);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
lean_dec(x_162);
lean_dec(x_145);
lean_dec(x_118);
goto block_160;
}
else
{
if (lean_obj_tag(x_162) == 0)
{
goto block_148;
}
else
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_162, 0);
lean_inc(x_198);
lean_dec_ref(x_162);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_dec(x_145);
lean_dec(x_118);
goto block_160;
}
else
{
goto block_148;
}
}
}
}
block_148:
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_146, 0, x_118);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_119);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
block_153:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
block_157:
{
if (x_154 == 0)
{
lean_dec(x_116);
x_149 = x_154;
goto block_153;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_116);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_117);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_144);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
block_160:
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_144);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_142);
lean_dec_ref(x_4);
lean_dec_ref(x_121);
lean_dec(x_118);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_111);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_200 = x_112;
} else {
 lean_dec_ref(x_112);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_143, 0);
lean_inc(x_201);
lean_dec_ref(x_143);
lean_inc_ref(x_5);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_113);
lean_ctor_set(x_202, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_203 = x_5;
} else {
 lean_dec_ref(x_5);
 x_203 = lean_box(0);
}
x_204 = 0;
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 1, 1);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_204);
if (lean_is_scalar(x_203)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_203;
}
lean_ctor_set(x_206, 0, x_202);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint64_t x_228; uint64_t x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; size_t x_235; size_t x_236; size_t x_237; size_t x_238; size_t x_239; lean_object* x_240; lean_object* x_241; 
x_207 = lean_ctor_get(x_4, 0);
x_208 = lean_ctor_get(x_4, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_4);
x_209 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_209);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_210 = x_3;
} else {
 lean_dec_ref(x_3);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_5, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_212);
x_213 = lean_ctor_get(x_207, 0);
lean_inc(x_213);
x_214 = lean_ctor_get_uint8(x_207, sizeof(void*)*1);
x_215 = lean_ctor_get(x_208, 0);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_208, sizeof(void*)*1);
x_217 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_217, 0, x_2);
x_218 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_218, 0, x_217);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_nat_mul(x_213, x_219);
x_221 = l_Bool_toNat(x_214);
x_222 = lean_nat_lor(x_220, x_221);
lean_dec(x_221);
lean_dec(x_220);
x_223 = lean_nat_mul(x_215, x_219);
x_224 = l_Bool_toNat(x_216);
x_225 = lean_nat_lor(x_223, x_224);
lean_dec(x_224);
lean_dec(x_223);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_get_size(x_212);
lean_inc_ref(x_226);
lean_inc_ref(x_1);
x_228 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_540_(x_1, x_226);
x_229 = 32;
x_230 = lean_uint64_shift_right(x_228, x_229);
x_231 = lean_uint64_xor(x_228, x_230);
x_232 = 16;
x_233 = lean_uint64_shift_right(x_231, x_232);
x_234 = lean_uint64_xor(x_231, x_233);
x_235 = lean_uint64_to_usize(x_234);
x_236 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_237 = 1;
x_238 = lean_usize_sub(x_236, x_237);
x_239 = lean_usize_land(x_235, x_238);
x_240 = lean_array_uget(x_212, x_239);
lean_inc(x_240);
lean_inc_ref(x_226);
lean_inc_ref(x_218);
x_241 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_218, x_226, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_247; uint8_t x_252; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_inc_ref(x_5);
lean_inc_ref(x_209);
if (lean_is_scalar(x_210)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_210;
}
lean_ctor_set(x_242, 0, x_209);
lean_ctor_set(x_242, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_243 = x_5;
} else {
 lean_dec_ref(x_5);
 x_243 = lean_box(0);
}
x_259 = l_Std_Sat_AIG_getConstant___redArg(x_242, x_207);
lean_dec_ref(x_207);
x_260 = l_Std_Sat_AIG_getConstant___redArg(x_242, x_208);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_261 = x_208;
} else {
 lean_dec_ref(x_208);
 x_261 = lean_box(0);
}
if (lean_obj_tag(x_259) == 0)
{
lean_dec(x_243);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_262; 
x_262 = lean_nat_dec_eq(x_213, x_215);
lean_dec(x_215);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_270; 
lean_dec_ref(x_242);
lean_dec(x_213);
x_263 = lean_array_get_size(x_209);
lean_inc(x_240);
lean_inc_ref(x_226);
lean_inc_ref(x_218);
x_270 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_218, x_226, x_240);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_dec_ref(x_218);
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_add(x_211, x_271);
lean_dec(x_211);
lean_inc(x_263);
lean_inc_ref(x_226);
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_226);
lean_ctor_set(x_273, 1, x_263);
lean_ctor_set(x_273, 2, x_240);
x_274 = lean_array_uset(x_212, x_239, x_273);
x_275 = lean_unsigned_to_nat(4u);
x_276 = lean_nat_mul(x_272, x_275);
x_277 = lean_unsigned_to_nat(3u);
x_278 = lean_nat_div(x_276, x_277);
lean_dec(x_276);
x_279 = lean_array_get_size(x_274);
x_280 = lean_nat_dec_le(x_278, x_279);
lean_dec(x_279);
lean_dec(x_278);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_540____boxed), 3, 2);
lean_closure_set(x_281, 0, lean_box(0));
lean_closure_set(x_281, 1, x_1);
x_282 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_281, x_274);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_272);
lean_ctor_set(x_283, 1, x_282);
x_264 = x_283;
goto block_269;
}
else
{
lean_object* x_284; 
lean_dec_ref(x_1);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_272);
lean_ctor_set(x_284, 1, x_274);
x_264 = x_284;
goto block_269;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec_ref(x_1);
x_285 = lean_box(0);
x_286 = lean_array_uset(x_212, x_239, x_285);
lean_inc(x_263);
lean_inc_ref(x_226);
x_287 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_218, x_226, x_263, x_240);
x_288 = lean_array_uset(x_286, x_239, x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_211);
lean_ctor_set(x_289, 1, x_288);
x_264 = x_289;
goto block_269;
}
block_269:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_array_push(x_209, x_226);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
if (lean_is_scalar(x_261)) {
 x_267 = lean_alloc_ctor(0, 1, 1);
} else {
 x_267 = x_261;
}
lean_ctor_set(x_267, 0, x_263);
lean_ctor_set_uint8(x_267, sizeof(void*)*1, x_262);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
else
{
lean_dec(x_261);
lean_dec(x_240);
lean_dec_ref(x_226);
lean_dec_ref(x_218);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_209);
lean_dec_ref(x_1);
if (x_214 == 0)
{
if (x_216 == 0)
{
x_252 = x_262;
goto block_255;
}
else
{
lean_dec(x_213);
x_247 = x_214;
goto block_251;
}
}
else
{
x_252 = x_216;
goto block_255;
}
}
}
else
{
lean_object* x_290; uint8_t x_291; 
lean_dec(x_240);
lean_dec_ref(x_226);
lean_dec_ref(x_218);
lean_dec(x_215);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_209);
lean_dec_ref(x_1);
x_290 = lean_ctor_get(x_260, 0);
lean_inc(x_290);
lean_dec_ref(x_260);
x_291 = lean_unbox(x_290);
lean_dec(x_290);
if (x_291 == 0)
{
lean_dec(x_261);
lean_dec(x_213);
goto block_258;
}
else
{
lean_object* x_292; lean_object* x_293; 
if (lean_is_scalar(x_261)) {
 x_292 = lean_alloc_ctor(0, 1, 1);
} else {
 x_292 = x_261;
}
lean_ctor_set(x_292, 0, x_213);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_214);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_242);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
lean_object* x_294; uint8_t x_295; 
lean_dec(x_261);
lean_dec(x_240);
lean_dec_ref(x_226);
lean_dec_ref(x_218);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_209);
lean_dec_ref(x_1);
x_294 = lean_ctor_get(x_259, 0);
lean_inc(x_294);
lean_dec_ref(x_259);
x_295 = lean_unbox(x_294);
lean_dec(x_294);
if (x_295 == 0)
{
lean_dec(x_260);
lean_dec(x_243);
lean_dec(x_215);
goto block_258;
}
else
{
if (lean_obj_tag(x_260) == 0)
{
goto block_246;
}
else
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_ctor_get(x_260, 0);
lean_inc(x_296);
lean_dec_ref(x_260);
x_297 = lean_unbox(x_296);
lean_dec(x_296);
if (x_297 == 0)
{
lean_dec(x_243);
lean_dec(x_215);
goto block_258;
}
else
{
goto block_246;
}
}
}
}
block_246:
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_244, 0, x_215);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_216);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
block_251:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_unsigned_to_nat(0u);
x_249 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set_uint8(x_249, sizeof(void*)*1, x_247);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
block_255:
{
if (x_252 == 0)
{
lean_dec(x_213);
x_247 = x_252;
goto block_251;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_253, 0, x_213);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_214);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_242);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
block_258:
{
lean_object* x_256; lean_object* x_257; 
x_256 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_242);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_240);
lean_dec_ref(x_226);
lean_dec_ref(x_218);
lean_dec(x_215);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_207);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_298 = x_208;
} else {
 lean_dec_ref(x_208);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_241, 0);
lean_inc(x_299);
lean_dec_ref(x_241);
lean_inc_ref(x_5);
if (lean_is_scalar(x_210)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_210;
}
lean_ctor_set(x_300, 0, x_209);
lean_ctor_set(x_300, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_301 = x_5;
} else {
 lean_dec_ref(x_5);
 x_301 = lean_box(0);
}
x_302 = 0;
if (lean_is_scalar(x_298)) {
 x_303 = lean_alloc_ctor(0, 1, 1);
} else {
 x_303 = x_298;
}
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set_uint8(x_303, sizeof(void*)*1, x_302);
if (lean_is_scalar(x_301)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_301;
}
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_303);
return x_304;
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
