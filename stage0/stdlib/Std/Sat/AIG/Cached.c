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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_39; 
x_29 = lean_ctor_get(x_5, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 0);
lean_dec(x_30);
x_31 = lean_array_get_size(x_6);
lean_inc(x_26);
lean_inc(x_12);
lean_inc(x_11);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_11, x_12, x_26);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_11);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_8, x_40);
lean_dec(x_8);
lean_inc(x_31);
lean_inc(x_12);
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
x_50 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
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
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_43);
lean_ctor_set(x_5, 0, x_41);
x_32 = x_5;
goto block_38;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_array_uset(x_9, x_25, x_52);
lean_inc(x_31);
lean_inc(x_12);
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
lean_inc(x_12);
lean_inc(x_11);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_11, x_12, x_26);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_11);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_8, x_65);
lean_dec(x_8);
lean_inc(x_56);
lean_inc(x_12);
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
x_75 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
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
lean_dec(x_1);
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
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = lean_array_uset(x_9, x_25, x_79);
lean_inc(x_56);
lean_inc(x_12);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_84 = lean_ctor_get(x_27, 0);
lean_inc(x_84);
lean_dec(x_27);
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
uint8_t x_89; 
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_89 = 0;
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
x_46 = x_89;
goto block_50;
}
}
else
{
if (x_17 == 0)
{
lean_dec(x_14);
x_46 = x_89;
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
lean_object* x_90; uint8_t x_91; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_90 = lean_ctor_get(x_59, 0);
lean_inc(x_90);
lean_dec(x_59);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_dec(x_60);
lean_dec(x_14);
goto block_57;
}
else
{
lean_object* x_92; lean_object* x_93; 
if (lean_is_scalar(x_60)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_60;
}
lean_ctor_set(x_92, 0, x_14);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_15);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_60);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_94 = lean_ctor_get(x_58, 0);
lean_inc(x_94);
lean_dec(x_58);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
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
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_59, 0);
lean_inc(x_96);
lean_dec(x_59);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
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
uint8_t x_98; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_9);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_9, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_41, 0);
lean_inc(x_100);
lean_dec(x_41);
lean_inc(x_5);
x_101 = !lean_is_exclusive(x_5);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_5, 1);
lean_dec(x_102);
x_103 = lean_ctor_get(x_5, 0);
lean_dec(x_103);
x_104 = 0;
lean_ctor_set(x_9, 0, x_100);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_104);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
uint8_t x_105; lean_object* x_106; 
lean_dec(x_5);
x_105 = 0;
lean_ctor_set(x_9, 0, x_100);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_105);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_3);
lean_ctor_set(x_106, 1, x_9);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_9);
x_107 = lean_ctor_get(x_41, 0);
lean_inc(x_107);
lean_dec(x_41);
lean_inc(x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_108 = x_5;
} else {
 lean_dec_ref(x_5);
 x_108 = lean_box(0);
}
x_109 = 0;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_3);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; size_t x_138; size_t x_139; size_t x_140; size_t x_141; size_t x_142; lean_object* x_143; lean_object* x_144; 
x_112 = lean_ctor_get(x_4, 0);
x_113 = lean_ctor_get(x_4, 1);
x_114 = lean_ctor_get(x_3, 0);
lean_inc(x_114);
lean_dec(x_3);
x_115 = lean_ctor_get(x_5, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_112, sizeof(void*)*1);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_113, sizeof(void*)*1);
x_121 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_121, 0, x_2);
x_122 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_122, 0, x_121);
x_123 = lean_unsigned_to_nat(2u);
x_124 = lean_nat_mul(x_117, x_123);
x_125 = l_Bool_toNat(x_118);
x_126 = lean_nat_lor(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
x_127 = lean_nat_mul(x_119, x_123);
x_128 = l_Bool_toNat(x_120);
x_129 = lean_nat_lor(x_127, x_128);
lean_dec(x_128);
lean_dec(x_127);
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 1, x_129);
lean_ctor_set(x_4, 0, x_126);
x_130 = lean_array_get_size(x_116);
lean_inc(x_4);
lean_inc(x_1);
x_131 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_4);
x_132 = 32;
x_133 = lean_uint64_shift_right(x_131, x_132);
x_134 = lean_uint64_xor(x_131, x_133);
x_135 = 16;
x_136 = lean_uint64_shift_right(x_134, x_135);
x_137 = lean_uint64_xor(x_134, x_136);
x_138 = lean_uint64_to_usize(x_137);
x_139 = lean_usize_of_nat(x_130);
lean_dec(x_130);
x_140 = 1;
x_141 = lean_usize_sub(x_139, x_140);
x_142 = lean_usize_land(x_138, x_141);
x_143 = lean_array_uget(x_116, x_142);
lean_inc(x_143);
lean_inc(x_4);
lean_inc(x_122);
x_144 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_122, x_4, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_150; uint8_t x_155; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_inc(x_5);
lean_inc(x_114);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_114);
lean_ctor_set(x_145, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_146 = x_5;
} else {
 lean_dec_ref(x_5);
 x_146 = lean_box(0);
}
x_162 = l_Std_Sat_AIG_getConstant___redArg(x_145, x_112);
lean_dec(x_112);
x_163 = l_Std_Sat_AIG_getConstant___redArg(x_145, x_113);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_164 = x_113;
} else {
 lean_dec_ref(x_113);
 x_164 = lean_box(0);
}
if (lean_obj_tag(x_162) == 0)
{
lean_dec(x_146);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_165; 
x_165 = lean_nat_dec_eq(x_117, x_119);
lean_dec(x_119);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_173; 
lean_dec(x_145);
lean_dec(x_117);
x_166 = lean_array_get_size(x_114);
lean_inc(x_143);
lean_inc(x_4);
lean_inc(x_122);
x_173 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_122, x_4, x_143);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec(x_122);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_add(x_115, x_174);
lean_dec(x_115);
lean_inc(x_166);
lean_inc(x_4);
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_4);
lean_ctor_set(x_176, 1, x_166);
lean_ctor_set(x_176, 2, x_143);
x_177 = lean_array_uset(x_116, x_142, x_176);
x_178 = lean_unsigned_to_nat(4u);
x_179 = lean_nat_mul(x_175, x_178);
x_180 = lean_unsigned_to_nat(3u);
x_181 = lean_nat_div(x_179, x_180);
lean_dec(x_179);
x_182 = lean_array_get_size(x_177);
x_183 = lean_nat_dec_le(x_181, x_182);
lean_dec(x_182);
lean_dec(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_184, 0, lean_box(0));
lean_closure_set(x_184, 1, x_1);
x_185 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_184, x_177);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_175);
lean_ctor_set(x_186, 1, x_185);
x_167 = x_186;
goto block_172;
}
else
{
lean_object* x_187; 
lean_dec(x_1);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_175);
lean_ctor_set(x_187, 1, x_177);
x_167 = x_187;
goto block_172;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_1);
x_188 = lean_box(0);
x_189 = lean_array_uset(x_116, x_142, x_188);
lean_inc(x_166);
lean_inc(x_4);
x_190 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_122, x_4, x_166, x_143);
x_191 = lean_array_uset(x_189, x_142, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_115);
lean_ctor_set(x_192, 1, x_191);
x_167 = x_192;
goto block_172;
}
block_172:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_array_push(x_114, x_4);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
if (lean_is_scalar(x_164)) {
 x_170 = lean_alloc_ctor(0, 1, 1);
} else {
 x_170 = x_164;
}
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_165);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
else
{
uint8_t x_193; 
lean_dec(x_164);
lean_dec(x_143);
lean_dec(x_4);
lean_dec(x_122);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_193 = 0;
if (x_118 == 0)
{
if (x_120 == 0)
{
x_155 = x_165;
goto block_158;
}
else
{
lean_dec(x_117);
x_150 = x_193;
goto block_154;
}
}
else
{
if (x_120 == 0)
{
lean_dec(x_117);
x_150 = x_193;
goto block_154;
}
else
{
x_155 = x_165;
goto block_158;
}
}
}
}
else
{
lean_object* x_194; uint8_t x_195; 
lean_dec(x_143);
lean_dec(x_4);
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_194 = lean_ctor_get(x_163, 0);
lean_inc(x_194);
lean_dec(x_163);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_dec(x_164);
lean_dec(x_117);
goto block_161;
}
else
{
lean_object* x_196; lean_object* x_197; 
if (lean_is_scalar(x_164)) {
 x_196 = lean_alloc_ctor(0, 1, 1);
} else {
 x_196 = x_164;
}
lean_ctor_set(x_196, 0, x_117);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_118);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_145);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; uint8_t x_199; 
lean_dec(x_164);
lean_dec(x_143);
lean_dec(x_4);
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_198 = lean_ctor_get(x_162, 0);
lean_inc(x_198);
lean_dec(x_162);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_dec(x_163);
lean_dec(x_146);
lean_dec(x_119);
goto block_161;
}
else
{
if (lean_obj_tag(x_163) == 0)
{
goto block_149;
}
else
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_163, 0);
lean_inc(x_200);
lean_dec(x_163);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_dec(x_146);
lean_dec(x_119);
goto block_161;
}
else
{
goto block_149;
}
}
}
}
block_149:
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_119);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_120);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
block_154:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_150);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
block_158:
{
if (x_155 == 0)
{
lean_dec(x_117);
x_150 = x_155;
goto block_154;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_117);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_118);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
block_161:
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_145);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_143);
lean_dec(x_4);
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_1);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_202 = x_113;
} else {
 lean_dec_ref(x_113);
 x_202 = lean_box(0);
}
x_203 = lean_ctor_get(x_144, 0);
lean_inc(x_203);
lean_dec(x_144);
lean_inc(x_5);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_114);
lean_ctor_set(x_204, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_205 = x_5;
} else {
 lean_dec_ref(x_5);
 x_205 = lean_box(0);
}
x_206 = 0;
if (lean_is_scalar(x_202)) {
 x_207 = lean_alloc_ctor(0, 1, 1);
} else {
 x_207 = x_202;
}
lean_ctor_set(x_207, 0, x_203);
lean_ctor_set_uint8(x_207, sizeof(void*)*1, x_206);
if (lean_is_scalar(x_205)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_205;
}
lean_ctor_set(x_208, 0, x_204);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; size_t x_237; size_t x_238; size_t x_239; size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; 
x_209 = lean_ctor_get(x_4, 0);
x_210 = lean_ctor_get(x_4, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_4);
x_211 = lean_ctor_get(x_3, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_212 = x_3;
} else {
 lean_dec_ref(x_3);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_5, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_5, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_209, 0);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_209, sizeof(void*)*1);
x_217 = lean_ctor_get(x_210, 0);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_210, sizeof(void*)*1);
x_219 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_219, 0, x_2);
x_220 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_220, 0, x_219);
x_221 = lean_unsigned_to_nat(2u);
x_222 = lean_nat_mul(x_215, x_221);
x_223 = l_Bool_toNat(x_216);
x_224 = lean_nat_lor(x_222, x_223);
lean_dec(x_223);
lean_dec(x_222);
x_225 = lean_nat_mul(x_217, x_221);
x_226 = l_Bool_toNat(x_218);
x_227 = lean_nat_lor(x_225, x_226);
lean_dec(x_226);
lean_dec(x_225);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_array_get_size(x_214);
lean_inc(x_228);
lean_inc(x_1);
x_230 = l_Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_547_(x_1, x_228);
x_231 = 32;
x_232 = lean_uint64_shift_right(x_230, x_231);
x_233 = lean_uint64_xor(x_230, x_232);
x_234 = 16;
x_235 = lean_uint64_shift_right(x_233, x_234);
x_236 = lean_uint64_xor(x_233, x_235);
x_237 = lean_uint64_to_usize(x_236);
x_238 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_239 = 1;
x_240 = lean_usize_sub(x_238, x_239);
x_241 = lean_usize_land(x_237, x_240);
x_242 = lean_array_uget(x_214, x_241);
lean_inc(x_242);
lean_inc(x_228);
lean_inc(x_220);
x_243 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_220, x_228, x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_249; uint8_t x_254; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_inc(x_5);
lean_inc(x_211);
if (lean_is_scalar(x_212)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_212;
}
lean_ctor_set(x_244, 0, x_211);
lean_ctor_set(x_244, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_245 = x_5;
} else {
 lean_dec_ref(x_5);
 x_245 = lean_box(0);
}
x_261 = l_Std_Sat_AIG_getConstant___redArg(x_244, x_209);
lean_dec(x_209);
x_262 = l_Std_Sat_AIG_getConstant___redArg(x_244, x_210);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_263 = x_210;
} else {
 lean_dec_ref(x_210);
 x_263 = lean_box(0);
}
if (lean_obj_tag(x_261) == 0)
{
lean_dec(x_245);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_264; 
x_264 = lean_nat_dec_eq(x_215, x_217);
lean_dec(x_217);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_272; 
lean_dec(x_244);
lean_dec(x_215);
x_265 = lean_array_get_size(x_211);
lean_inc(x_242);
lean_inc(x_228);
lean_inc(x_220);
x_272 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_220, x_228, x_242);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec(x_220);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_add(x_213, x_273);
lean_dec(x_213);
lean_inc(x_265);
lean_inc(x_228);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_228);
lean_ctor_set(x_275, 1, x_265);
lean_ctor_set(x_275, 2, x_242);
x_276 = lean_array_uset(x_214, x_241, x_275);
x_277 = lean_unsigned_to_nat(4u);
x_278 = lean_nat_mul(x_274, x_277);
x_279 = lean_unsigned_to_nat(3u);
x_280 = lean_nat_div(x_278, x_279);
lean_dec(x_278);
x_281 = lean_array_get_size(x_276);
x_282 = lean_nat_dec_le(x_280, x_281);
lean_dec(x_281);
lean_dec(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_alloc_closure((void*)(l_Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_547____boxed), 3, 2);
lean_closure_set(x_283, 0, lean_box(0));
lean_closure_set(x_283, 1, x_1);
x_284 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_283, x_276);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_274);
lean_ctor_set(x_285, 1, x_284);
x_266 = x_285;
goto block_271;
}
else
{
lean_object* x_286; 
lean_dec(x_1);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_274);
lean_ctor_set(x_286, 1, x_276);
x_266 = x_286;
goto block_271;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_1);
x_287 = lean_box(0);
x_288 = lean_array_uset(x_214, x_241, x_287);
lean_inc(x_265);
lean_inc(x_228);
x_289 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_220, x_228, x_265, x_242);
x_290 = lean_array_uset(x_288, x_241, x_289);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_213);
lean_ctor_set(x_291, 1, x_290);
x_266 = x_291;
goto block_271;
}
block_271:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_array_push(x_211, x_228);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
if (lean_is_scalar(x_263)) {
 x_269 = lean_alloc_ctor(0, 1, 1);
} else {
 x_269 = x_263;
}
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_264);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
else
{
uint8_t x_292; 
lean_dec(x_263);
lean_dec(x_242);
lean_dec(x_228);
lean_dec(x_220);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_1);
x_292 = 0;
if (x_216 == 0)
{
if (x_218 == 0)
{
x_254 = x_264;
goto block_257;
}
else
{
lean_dec(x_215);
x_249 = x_292;
goto block_253;
}
}
else
{
if (x_218 == 0)
{
lean_dec(x_215);
x_249 = x_292;
goto block_253;
}
else
{
x_254 = x_264;
goto block_257;
}
}
}
}
else
{
lean_object* x_293; uint8_t x_294; 
lean_dec(x_242);
lean_dec(x_228);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_1);
x_293 = lean_ctor_get(x_262, 0);
lean_inc(x_293);
lean_dec(x_262);
x_294 = lean_unbox(x_293);
lean_dec(x_293);
if (x_294 == 0)
{
lean_dec(x_263);
lean_dec(x_215);
goto block_260;
}
else
{
lean_object* x_295; lean_object* x_296; 
if (lean_is_scalar(x_263)) {
 x_295 = lean_alloc_ctor(0, 1, 1);
} else {
 x_295 = x_263;
}
lean_ctor_set(x_295, 0, x_215);
lean_ctor_set_uint8(x_295, sizeof(void*)*1, x_216);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_244);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
lean_object* x_297; uint8_t x_298; 
lean_dec(x_263);
lean_dec(x_242);
lean_dec(x_228);
lean_dec(x_220);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_1);
x_297 = lean_ctor_get(x_261, 0);
lean_inc(x_297);
lean_dec(x_261);
x_298 = lean_unbox(x_297);
lean_dec(x_297);
if (x_298 == 0)
{
lean_dec(x_262);
lean_dec(x_245);
lean_dec(x_217);
goto block_260;
}
else
{
if (lean_obj_tag(x_262) == 0)
{
goto block_248;
}
else
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_262, 0);
lean_inc(x_299);
lean_dec(x_262);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
lean_dec(x_245);
lean_dec(x_217);
goto block_260;
}
else
{
goto block_248;
}
}
}
}
block_248:
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_246, 0, x_217);
lean_ctor_set_uint8(x_246, sizeof(void*)*1, x_218);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
block_253:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_unsigned_to_nat(0u);
x_251 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set_uint8(x_251, sizeof(void*)*1, x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_244);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
block_257:
{
if (x_254 == 0)
{
lean_dec(x_215);
x_249 = x_254;
goto block_253;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_255, 0, x_215);
lean_ctor_set_uint8(x_255, sizeof(void*)*1, x_216);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_244);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
block_260:
{
lean_object* x_258; lean_object* x_259; 
x_258 = l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0;
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_244);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_242);
lean_dec(x_228);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_209);
lean_dec(x_1);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_301 = x_210;
} else {
 lean_dec_ref(x_210);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_243, 0);
lean_inc(x_302);
lean_dec(x_243);
lean_inc(x_5);
if (lean_is_scalar(x_212)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_212;
}
lean_ctor_set(x_303, 0, x_211);
lean_ctor_set(x_303, 1, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_304 = x_5;
} else {
 lean_dec_ref(x_5);
 x_304 = lean_box(0);
}
x_305 = 0;
if (lean_is_scalar(x_301)) {
 x_306 = lean_alloc_ctor(0, 1, 1);
} else {
 x_306 = x_301;
}
lean_ctor_set(x_306, 0, x_302);
lean_ctor_set_uint8(x_306, sizeof(void*)*1, x_305);
if (lean_is_scalar(x_304)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_304;
}
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_306);
return x_307;
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
