// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: Init Lean.Expr
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
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_new;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_keyIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_hasResultFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_store(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_ReplaceImpl_Cache_hasResultFor(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_cacheSize;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_keyIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object*, lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_resultIdx(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_resultIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object*, lean_object*, lean_object*);
static size_t _init_l_Lean_Expr_ReplaceImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8191;
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(16382u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_keyIdx(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; 
x_2 = lean_ptr_addr(x_1);
x_3 = 8191;
x_4 = lean_usize_mod(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_keyIdx___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_ReplaceImpl_Cache_keyIdx(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_resultIdx(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; size_t x_5; 
x_2 = lean_ptr_addr(x_1);
x_3 = 8191;
x_4 = lean_usize_mod(x_2, x_3);
x_5 = lean_usize_add(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_resultIdx___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_ReplaceImpl_Cache_resultIdx(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_ReplaceImpl_Cache_hasResultFor(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; size_t x_7; uint8_t x_8; 
x_3 = lean_ptr_addr(x_2);
x_4 = 8191;
x_5 = lean_usize_mod(x_3, x_4);
x_6 = lean_array_uget(x_1, x_5);
x_7 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_8 = lean_usize_dec_eq(x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_hasResultFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_hasResultFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_ptr_addr(x_2);
x_4 = 8191;
x_5 = lean_usize_mod(x_3, x_4);
x_6 = lean_usize_add(x_5, x_4);
x_7 = lean_array_uget(x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_getResultFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_getResultFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_Cache_store(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_ptr_addr(x_2);
x_5 = 8191;
x_6 = lean_usize_mod(x_4, x_5);
x_7 = lean_array_uset(x_1, x_6, x_2);
x_8 = lean_usize_add(x_6, x_5);
x_9 = lean_array_uset(x_7, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ptr_addr(x_1);
x_5 = 8191;
x_6 = lean_usize_mod(x_4, x_5);
x_7 = lean_array_uset(x_3, x_6, x_1);
x_8 = lean_usize_add(x_6, x_5);
lean_inc(x_2);
x_9 = lean_array_uset(x_7, x_8, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ptr_addr(x_2);
x_5 = 8191;
x_6 = lean_usize_mod(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_9 = lean_usize_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_1);
lean_inc(x_2);
x_10 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_10) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_11, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_12);
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_12, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_2);
x_20 = lean_array_uset(x_19, x_6, x_2);
x_21 = lean_usize_add(x_6, x_5);
x_22 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_23 = lean_ptr_addr(x_14);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_2);
x_25 = l_Lean_Expr_app___override(x_14, x_18);
lean_inc(x_25);
x_26 = lean_array_uset(x_20, x_21, x_25);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_28 = lean_ptr_addr(x_18);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_14, x_18);
lean_inc(x_30);
x_31 = lean_array_uset(x_20, x_21, x_30);
lean_ctor_set(x_16, 1, x_31);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_14);
lean_inc(x_2);
x_32 = lean_array_uset(x_20, x_21, x_2);
lean_ctor_set(x_16, 1, x_32);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; size_t x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
lean_inc(x_2);
x_35 = lean_array_uset(x_34, x_6, x_2);
x_36 = lean_usize_add(x_6, x_5);
x_37 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_38 = lean_ptr_addr(x_14);
x_39 = lean_usize_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_2);
x_40 = l_Lean_Expr_app___override(x_14, x_33);
lean_inc(x_40);
x_41 = lean_array_uset(x_35, x_36, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_44 = lean_ptr_addr(x_33);
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_46 = l_Lean_Expr_app___override(x_14, x_33);
lean_inc(x_46);
x_47 = lean_array_uset(x_35, x_36, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_14);
lean_inc(x_2);
x_49 = lean_array_uset(x_35, x_36, x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
case 6:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_52);
lean_inc(x_1);
x_55 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_52, x_3);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_53);
x_58 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_53, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; size_t x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_array_uset(x_61, x_6, x_2);
x_63 = lean_usize_add(x_6, x_5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_64 = l_Lean_Expr_lam___override(x_51, x_52, x_53, x_54);
x_65 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_66 = lean_ptr_addr(x_56);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
lean_dec(x_53);
x_68 = l_Lean_Expr_lam___override(x_51, x_56, x_60, x_54);
lean_inc(x_68);
x_69 = lean_array_uset(x_62, x_63, x_68);
lean_ctor_set(x_58, 1, x_69);
lean_ctor_set(x_58, 0, x_68);
return x_58;
}
else
{
size_t x_70; size_t x_71; uint8_t x_72; 
x_70 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_71 = lean_ptr_addr(x_60);
x_72 = lean_usize_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
x_73 = l_Lean_Expr_lam___override(x_51, x_56, x_60, x_54);
lean_inc(x_73);
x_74 = lean_array_uset(x_62, x_63, x_73);
lean_ctor_set(x_58, 1, x_74);
lean_ctor_set(x_58, 0, x_73);
return x_58;
}
else
{
uint8_t x_75; 
x_75 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_54, x_54);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
x_76 = l_Lean_Expr_lam___override(x_51, x_56, x_60, x_54);
lean_inc(x_76);
x_77 = lean_array_uset(x_62, x_63, x_76);
lean_ctor_set(x_58, 1, x_77);
lean_ctor_set(x_58, 0, x_76);
return x_58;
}
else
{
lean_object* x_78; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_51);
lean_inc(x_64);
x_78 = lean_array_uset(x_62, x_63, x_64);
lean_ctor_set(x_58, 1, x_78);
lean_ctor_set(x_58, 0, x_64);
return x_58;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; size_t x_84; size_t x_85; uint8_t x_86; 
x_79 = lean_ctor_get(x_58, 0);
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_58);
x_81 = lean_array_uset(x_80, x_6, x_2);
x_82 = lean_usize_add(x_6, x_5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_83 = l_Lean_Expr_lam___override(x_51, x_52, x_53, x_54);
x_84 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_85 = lean_ptr_addr(x_56);
x_86 = lean_usize_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_83);
lean_dec(x_53);
x_87 = l_Lean_Expr_lam___override(x_51, x_56, x_79, x_54);
lean_inc(x_87);
x_88 = lean_array_uset(x_81, x_82, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
size_t x_90; size_t x_91; uint8_t x_92; 
x_90 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_91 = lean_ptr_addr(x_79);
x_92 = lean_usize_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
x_93 = l_Lean_Expr_lam___override(x_51, x_56, x_79, x_54);
lean_inc(x_93);
x_94 = lean_array_uset(x_81, x_82, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
uint8_t x_96; 
x_96 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_54, x_54);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
x_97 = l_Lean_Expr_lam___override(x_51, x_56, x_79, x_54);
lean_inc(x_97);
x_98 = lean_array_uset(x_81, x_82, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_79);
lean_dec(x_56);
lean_dec(x_51);
lean_inc(x_83);
x_100 = lean_array_uset(x_81, x_82, x_83);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_83);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
case 7:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_102 = lean_ctor_get(x_2, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_2, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 2);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_103);
lean_inc(x_1);
x_106 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_103, x_3);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_104);
x_109 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_104, x_108);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; lean_object* x_115; size_t x_116; size_t x_117; uint8_t x_118; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
x_113 = lean_array_uset(x_112, x_6, x_2);
x_114 = lean_usize_add(x_6, x_5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
x_115 = l_Lean_Expr_forallE___override(x_102, x_103, x_104, x_105);
x_116 = lean_ptr_addr(x_103);
lean_dec(x_103);
x_117 = lean_ptr_addr(x_107);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_115);
lean_dec(x_104);
x_119 = l_Lean_Expr_forallE___override(x_102, x_107, x_111, x_105);
lean_inc(x_119);
x_120 = lean_array_uset(x_113, x_114, x_119);
lean_ctor_set(x_109, 1, x_120);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_121; size_t x_122; uint8_t x_123; 
x_121 = lean_ptr_addr(x_104);
lean_dec(x_104);
x_122 = lean_ptr_addr(x_111);
x_123 = lean_usize_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_115);
x_124 = l_Lean_Expr_forallE___override(x_102, x_107, x_111, x_105);
lean_inc(x_124);
x_125 = lean_array_uset(x_113, x_114, x_124);
lean_ctor_set(x_109, 1, x_125);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
else
{
uint8_t x_126; 
x_126 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_105, x_105);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
x_127 = l_Lean_Expr_forallE___override(x_102, x_107, x_111, x_105);
lean_inc(x_127);
x_128 = lean_array_uset(x_113, x_114, x_127);
lean_ctor_set(x_109, 1, x_128);
lean_ctor_set(x_109, 0, x_127);
return x_109;
}
else
{
lean_object* x_129; 
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_102);
lean_inc(x_115);
x_129 = lean_array_uset(x_113, x_114, x_115);
lean_ctor_set(x_109, 1, x_129);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; lean_object* x_134; size_t x_135; size_t x_136; uint8_t x_137; 
x_130 = lean_ctor_get(x_109, 0);
x_131 = lean_ctor_get(x_109, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_109);
x_132 = lean_array_uset(x_131, x_6, x_2);
x_133 = lean_usize_add(x_6, x_5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
x_134 = l_Lean_Expr_forallE___override(x_102, x_103, x_104, x_105);
x_135 = lean_ptr_addr(x_103);
lean_dec(x_103);
x_136 = lean_ptr_addr(x_107);
x_137 = lean_usize_dec_eq(x_135, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_134);
lean_dec(x_104);
x_138 = l_Lean_Expr_forallE___override(x_102, x_107, x_130, x_105);
lean_inc(x_138);
x_139 = lean_array_uset(x_132, x_133, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
else
{
size_t x_141; size_t x_142; uint8_t x_143; 
x_141 = lean_ptr_addr(x_104);
lean_dec(x_104);
x_142 = lean_ptr_addr(x_130);
x_143 = lean_usize_dec_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_134);
x_144 = l_Lean_Expr_forallE___override(x_102, x_107, x_130, x_105);
lean_inc(x_144);
x_145 = lean_array_uset(x_132, x_133, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
else
{
uint8_t x_147; 
x_147 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_105, x_105);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_134);
x_148 = l_Lean_Expr_forallE___override(x_102, x_107, x_130, x_105);
lean_inc(x_148);
x_149 = lean_array_uset(x_132, x_133, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_130);
lean_dec(x_107);
lean_dec(x_102);
lean_inc(x_134);
x_151 = lean_array_uset(x_132, x_133, x_134);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_134);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
case 8:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_153 = lean_ctor_get(x_2, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_2, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 3);
lean_inc(x_156);
x_157 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_154);
lean_inc(x_1);
x_158 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_154, x_3);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_155);
lean_inc(x_1);
x_161 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_155, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_156);
x_164 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_156, x_163);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; size_t x_171; uint8_t x_172; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_2);
x_168 = lean_array_uset(x_167, x_6, x_2);
x_169 = lean_usize_add(x_6, x_5);
x_170 = lean_ptr_addr(x_154);
lean_dec(x_154);
x_171 = lean_ptr_addr(x_159);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_2);
x_173 = l_Lean_Expr_letE___override(x_153, x_159, x_162, x_166, x_157);
lean_inc(x_173);
x_174 = lean_array_uset(x_168, x_169, x_173);
lean_ctor_set(x_164, 1, x_174);
lean_ctor_set(x_164, 0, x_173);
return x_164;
}
else
{
size_t x_175; size_t x_176; uint8_t x_177; 
x_175 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_176 = lean_ptr_addr(x_162);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_156);
lean_dec(x_2);
x_178 = l_Lean_Expr_letE___override(x_153, x_159, x_162, x_166, x_157);
lean_inc(x_178);
x_179 = lean_array_uset(x_168, x_169, x_178);
lean_ctor_set(x_164, 1, x_179);
lean_ctor_set(x_164, 0, x_178);
return x_164;
}
else
{
size_t x_180; size_t x_181; uint8_t x_182; 
x_180 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_181 = lean_ptr_addr(x_166);
x_182 = lean_usize_dec_eq(x_180, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_2);
x_183 = l_Lean_Expr_letE___override(x_153, x_159, x_162, x_166, x_157);
lean_inc(x_183);
x_184 = lean_array_uset(x_168, x_169, x_183);
lean_ctor_set(x_164, 1, x_184);
lean_ctor_set(x_164, 0, x_183);
return x_164;
}
else
{
lean_object* x_185; 
lean_dec(x_166);
lean_dec(x_162);
lean_dec(x_159);
lean_dec(x_153);
lean_inc(x_2);
x_185 = lean_array_uset(x_168, x_169, x_2);
lean_ctor_set(x_164, 1, x_185);
lean_ctor_set(x_164, 0, x_2);
return x_164;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; size_t x_189; size_t x_190; size_t x_191; uint8_t x_192; 
x_186 = lean_ctor_get(x_164, 0);
x_187 = lean_ctor_get(x_164, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_164);
lean_inc(x_2);
x_188 = lean_array_uset(x_187, x_6, x_2);
x_189 = lean_usize_add(x_6, x_5);
x_190 = lean_ptr_addr(x_154);
lean_dec(x_154);
x_191 = lean_ptr_addr(x_159);
x_192 = lean_usize_dec_eq(x_190, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_2);
x_193 = l_Lean_Expr_letE___override(x_153, x_159, x_162, x_186, x_157);
lean_inc(x_193);
x_194 = lean_array_uset(x_188, x_189, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
else
{
size_t x_196; size_t x_197; uint8_t x_198; 
x_196 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_197 = lean_ptr_addr(x_162);
x_198 = lean_usize_dec_eq(x_196, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_156);
lean_dec(x_2);
x_199 = l_Lean_Expr_letE___override(x_153, x_159, x_162, x_186, x_157);
lean_inc(x_199);
x_200 = lean_array_uset(x_188, x_189, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
else
{
size_t x_202; size_t x_203; uint8_t x_204; 
x_202 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_203 = lean_ptr_addr(x_186);
x_204 = lean_usize_dec_eq(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_2);
x_205 = l_Lean_Expr_letE___override(x_153, x_159, x_162, x_186, x_157);
lean_inc(x_205);
x_206 = lean_array_uset(x_188, x_189, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_186);
lean_dec(x_162);
lean_dec(x_159);
lean_dec(x_153);
lean_inc(x_2);
x_208 = lean_array_uset(x_188, x_189, x_2);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_2);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
case 10:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_2, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
lean_inc(x_211);
x_212 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_211, x_3);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; size_t x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_2);
x_216 = lean_array_uset(x_215, x_6, x_2);
x_217 = lean_usize_add(x_6, x_5);
x_218 = lean_ptr_addr(x_211);
lean_dec(x_211);
x_219 = lean_ptr_addr(x_214);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_2);
x_221 = l_Lean_Expr_mdata___override(x_210, x_214);
lean_inc(x_221);
x_222 = lean_array_uset(x_216, x_217, x_221);
lean_ctor_set(x_212, 1, x_222);
lean_ctor_set(x_212, 0, x_221);
return x_212;
}
else
{
lean_object* x_223; 
lean_dec(x_214);
lean_dec(x_210);
lean_inc(x_2);
x_223 = lean_array_uset(x_216, x_217, x_2);
lean_ctor_set(x_212, 1, x_223);
lean_ctor_set(x_212, 0, x_2);
return x_212;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; size_t x_227; size_t x_228; size_t x_229; uint8_t x_230; 
x_224 = lean_ctor_get(x_212, 0);
x_225 = lean_ctor_get(x_212, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_212);
lean_inc(x_2);
x_226 = lean_array_uset(x_225, x_6, x_2);
x_227 = lean_usize_add(x_6, x_5);
x_228 = lean_ptr_addr(x_211);
lean_dec(x_211);
x_229 = lean_ptr_addr(x_224);
x_230 = lean_usize_dec_eq(x_228, x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_2);
x_231 = l_Lean_Expr_mdata___override(x_210, x_224);
lean_inc(x_231);
x_232 = lean_array_uset(x_226, x_227, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_224);
lean_dec(x_210);
lean_inc(x_2);
x_234 = lean_array_uset(x_226, x_227, x_2);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_2);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
case 11:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_2, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_2, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_2, 2);
lean_inc(x_238);
lean_inc(x_238);
x_239 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_238, x_3);
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; size_t x_244; size_t x_245; size_t x_246; uint8_t x_247; 
x_241 = lean_ctor_get(x_239, 0);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_2);
x_243 = lean_array_uset(x_242, x_6, x_2);
x_244 = lean_usize_add(x_6, x_5);
x_245 = lean_ptr_addr(x_238);
lean_dec(x_238);
x_246 = lean_ptr_addr(x_241);
x_247 = lean_usize_dec_eq(x_245, x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_2);
x_248 = l_Lean_Expr_proj___override(x_236, x_237, x_241);
lean_inc(x_248);
x_249 = lean_array_uset(x_243, x_244, x_248);
lean_ctor_set(x_239, 1, x_249);
lean_ctor_set(x_239, 0, x_248);
return x_239;
}
else
{
lean_object* x_250; 
lean_dec(x_241);
lean_dec(x_237);
lean_dec(x_236);
lean_inc(x_2);
x_250 = lean_array_uset(x_243, x_244, x_2);
lean_ctor_set(x_239, 1, x_250);
lean_ctor_set(x_239, 0, x_2);
return x_239;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; size_t x_254; size_t x_255; size_t x_256; uint8_t x_257; 
x_251 = lean_ctor_get(x_239, 0);
x_252 = lean_ctor_get(x_239, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_239);
lean_inc(x_2);
x_253 = lean_array_uset(x_252, x_6, x_2);
x_254 = lean_usize_add(x_6, x_5);
x_255 = lean_ptr_addr(x_238);
lean_dec(x_238);
x_256 = lean_ptr_addr(x_251);
x_257 = lean_usize_dec_eq(x_255, x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_2);
x_258 = l_Lean_Expr_proj___override(x_236, x_237, x_251);
lean_inc(x_258);
x_259 = lean_array_uset(x_253, x_254, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_251);
lean_dec(x_237);
lean_dec(x_236);
lean_inc(x_2);
x_261 = lean_array_uset(x_253, x_254, x_2);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_2);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
default: 
{
lean_object* x_263; 
lean_dec(x_1);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_2);
lean_ctor_set(x_263, 1, x_3);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; size_t x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_1);
x_264 = lean_ctor_get(x_10, 0);
lean_inc(x_264);
lean_dec(x_10);
x_265 = lean_array_uset(x_3, x_6, x_2);
x_266 = lean_usize_add(x_6, x_5);
lean_inc(x_264);
x_267 = lean_array_uset(x_265, x_266, x_264);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
else
{
size_t x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_2);
lean_dec(x_1);
x_269 = lean_usize_add(x_6, x_5);
x_270 = lean_array_uget(x_3, x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_3);
return x_271;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_ReplaceImpl_Cache_new;
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Expr_replaceNoCache(x_1, x_4);
lean_inc(x_5);
x_7 = l_Lean_Expr_replaceNoCache(x_1, x_5);
x_8 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = l_Lean_Expr_app___override(x_6, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_13 = lean_ptr_addr(x_7);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = l_Lean_Expr_app___override(x_6, x_7);
return x_15;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_17);
lean_inc(x_1);
x_20 = l_Lean_Expr_replaceNoCache(x_1, x_17);
lean_inc(x_18);
x_21 = l_Lean_Expr_replaceNoCache(x_1, x_18);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_22 = l_Lean_Expr_lam___override(x_16, x_17, x_18, x_19);
x_23 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_24 = lean_ptr_addr(x_20);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_18);
x_26 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_26;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_28 = lean_ptr_addr(x_21);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_22);
x_30 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_19, x_19);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
x_32 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_32;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
return x_22;
}
}
}
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_34);
lean_inc(x_1);
x_37 = l_Lean_Expr_replaceNoCache(x_1, x_34);
lean_inc(x_35);
x_38 = l_Lean_Expr_replaceNoCache(x_1, x_35);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_39 = l_Lean_Expr_forallE___override(x_33, x_34, x_35, x_36);
x_40 = lean_ptr_addr(x_34);
lean_dec(x_34);
x_41 = lean_ptr_addr(x_37);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_35);
x_43 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_43;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_35);
lean_dec(x_35);
x_45 = lean_ptr_addr(x_38);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_39);
x_47 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_36, x_36);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_39);
x_49 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_49;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
return x_39;
}
}
}
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; uint8_t x_60; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_51);
lean_inc(x_1);
x_55 = l_Lean_Expr_replaceNoCache(x_1, x_51);
lean_inc(x_52);
lean_inc(x_1);
x_56 = l_Lean_Expr_replaceNoCache(x_1, x_52);
lean_inc(x_53);
x_57 = l_Lean_Expr_replaceNoCache(x_1, x_53);
x_58 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_59 = lean_ptr_addr(x_55);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_2);
x_61 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_61;
}
else
{
size_t x_62; size_t x_63; uint8_t x_64; 
x_62 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_63 = lean_ptr_addr(x_56);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_53);
lean_dec(x_2);
x_65 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_65;
}
else
{
size_t x_66; size_t x_67; uint8_t x_68; 
x_66 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_67 = lean_ptr_addr(x_57);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_2);
x_69 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_69;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_50);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_inc(x_71);
x_72 = l_Lean_Expr_replaceNoCache(x_1, x_71);
x_73 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_74 = lean_ptr_addr(x_72);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_2);
x_76 = l_Lean_Expr_mdata___override(x_70, x_72);
return x_76;
}
else
{
lean_dec(x_72);
lean_dec(x_70);
return x_2;
}
}
case 11:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; uint8_t x_83; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
lean_inc(x_79);
x_80 = l_Lean_Expr_replaceNoCache(x_1, x_79);
x_81 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_82 = lean_ptr_addr(x_80);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_2);
x_84 = l_Lean_Expr_proj___override(x_77, x_78, x_80);
return x_84;
}
else
{
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
return x_2;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
lean_dec(x_3);
return x_85;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_cacheSize = _init_l_Lean_Expr_ReplaceImpl_cacheSize();
l_Lean_Expr_ReplaceImpl_Cache_new = _init_l_Lean_Expr_ReplaceImpl_Cache_new();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_Cache_new);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
