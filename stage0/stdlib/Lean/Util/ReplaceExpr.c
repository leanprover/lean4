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
size_t lean_usize_shift_right(size_t, size_t);
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
x_1 = 8192;
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_Cache_new() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(16384u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_Cache_keyIdx(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; size_t x_5; size_t x_6; 
x_2 = lean_ptr_addr(x_1);
x_3 = 4;
x_4 = lean_usize_shift_right(x_2, x_3);
x_5 = 8192;
x_6 = lean_usize_mod(x_4, x_5);
return x_6;
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
size_t x_2; size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; 
x_2 = lean_ptr_addr(x_1);
x_3 = 4;
x_4 = lean_usize_shift_right(x_2, x_3);
x_5 = 8192;
x_6 = lean_usize_mod(x_4, x_5);
x_7 = lean_usize_add(x_6, x_5);
return x_7;
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
size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_3 = lean_ptr_addr(x_2);
x_4 = 4;
x_5 = lean_usize_shift_right(x_3, x_4);
x_6 = 8192;
x_7 = lean_usize_mod(x_5, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = lean_usize_dec_eq(x_3, x_9);
return x_10;
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
size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ptr_addr(x_2);
x_4 = 4;
x_5 = lean_usize_shift_right(x_3, x_4);
x_6 = 8192;
x_7 = lean_usize_mod(x_5, x_6);
x_8 = lean_usize_add(x_7, x_6);
x_9 = lean_array_uget(x_1, x_8);
return x_9;
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
size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_4 = lean_ptr_addr(x_2);
x_5 = 4;
x_6 = lean_usize_shift_right(x_4, x_5);
x_7 = 8192;
x_8 = lean_usize_mod(x_6, x_7);
x_9 = lean_array_uset(x_1, x_8, x_2);
x_10 = lean_usize_add(x_8, x_7);
x_11 = lean_array_uset(x_9, x_10, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ptr_addr(x_1);
x_5 = 4;
x_6 = lean_usize_shift_right(x_4, x_5);
x_7 = 8192;
x_8 = lean_usize_mod(x_6, x_7);
x_9 = lean_array_uset(x_3, x_8, x_1);
x_10 = lean_usize_add(x_8, x_7);
lean_inc(x_2);
x_11 = lean_array_uset(x_9, x_10, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
x_4 = lean_ptr_addr(x_2);
x_5 = 4;
x_6 = lean_usize_shift_right(x_4, x_5);
x_7 = 8192;
x_8 = lean_usize_mod(x_6, x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_11 = lean_usize_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_1);
lean_inc(x_2);
x_12 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_13, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_14);
x_18 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_14, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_2);
x_22 = lean_array_uset(x_21, x_8, x_2);
x_23 = lean_usize_add(x_8, x_7);
x_24 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_25 = lean_ptr_addr(x_16);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_2);
x_27 = l_Lean_Expr_app___override(x_16, x_20);
lean_inc(x_27);
x_28 = lean_array_uset(x_22, x_23, x_27);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_30 = lean_ptr_addr(x_20);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_32 = l_Lean_Expr_app___override(x_16, x_20);
lean_inc(x_32);
x_33 = lean_array_uset(x_22, x_23, x_32);
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
else
{
lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_16);
lean_inc(x_2);
x_34 = lean_array_uset(x_22, x_23, x_2);
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; size_t x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
lean_inc(x_2);
x_37 = lean_array_uset(x_36, x_8, x_2);
x_38 = lean_usize_add(x_8, x_7);
x_39 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_40 = lean_ptr_addr(x_16);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_2);
x_42 = l_Lean_Expr_app___override(x_16, x_35);
lean_inc(x_42);
x_43 = lean_array_uset(x_37, x_38, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
size_t x_45; size_t x_46; uint8_t x_47; 
x_45 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_46 = lean_ptr_addr(x_35);
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_48 = l_Lean_Expr_app___override(x_16, x_35);
lean_inc(x_48);
x_49 = lean_array_uset(x_37, x_38, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_35);
lean_dec(x_16);
lean_inc(x_2);
x_51 = lean_array_uset(x_37, x_38, x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_54);
lean_inc(x_1);
x_57 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_54, x_3);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_55);
x_60 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_55, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; size_t x_67; size_t x_68; uint8_t x_69; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
x_64 = lean_array_uset(x_63, x_8, x_2);
x_65 = lean_usize_add(x_8, x_7);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_66 = l_Lean_Expr_lam___override(x_53, x_54, x_55, x_56);
x_67 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_68 = lean_ptr_addr(x_58);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_66);
lean_dec(x_55);
x_70 = l_Lean_Expr_lam___override(x_53, x_58, x_62, x_56);
lean_inc(x_70);
x_71 = lean_array_uset(x_64, x_65, x_70);
lean_ctor_set(x_60, 1, x_71);
lean_ctor_set(x_60, 0, x_70);
return x_60;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_73 = lean_ptr_addr(x_62);
x_74 = lean_usize_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_66);
x_75 = l_Lean_Expr_lam___override(x_53, x_58, x_62, x_56);
lean_inc(x_75);
x_76 = lean_array_uset(x_64, x_65, x_75);
lean_ctor_set(x_60, 1, x_76);
lean_ctor_set(x_60, 0, x_75);
return x_60;
}
else
{
uint8_t x_77; 
x_77 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_56, x_56);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_66);
x_78 = l_Lean_Expr_lam___override(x_53, x_58, x_62, x_56);
lean_inc(x_78);
x_79 = lean_array_uset(x_64, x_65, x_78);
lean_ctor_set(x_60, 1, x_79);
lean_ctor_set(x_60, 0, x_78);
return x_60;
}
else
{
lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_58);
lean_dec(x_53);
lean_inc(x_66);
x_80 = lean_array_uset(x_64, x_65, x_66);
lean_ctor_set(x_60, 1, x_80);
lean_ctor_set(x_60, 0, x_66);
return x_60;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; lean_object* x_85; size_t x_86; size_t x_87; uint8_t x_88; 
x_81 = lean_ctor_get(x_60, 0);
x_82 = lean_ctor_get(x_60, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_60);
x_83 = lean_array_uset(x_82, x_8, x_2);
x_84 = lean_usize_add(x_8, x_7);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_85 = l_Lean_Expr_lam___override(x_53, x_54, x_55, x_56);
x_86 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_87 = lean_ptr_addr(x_58);
x_88 = lean_usize_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_85);
lean_dec(x_55);
x_89 = l_Lean_Expr_lam___override(x_53, x_58, x_81, x_56);
lean_inc(x_89);
x_90 = lean_array_uset(x_83, x_84, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
size_t x_92; size_t x_93; uint8_t x_94; 
x_92 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_93 = lean_ptr_addr(x_81);
x_94 = lean_usize_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
x_95 = l_Lean_Expr_lam___override(x_53, x_58, x_81, x_56);
lean_inc(x_95);
x_96 = lean_array_uset(x_83, x_84, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
else
{
uint8_t x_98; 
x_98 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_56, x_56);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_85);
x_99 = l_Lean_Expr_lam___override(x_53, x_58, x_81, x_56);
lean_inc(x_99);
x_100 = lean_array_uset(x_83, x_84, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_81);
lean_dec(x_58);
lean_dec(x_53);
lean_inc(x_85);
x_102 = lean_array_uset(x_83, x_84, x_85);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_85);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_104 = lean_ctor_get(x_2, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_2, 2);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_105);
lean_inc(x_1);
x_108 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_105, x_3);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_106);
x_111 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_106, x_110);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; lean_object* x_117; size_t x_118; size_t x_119; uint8_t x_120; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
x_115 = lean_array_uset(x_114, x_8, x_2);
x_116 = lean_usize_add(x_8, x_7);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
x_117 = l_Lean_Expr_forallE___override(x_104, x_105, x_106, x_107);
x_118 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_119 = lean_ptr_addr(x_109);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_117);
lean_dec(x_106);
x_121 = l_Lean_Expr_forallE___override(x_104, x_109, x_113, x_107);
lean_inc(x_121);
x_122 = lean_array_uset(x_115, x_116, x_121);
lean_ctor_set(x_111, 1, x_122);
lean_ctor_set(x_111, 0, x_121);
return x_111;
}
else
{
size_t x_123; size_t x_124; uint8_t x_125; 
x_123 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_124 = lean_ptr_addr(x_113);
x_125 = lean_usize_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
x_126 = l_Lean_Expr_forallE___override(x_104, x_109, x_113, x_107);
lean_inc(x_126);
x_127 = lean_array_uset(x_115, x_116, x_126);
lean_ctor_set(x_111, 1, x_127);
lean_ctor_set(x_111, 0, x_126);
return x_111;
}
else
{
uint8_t x_128; 
x_128 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_107, x_107);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_117);
x_129 = l_Lean_Expr_forallE___override(x_104, x_109, x_113, x_107);
lean_inc(x_129);
x_130 = lean_array_uset(x_115, x_116, x_129);
lean_ctor_set(x_111, 1, x_130);
lean_ctor_set(x_111, 0, x_129);
return x_111;
}
else
{
lean_object* x_131; 
lean_dec(x_113);
lean_dec(x_109);
lean_dec(x_104);
lean_inc(x_117);
x_131 = lean_array_uset(x_115, x_116, x_117);
lean_ctor_set(x_111, 1, x_131);
lean_ctor_set(x_111, 0, x_117);
return x_111;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; lean_object* x_136; size_t x_137; size_t x_138; uint8_t x_139; 
x_132 = lean_ctor_get(x_111, 0);
x_133 = lean_ctor_get(x_111, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_111);
x_134 = lean_array_uset(x_133, x_8, x_2);
x_135 = lean_usize_add(x_8, x_7);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
x_136 = l_Lean_Expr_forallE___override(x_104, x_105, x_106, x_107);
x_137 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_138 = lean_ptr_addr(x_109);
x_139 = lean_usize_dec_eq(x_137, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_136);
lean_dec(x_106);
x_140 = l_Lean_Expr_forallE___override(x_104, x_109, x_132, x_107);
lean_inc(x_140);
x_141 = lean_array_uset(x_134, x_135, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
size_t x_143; size_t x_144; uint8_t x_145; 
x_143 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_144 = lean_ptr_addr(x_132);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_136);
x_146 = l_Lean_Expr_forallE___override(x_104, x_109, x_132, x_107);
lean_inc(x_146);
x_147 = lean_array_uset(x_134, x_135, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_107, x_107);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_136);
x_150 = l_Lean_Expr_forallE___override(x_104, x_109, x_132, x_107);
lean_inc(x_150);
x_151 = lean_array_uset(x_134, x_135, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_132);
lean_dec(x_109);
lean_dec(x_104);
lean_inc(x_136);
x_153 = lean_array_uset(x_134, x_135, x_136);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_136);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
case 8:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_155 = lean_ctor_get(x_2, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_2, 3);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_156);
lean_inc(x_1);
x_160 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_156, x_3);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_157);
lean_inc(x_1);
x_163 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_157, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_158);
x_166 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_158, x_165);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; size_t x_173; uint8_t x_174; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_2);
x_170 = lean_array_uset(x_169, x_8, x_2);
x_171 = lean_usize_add(x_8, x_7);
x_172 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_173 = lean_ptr_addr(x_161);
x_174 = lean_usize_dec_eq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_2);
x_175 = l_Lean_Expr_letE___override(x_155, x_161, x_164, x_168, x_159);
lean_inc(x_175);
x_176 = lean_array_uset(x_170, x_171, x_175);
lean_ctor_set(x_166, 1, x_176);
lean_ctor_set(x_166, 0, x_175);
return x_166;
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_157);
lean_dec(x_157);
x_178 = lean_ptr_addr(x_164);
x_179 = lean_usize_dec_eq(x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_158);
lean_dec(x_2);
x_180 = l_Lean_Expr_letE___override(x_155, x_161, x_164, x_168, x_159);
lean_inc(x_180);
x_181 = lean_array_uset(x_170, x_171, x_180);
lean_ctor_set(x_166, 1, x_181);
lean_ctor_set(x_166, 0, x_180);
return x_166;
}
else
{
size_t x_182; size_t x_183; uint8_t x_184; 
x_182 = lean_ptr_addr(x_158);
lean_dec(x_158);
x_183 = lean_ptr_addr(x_168);
x_184 = lean_usize_dec_eq(x_182, x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_2);
x_185 = l_Lean_Expr_letE___override(x_155, x_161, x_164, x_168, x_159);
lean_inc(x_185);
x_186 = lean_array_uset(x_170, x_171, x_185);
lean_ctor_set(x_166, 1, x_186);
lean_ctor_set(x_166, 0, x_185);
return x_166;
}
else
{
lean_object* x_187; 
lean_dec(x_168);
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_155);
lean_inc(x_2);
x_187 = lean_array_uset(x_170, x_171, x_2);
lean_ctor_set(x_166, 1, x_187);
lean_ctor_set(x_166, 0, x_2);
return x_166;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; size_t x_191; size_t x_192; size_t x_193; uint8_t x_194; 
x_188 = lean_ctor_get(x_166, 0);
x_189 = lean_ctor_get(x_166, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_166);
lean_inc(x_2);
x_190 = lean_array_uset(x_189, x_8, x_2);
x_191 = lean_usize_add(x_8, x_7);
x_192 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_193 = lean_ptr_addr(x_161);
x_194 = lean_usize_dec_eq(x_192, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_2);
x_195 = l_Lean_Expr_letE___override(x_155, x_161, x_164, x_188, x_159);
lean_inc(x_195);
x_196 = lean_array_uset(x_190, x_191, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
else
{
size_t x_198; size_t x_199; uint8_t x_200; 
x_198 = lean_ptr_addr(x_157);
lean_dec(x_157);
x_199 = lean_ptr_addr(x_164);
x_200 = lean_usize_dec_eq(x_198, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_158);
lean_dec(x_2);
x_201 = l_Lean_Expr_letE___override(x_155, x_161, x_164, x_188, x_159);
lean_inc(x_201);
x_202 = lean_array_uset(x_190, x_191, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
else
{
size_t x_204; size_t x_205; uint8_t x_206; 
x_204 = lean_ptr_addr(x_158);
lean_dec(x_158);
x_205 = lean_ptr_addr(x_188);
x_206 = lean_usize_dec_eq(x_204, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_2);
x_207 = l_Lean_Expr_letE___override(x_155, x_161, x_164, x_188, x_159);
lean_inc(x_207);
x_208 = lean_array_uset(x_190, x_191, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_188);
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_155);
lean_inc(x_2);
x_210 = lean_array_uset(x_190, x_191, x_2);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_2);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
}
case 10:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_212 = lean_ctor_get(x_2, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_2, 1);
lean_inc(x_213);
lean_inc(x_213);
x_214 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_213, x_3);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; size_t x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_2);
x_218 = lean_array_uset(x_217, x_8, x_2);
x_219 = lean_usize_add(x_8, x_7);
x_220 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_221 = lean_ptr_addr(x_216);
x_222 = lean_usize_dec_eq(x_220, x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_2);
x_223 = l_Lean_Expr_mdata___override(x_212, x_216);
lean_inc(x_223);
x_224 = lean_array_uset(x_218, x_219, x_223);
lean_ctor_set(x_214, 1, x_224);
lean_ctor_set(x_214, 0, x_223);
return x_214;
}
else
{
lean_object* x_225; 
lean_dec(x_216);
lean_dec(x_212);
lean_inc(x_2);
x_225 = lean_array_uset(x_218, x_219, x_2);
lean_ctor_set(x_214, 1, x_225);
lean_ctor_set(x_214, 0, x_2);
return x_214;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; size_t x_229; size_t x_230; size_t x_231; uint8_t x_232; 
x_226 = lean_ctor_get(x_214, 0);
x_227 = lean_ctor_get(x_214, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_214);
lean_inc(x_2);
x_228 = lean_array_uset(x_227, x_8, x_2);
x_229 = lean_usize_add(x_8, x_7);
x_230 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_231 = lean_ptr_addr(x_226);
x_232 = lean_usize_dec_eq(x_230, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_2);
x_233 = l_Lean_Expr_mdata___override(x_212, x_226);
lean_inc(x_233);
x_234 = lean_array_uset(x_228, x_229, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_226);
lean_dec(x_212);
lean_inc(x_2);
x_236 = lean_array_uset(x_228, x_229, x_2);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_2);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
case 11:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_2, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_2, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_2, 2);
lean_inc(x_240);
lean_inc(x_240);
x_241 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_240, x_3);
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; size_t x_246; size_t x_247; size_t x_248; uint8_t x_249; 
x_243 = lean_ctor_get(x_241, 0);
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_2);
x_245 = lean_array_uset(x_244, x_8, x_2);
x_246 = lean_usize_add(x_8, x_7);
x_247 = lean_ptr_addr(x_240);
lean_dec(x_240);
x_248 = lean_ptr_addr(x_243);
x_249 = lean_usize_dec_eq(x_247, x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_2);
x_250 = l_Lean_Expr_proj___override(x_238, x_239, x_243);
lean_inc(x_250);
x_251 = lean_array_uset(x_245, x_246, x_250);
lean_ctor_set(x_241, 1, x_251);
lean_ctor_set(x_241, 0, x_250);
return x_241;
}
else
{
lean_object* x_252; 
lean_dec(x_243);
lean_dec(x_239);
lean_dec(x_238);
lean_inc(x_2);
x_252 = lean_array_uset(x_245, x_246, x_2);
lean_ctor_set(x_241, 1, x_252);
lean_ctor_set(x_241, 0, x_2);
return x_241;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; size_t x_256; size_t x_257; size_t x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_241, 0);
x_254 = lean_ctor_get(x_241, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_241);
lean_inc(x_2);
x_255 = lean_array_uset(x_254, x_8, x_2);
x_256 = lean_usize_add(x_8, x_7);
x_257 = lean_ptr_addr(x_240);
lean_dec(x_240);
x_258 = lean_ptr_addr(x_253);
x_259 = lean_usize_dec_eq(x_257, x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_2);
x_260 = l_Lean_Expr_proj___override(x_238, x_239, x_253);
lean_inc(x_260);
x_261 = lean_array_uset(x_255, x_256, x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_253);
lean_dec(x_239);
lean_dec(x_238);
lean_inc(x_2);
x_263 = lean_array_uset(x_255, x_256, x_2);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_2);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
default: 
{
lean_object* x_265; 
lean_dec(x_1);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_2);
lean_ctor_set(x_265, 1, x_3);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; size_t x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_1);
x_266 = lean_ctor_get(x_12, 0);
lean_inc(x_266);
lean_dec(x_12);
x_267 = lean_array_uset(x_3, x_8, x_2);
x_268 = lean_usize_add(x_8, x_7);
lean_inc(x_266);
x_269 = lean_array_uset(x_267, x_268, x_266);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
else
{
size_t x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_2);
lean_dec(x_1);
x_271 = lean_usize_add(x_8, x_7);
x_272 = lean_array_uget(x_3, x_271);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_3);
return x_273;
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
