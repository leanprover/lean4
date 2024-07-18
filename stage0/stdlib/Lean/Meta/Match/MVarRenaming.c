// Lean compiler output
// Module: Lean.Meta.Match.MVarRenaming
// Imports: Lean.Util.ReplaceExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_map___default;
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_apply___closed__1;
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__1;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_is_exclusive_obj(lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__4;
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(uint8_t, uint8_t);
lean_object* l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_mvarId_x21___spec__1(lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__3(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* _init_l_Lean_Meta_MVarRenaming_map___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_MVarRenaming_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MVarRenaming_find_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_MVarRenaming_find_x21___closed__1;
x_2 = l_Lean_Meta_MVarRenaming_find_x21___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Meta_MVarRenaming_find_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_MVarRenaming_find_x21___closed__4;
x_5 = l_panic___at_Lean_Expr_mvarId_x21___spec__1(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MVarRenaming_find_x21(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_to_uint64(x_5);
x_7 = 11;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_hashmap_mk_idx(x_4, x_8);
x_10 = lean_array_uget(x_3, x_9);
x_11 = l_Lean_AssocList_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__3(x_2, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
x_132 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_2, x_131);
lean_dec(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
lean_inc(x_1);
x_133 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_1, x_5);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Expr_mvar___override(x_134);
x_136 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_135, x_5);
return x_136;
}
}
else
{
lean_object* x_137; 
x_137 = lean_box(0);
x_6 = x_137;
goto block_130;
}
block_130:
{
lean_dec(x_6);
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
x_9 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_7, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_8);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_16 = lean_ptr_addr(x_10);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_18 = l_Lean_Expr_app___override(x_10, x_13);
x_19 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_18, x_14);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_21 = lean_ptr_addr(x_13);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Expr_app___override(x_10, x_13);
x_24 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_23, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_10);
lean_inc(x_1);
x_25 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_1, x_14);
return x_25;
}
}
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; uint8_t x_39; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_27);
x_30 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_27, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_28);
x_33 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_28, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_36 = l_Lean_Expr_lam___override(x_26, x_27, x_28, x_29);
x_37 = lean_ptr_addr(x_27);
lean_dec(x_27);
x_38 = lean_ptr_addr(x_31);
x_39 = lean_usize_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_28);
x_40 = l_Lean_Expr_lam___override(x_26, x_31, x_34, x_29);
x_41 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_40, x_35);
return x_41;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_43 = lean_ptr_addr(x_34);
x_44 = lean_usize_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_36);
x_45 = l_Lean_Expr_lam___override(x_26, x_31, x_34, x_29);
x_46 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_45, x_35);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_29, x_29);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_36);
x_48 = l_Lean_Expr_lam___override(x_26, x_31, x_34, x_29);
x_49 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_48, x_35);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_26);
x_50 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_36, x_35);
return x_50;
}
}
}
}
case 7:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; uint8_t x_64; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_52);
x_55 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_52, x_5);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_53);
x_58 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_53, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_61 = l_Lean_Expr_forallE___override(x_51, x_52, x_53, x_54);
x_62 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_63 = lean_ptr_addr(x_56);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_53);
x_65 = l_Lean_Expr_forallE___override(x_51, x_56, x_59, x_54);
x_66 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_65, x_60);
return x_66;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; 
x_67 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_68 = lean_ptr_addr(x_59);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
x_70 = l_Lean_Expr_forallE___override(x_51, x_56, x_59, x_54);
x_71 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_70, x_60);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_54, x_54);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
x_73 = l_Lean_Expr_forallE___override(x_51, x_56, x_59, x_54);
x_74 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_73, x_60);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_51);
x_75 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_61, x_60);
return x_75;
}
}
}
}
case 8:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; uint8_t x_92; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 3);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_77);
x_81 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_77, x_5);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_78);
x_84 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_78, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_79);
x_87 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_79, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ptr_addr(x_77);
lean_dec(x_77);
x_91 = lean_ptr_addr(x_82);
x_92 = lean_usize_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
lean_dec(x_78);
x_93 = l_Lean_Expr_letE___override(x_76, x_82, x_85, x_88, x_80);
x_94 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_93, x_89);
return x_94;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_78);
lean_dec(x_78);
x_96 = lean_ptr_addr(x_85);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = l_Lean_Expr_letE___override(x_76, x_82, x_85, x_88, x_80);
x_99 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_98, x_89);
return x_99;
}
else
{
size_t x_100; size_t x_101; uint8_t x_102; 
x_100 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_101 = lean_ptr_addr(x_88);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_Expr_letE___override(x_76, x_82, x_85, x_88, x_80);
x_104 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_103, x_89);
return x_104;
}
else
{
lean_object* x_105; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_76);
lean_inc(x_1);
x_105 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_1, x_89);
return x_105;
}
}
}
}
case 10:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; uint8_t x_113; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_1, 1);
lean_inc(x_107);
lean_inc(x_107);
x_108 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_107, x_5);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_112 = lean_ptr_addr(x_109);
x_113 = lean_usize_dec_eq(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Lean_Expr_mdata___override(x_106, x_109);
x_115 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_114, x_110);
return x_115;
}
else
{
lean_object* x_116; 
lean_dec(x_109);
lean_dec(x_106);
lean_inc(x_1);
x_116 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_1, x_110);
return x_116;
}
}
case 11:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; size_t x_123; size_t x_124; uint8_t x_125; 
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 2);
lean_inc(x_119);
lean_inc(x_119);
x_120 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_2, x_119, x_5);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ptr_addr(x_119);
lean_dec(x_119);
x_124 = lean_ptr_addr(x_121);
x_125 = lean_usize_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Lean_Expr_proj___override(x_117, x_118, x_121);
x_127 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_126, x_122);
return x_127;
}
else
{
lean_object* x_128; 
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
lean_inc(x_1);
x_128 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_3, x_1, x_122);
return x_128;
}
}
default: 
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_5);
return x_129;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_is_exclusive_obj(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__2(x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___lambda__1(x_2, x_1, x_4, x_6, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___lambda__1(x_2, x_1, x_4, x_10, x_3);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_apply___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Meta_MVarRenaming_apply___closed__1;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_MVarRenaming_apply___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MVarRenaming_apply(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ReplaceExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_MVarRenaming_map___default = _init_l_Lean_Meta_MVarRenaming_map___default();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_map___default);
l_Lean_Meta_MVarRenaming_find_x21___closed__1 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__1();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__1);
l_Lean_Meta_MVarRenaming_find_x21___closed__2 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__2();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__2);
l_Lean_Meta_MVarRenaming_find_x21___closed__3 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__3);
l_Lean_Meta_MVarRenaming_find_x21___closed__4 = _init_l_Lean_Meta_MVarRenaming_find_x21___closed__4();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_find_x21___closed__4);
l_Lean_Meta_MVarRenaming_apply___closed__1 = _init_l_Lean_Meta_MVarRenaming_apply___closed__1();
lean_mark_persistent(l_Lean_Meta_MVarRenaming_apply___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
