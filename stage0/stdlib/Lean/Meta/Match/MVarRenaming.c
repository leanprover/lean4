// Lean compiler output
// Module: Lean.Meta.Match.MVarRenaming
// Imports: Init Lean.Util.ReplaceExpr
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__1;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__4;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_mvarId_x21___spec__1(lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* l_Lean_Expr_ReplaceImpl_Cache_new(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_ReplaceImpl_Cache_store(lean_object*, lean_object*, lean_object*);
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
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_235; size_t x_236; size_t x_237; size_t x_238; lean_object* x_239; size_t x_240; uint8_t x_241; 
x_235 = lean_ctor_get(x_3, 0);
lean_inc(x_235);
x_236 = lean_ptr_addr(x_2);
x_237 = lean_ctor_get_usize(x_3, 1);
x_238 = lean_usize_mod(x_236, x_237);
x_239 = lean_array_uget(x_235, x_238);
x_240 = lean_ptr_addr(x_239);
lean_dec(x_239);
x_241 = lean_usize_dec_eq(x_236, x_240);
if (x_241 == 0)
{
lean_dec(x_235);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_2, 0);
lean_inc(x_242);
x_243 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_242);
lean_dec(x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_inc_n(x_2, 2);
x_244 = l_Lean_Expr_ReplaceImpl_Cache_store(x_3, x_2, x_2);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_2);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
lean_dec(x_243);
x_247 = l_Lean_Expr_mvar___override(x_246);
lean_inc(x_247);
x_248 = l_Lean_Expr_ReplaceImpl_Cache_store(x_3, x_2, x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
else
{
lean_object* x_250; 
x_250 = lean_box(0);
x_4 = x_250;
goto block_234;
}
}
else
{
size_t x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_2);
x_251 = lean_usize_add(x_238, x_237);
x_252 = lean_array_uget(x_235, x_251);
lean_dec(x_235);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_3);
return x_253;
}
block_234:
{
lean_dec(x_4);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_5, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_6);
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_15 = lean_ptr_addr(x_8);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = l_Lean_Expr_app___override(x_8, x_12);
lean_inc(x_17);
x_18 = l_Lean_Expr_ReplaceImpl_Cache_store(x_13, x_2, x_17);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_20 = lean_ptr_addr(x_12);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_app___override(x_8, x_12);
lean_inc(x_22);
x_23 = l_Lean_Expr_ReplaceImpl_Cache_store(x_13, x_2, x_22);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_8);
lean_inc_n(x_2, 2);
x_24 = l_Lean_Expr_ReplaceImpl_Cache_store(x_13, x_2, x_2);
lean_ctor_set(x_10, 1, x_24);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_28 = lean_ptr_addr(x_8);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_30 = l_Lean_Expr_app___override(x_8, x_25);
lean_inc(x_30);
x_31 = l_Lean_Expr_ReplaceImpl_Cache_store(x_26, x_2, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_34 = lean_ptr_addr(x_25);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Expr_app___override(x_8, x_25);
lean_inc(x_36);
x_37 = l_Lean_Expr_ReplaceImpl_Cache_store(x_26, x_2, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
lean_dec(x_8);
lean_inc_n(x_2, 2);
x_39 = l_Lean_Expr_ReplaceImpl_Cache_store(x_26, x_2, x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_42);
x_45 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_42, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_43);
x_48 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_43, x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
x_52 = l_Lean_Expr_lam___override(x_41, x_42, x_43, x_44);
x_53 = lean_ptr_addr(x_42);
lean_dec(x_42);
x_54 = lean_ptr_addr(x_46);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_43);
x_56 = l_Lean_Expr_lam___override(x_41, x_46, x_50, x_44);
lean_inc(x_56);
x_57 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_56);
lean_ctor_set(x_48, 1, x_57);
lean_ctor_set(x_48, 0, x_56);
return x_48;
}
else
{
size_t x_58; size_t x_59; uint8_t x_60; 
x_58 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_59 = lean_ptr_addr(x_50);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
x_61 = l_Lean_Expr_lam___override(x_41, x_46, x_50, x_44);
lean_inc(x_61);
x_62 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_61);
lean_ctor_set(x_48, 1, x_62);
lean_ctor_set(x_48, 0, x_61);
return x_48;
}
else
{
uint8_t x_63; 
x_63 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_44, x_44);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_52);
x_64 = l_Lean_Expr_lam___override(x_41, x_46, x_50, x_44);
lean_inc(x_64);
x_65 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_64);
lean_ctor_set(x_48, 1, x_65);
lean_ctor_set(x_48, 0, x_64);
return x_48;
}
else
{
lean_object* x_66; 
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_41);
lean_inc(x_52);
x_66 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_52);
lean_ctor_set(x_48, 1, x_66);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
x_69 = l_Lean_Expr_lam___override(x_41, x_42, x_43, x_44);
x_70 = lean_ptr_addr(x_42);
lean_dec(x_42);
x_71 = lean_ptr_addr(x_46);
x_72 = lean_usize_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_69);
lean_dec(x_43);
x_73 = l_Lean_Expr_lam___override(x_41, x_46, x_67, x_44);
lean_inc(x_73);
x_74 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_77 = lean_ptr_addr(x_67);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
x_79 = l_Lean_Expr_lam___override(x_41, x_46, x_67, x_44);
lean_inc(x_79);
x_80 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_44, x_44);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_69);
x_83 = l_Lean_Expr_lam___override(x_41, x_46, x_67, x_44);
lean_inc(x_83);
x_84 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_41);
lean_inc(x_69);
x_86 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_69);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_69);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
case 7:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_89);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_89, x_3);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_90);
x_95 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_90, x_94);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; size_t x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
x_99 = l_Lean_Expr_forallE___override(x_88, x_89, x_90, x_91);
x_100 = lean_ptr_addr(x_89);
lean_dec(x_89);
x_101 = lean_ptr_addr(x_93);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_99);
lean_dec(x_90);
x_103 = l_Lean_Expr_forallE___override(x_88, x_93, x_97, x_91);
lean_inc(x_103);
x_104 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_103);
lean_ctor_set(x_95, 1, x_104);
lean_ctor_set(x_95, 0, x_103);
return x_95;
}
else
{
size_t x_105; size_t x_106; uint8_t x_107; 
x_105 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_106 = lean_ptr_addr(x_97);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_99);
x_108 = l_Lean_Expr_forallE___override(x_88, x_93, x_97, x_91);
lean_inc(x_108);
x_109 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_108);
lean_ctor_set(x_95, 1, x_109);
lean_ctor_set(x_95, 0, x_108);
return x_95;
}
else
{
uint8_t x_110; 
x_110 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_91, x_91);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_99);
x_111 = l_Lean_Expr_forallE___override(x_88, x_93, x_97, x_91);
lean_inc(x_111);
x_112 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_111);
lean_ctor_set(x_95, 1, x_112);
lean_ctor_set(x_95, 0, x_111);
return x_95;
}
else
{
lean_object* x_113; 
lean_dec(x_97);
lean_dec(x_93);
lean_dec(x_88);
lean_inc(x_99);
x_113 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_99);
lean_ctor_set(x_95, 1, x_113);
lean_ctor_set(x_95, 0, x_99);
return x_95;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; size_t x_117; size_t x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_95, 0);
x_115 = lean_ctor_get(x_95, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_95);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
x_116 = l_Lean_Expr_forallE___override(x_88, x_89, x_90, x_91);
x_117 = lean_ptr_addr(x_89);
lean_dec(x_89);
x_118 = lean_ptr_addr(x_93);
x_119 = lean_usize_dec_eq(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_116);
lean_dec(x_90);
x_120 = l_Lean_Expr_forallE___override(x_88, x_93, x_114, x_91);
lean_inc(x_120);
x_121 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
size_t x_123; size_t x_124; uint8_t x_125; 
x_123 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_124 = lean_ptr_addr(x_114);
x_125 = lean_usize_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_116);
x_126 = l_Lean_Expr_forallE___override(x_88, x_93, x_114, x_91);
lean_inc(x_126);
x_127 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
else
{
uint8_t x_129; 
x_129 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_91, x_91);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_116);
x_130 = l_Lean_Expr_forallE___override(x_88, x_93, x_114, x_91);
lean_inc(x_130);
x_131 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_114);
lean_dec(x_93);
lean_dec(x_88);
lean_inc(x_116);
x_133 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_116);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_116);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
}
case 8:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_135 = lean_ctor_get(x_2, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 3);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_136);
x_140 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_136, x_3);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_137);
x_143 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_137, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_138);
x_146 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_138, x_145);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; size_t x_150; size_t x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = lean_ctor_get(x_146, 1);
x_150 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_151 = lean_ptr_addr(x_141);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_138);
lean_dec(x_137);
x_153 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_148, x_139);
lean_inc(x_153);
x_154 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_153);
lean_ctor_set(x_146, 1, x_154);
lean_ctor_set(x_146, 0, x_153);
return x_146;
}
else
{
size_t x_155; size_t x_156; uint8_t x_157; 
x_155 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_156 = lean_ptr_addr(x_144);
x_157 = lean_usize_dec_eq(x_155, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_138);
x_158 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_148, x_139);
lean_inc(x_158);
x_159 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_158);
lean_ctor_set(x_146, 1, x_159);
lean_ctor_set(x_146, 0, x_158);
return x_146;
}
else
{
size_t x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_161 = lean_ptr_addr(x_148);
x_162 = lean_usize_dec_eq(x_160, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_148, x_139);
lean_inc(x_163);
x_164 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_163);
lean_ctor_set(x_146, 1, x_164);
lean_ctor_set(x_146, 0, x_163);
return x_146;
}
else
{
lean_object* x_165; 
lean_dec(x_148);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_135);
lean_inc_n(x_2, 2);
x_165 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_2);
lean_ctor_set(x_146, 1, x_165);
lean_ctor_set(x_146, 0, x_2);
return x_146;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; size_t x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_146, 0);
x_167 = lean_ctor_get(x_146, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_146);
x_168 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_169 = lean_ptr_addr(x_141);
x_170 = lean_usize_dec_eq(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_138);
lean_dec(x_137);
x_171 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_166, x_139);
lean_inc(x_171);
x_172 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
else
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_175 = lean_ptr_addr(x_144);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_138);
x_177 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_166, x_139);
lean_inc(x_177);
x_178 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
else
{
size_t x_180; size_t x_181; uint8_t x_182; 
x_180 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_181 = lean_ptr_addr(x_166);
x_182 = lean_usize_dec_eq(x_180, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_166, x_139);
lean_inc(x_183);
x_184 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_166);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_135);
lean_inc_n(x_2, 2);
x_186 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_2);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_2);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
}
case 10:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_2, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 1);
lean_inc(x_189);
lean_inc(x_189);
x_190 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_189, x_3);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; size_t x_194; size_t x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_ctor_get(x_190, 1);
x_194 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_195 = lean_ptr_addr(x_192);
x_196 = lean_usize_dec_eq(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Lean_Expr_mdata___override(x_188, x_192);
lean_inc(x_197);
x_198 = l_Lean_Expr_ReplaceImpl_Cache_store(x_193, x_2, x_197);
lean_ctor_set(x_190, 1, x_198);
lean_ctor_set(x_190, 0, x_197);
return x_190;
}
else
{
lean_object* x_199; 
lean_dec(x_192);
lean_dec(x_188);
lean_inc_n(x_2, 2);
x_199 = l_Lean_Expr_ReplaceImpl_Cache_store(x_193, x_2, x_2);
lean_ctor_set(x_190, 1, x_199);
lean_ctor_set(x_190, 0, x_2);
return x_190;
}
}
else
{
lean_object* x_200; lean_object* x_201; size_t x_202; size_t x_203; uint8_t x_204; 
x_200 = lean_ctor_get(x_190, 0);
x_201 = lean_ctor_get(x_190, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_190);
x_202 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_203 = lean_ptr_addr(x_200);
x_204 = lean_usize_dec_eq(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = l_Lean_Expr_mdata___override(x_188, x_200);
lean_inc(x_205);
x_206 = l_Lean_Expr_ReplaceImpl_Cache_store(x_201, x_2, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_200);
lean_dec(x_188);
lean_inc_n(x_2, 2);
x_208 = l_Lean_Expr_ReplaceImpl_Cache_store(x_201, x_2, x_2);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_2);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
case 11:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_210 = lean_ctor_get(x_2, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_2, 2);
lean_inc(x_212);
lean_inc(x_212);
x_213 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_212, x_3);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; size_t x_217; size_t x_218; uint8_t x_219; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_ctor_get(x_213, 1);
x_217 = lean_ptr_addr(x_212);
lean_dec(x_212);
x_218 = lean_ptr_addr(x_215);
x_219 = lean_usize_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = l_Lean_Expr_proj___override(x_210, x_211, x_215);
lean_inc(x_220);
x_221 = l_Lean_Expr_ReplaceImpl_Cache_store(x_216, x_2, x_220);
lean_ctor_set(x_213, 1, x_221);
lean_ctor_set(x_213, 0, x_220);
return x_213;
}
else
{
lean_object* x_222; 
lean_dec(x_215);
lean_dec(x_211);
lean_dec(x_210);
lean_inc_n(x_2, 2);
x_222 = l_Lean_Expr_ReplaceImpl_Cache_store(x_216, x_2, x_2);
lean_ctor_set(x_213, 1, x_222);
lean_ctor_set(x_213, 0, x_2);
return x_213;
}
}
else
{
lean_object* x_223; lean_object* x_224; size_t x_225; size_t x_226; uint8_t x_227; 
x_223 = lean_ctor_get(x_213, 0);
x_224 = lean_ctor_get(x_213, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_213);
x_225 = lean_ptr_addr(x_212);
lean_dec(x_212);
x_226 = lean_ptr_addr(x_223);
x_227 = lean_usize_dec_eq(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = l_Lean_Expr_proj___override(x_210, x_211, x_223);
lean_inc(x_228);
x_229 = l_Lean_Expr_ReplaceImpl_Cache_store(x_224, x_2, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_223);
lean_dec(x_211);
lean_dec(x_210);
lean_inc_n(x_2, 2);
x_231 = l_Lean_Expr_ReplaceImpl_Cache_store(x_224, x_2, x_2);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_2);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
default: 
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_2);
lean_ctor_set(x_233, 1, x_3);
return x_233;
}
}
}
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
x_4 = l_Lean_Expr_ReplaceImpl_Cache_new(x_2);
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
