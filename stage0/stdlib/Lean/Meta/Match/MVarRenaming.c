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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_insert(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_RBNode_insert___at_Lean_MVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_Cache_new;
LEAN_EXPORT uint8_t l_Lean_Meta_MVarRenaming_isEmpty(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_map___default;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_apply___boxed(lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__3;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MVarRenaming_find_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MVarRenaming_find_x21___closed__4;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_mvarId_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(lean_object*, lean_object*);
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
size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_264; lean_object* x_270; size_t x_271; uint8_t x_272; 
x_4 = lean_ptr_addr(x_2);
x_5 = 4;
x_6 = lean_usize_shift_right(x_4, x_5);
x_7 = 8192;
x_8 = lean_usize_mod(x_6, x_7);
x_270 = lean_array_uget(x_3, x_8);
x_271 = lean_ptr_addr(x_270);
lean_dec(x_270);
x_272 = lean_usize_dec_eq(x_4, x_271);
if (x_272 == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_2, 0);
lean_inc(x_273);
x_274 = l_Lean_RBNode_find___at_Lean_Meta_MVarRenaming_find_x3f___spec__1(x_1, x_273);
lean_dec(x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_inc(x_2);
x_264 = x_2;
goto block_269;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec(x_274);
x_276 = l_Lean_Expr_mvar___override(x_275);
x_264 = x_276;
goto block_269;
}
}
else
{
lean_object* x_277; 
x_277 = lean_box(0);
x_9 = x_277;
goto block_263;
}
}
else
{
size_t x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_2);
x_278 = lean_usize_add(x_8, x_7);
x_279 = lean_array_uget(x_3, x_278);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_3);
return x_280;
}
block_263:
{
lean_dec(x_9);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_10, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_11);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_11, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_2);
x_19 = lean_array_uset(x_18, x_8, x_2);
x_20 = lean_usize_add(x_8, x_7);
x_21 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_22 = lean_ptr_addr(x_13);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = l_Lean_Expr_app___override(x_13, x_17);
lean_inc(x_24);
x_25 = lean_array_uset(x_19, x_20, x_24);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_27 = lean_ptr_addr(x_17);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_29 = l_Lean_Expr_app___override(x_13, x_17);
lean_inc(x_29);
x_30 = lean_array_uset(x_19, x_20, x_29);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_13);
lean_inc(x_2);
x_31 = lean_array_uset(x_19, x_20, x_2);
lean_ctor_set(x_15, 1, x_31);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
lean_inc(x_2);
x_34 = lean_array_uset(x_33, x_8, x_2);
x_35 = lean_usize_add(x_8, x_7);
x_36 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_37 = lean_ptr_addr(x_13);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_2);
x_39 = l_Lean_Expr_app___override(x_13, x_32);
lean_inc(x_39);
x_40 = lean_array_uset(x_34, x_35, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_43 = lean_ptr_addr(x_32);
x_44 = lean_usize_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_45 = l_Lean_Expr_app___override(x_13, x_32);
lean_inc(x_45);
x_46 = lean_array_uset(x_34, x_35, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
lean_dec(x_13);
lean_inc(x_2);
x_48 = lean_array_uset(x_34, x_35, x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
case 6:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_51);
x_54 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_51, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_52);
x_57 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_52, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; size_t x_64; size_t x_65; uint8_t x_66; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_array_uset(x_60, x_8, x_2);
x_62 = lean_usize_add(x_8, x_7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_63 = l_Lean_Expr_lam___override(x_50, x_51, x_52, x_53);
x_64 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_65 = lean_ptr_addr(x_55);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_52);
x_67 = l_Lean_Expr_lam___override(x_50, x_55, x_59, x_53);
lean_inc(x_67);
x_68 = lean_array_uset(x_61, x_62, x_67);
lean_ctor_set(x_57, 1, x_68);
lean_ctor_set(x_57, 0, x_67);
return x_57;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_70 = lean_ptr_addr(x_59);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
x_72 = l_Lean_Expr_lam___override(x_50, x_55, x_59, x_53);
lean_inc(x_72);
x_73 = lean_array_uset(x_61, x_62, x_72);
lean_ctor_set(x_57, 1, x_73);
lean_ctor_set(x_57, 0, x_72);
return x_57;
}
else
{
uint8_t x_74; 
x_74 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_53, x_53);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
x_75 = l_Lean_Expr_lam___override(x_50, x_55, x_59, x_53);
lean_inc(x_75);
x_76 = lean_array_uset(x_61, x_62, x_75);
lean_ctor_set(x_57, 1, x_76);
lean_ctor_set(x_57, 0, x_75);
return x_57;
}
else
{
lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_50);
lean_inc(x_63);
x_77 = lean_array_uset(x_61, x_62, x_63);
lean_ctor_set(x_57, 1, x_77);
lean_ctor_set(x_57, 0, x_63);
return x_57;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; lean_object* x_82; size_t x_83; size_t x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_57, 0);
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_57);
x_80 = lean_array_uset(x_79, x_8, x_2);
x_81 = lean_usize_add(x_8, x_7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_82 = l_Lean_Expr_lam___override(x_50, x_51, x_52, x_53);
x_83 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_84 = lean_ptr_addr(x_55);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_82);
lean_dec(x_52);
x_86 = l_Lean_Expr_lam___override(x_50, x_55, x_78, x_53);
lean_inc(x_86);
x_87 = lean_array_uset(x_80, x_81, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
size_t x_89; size_t x_90; uint8_t x_91; 
x_89 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_90 = lean_ptr_addr(x_78);
x_91 = lean_usize_dec_eq(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
x_92 = l_Lean_Expr_lam___override(x_50, x_55, x_78, x_53);
lean_inc(x_92);
x_93 = lean_array_uset(x_80, x_81, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
else
{
uint8_t x_95; 
x_95 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_53, x_53);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
x_96 = l_Lean_Expr_lam___override(x_50, x_55, x_78, x_53);
lean_inc(x_96);
x_97 = lean_array_uset(x_80, x_81, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_78);
lean_dec(x_55);
lean_dec(x_50);
lean_inc(x_82);
x_99 = lean_array_uset(x_80, x_81, x_82);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_82);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_101 = lean_ctor_get(x_2, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_2, 2);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_102);
x_105 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_102, x_3);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_103);
x_108 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_103, x_107);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; lean_object* x_114; size_t x_115; size_t x_116; uint8_t x_117; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
x_112 = lean_array_uset(x_111, x_8, x_2);
x_113 = lean_usize_add(x_8, x_7);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_114 = l_Lean_Expr_forallE___override(x_101, x_102, x_103, x_104);
x_115 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_116 = lean_ptr_addr(x_106);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_114);
lean_dec(x_103);
x_118 = l_Lean_Expr_forallE___override(x_101, x_106, x_110, x_104);
lean_inc(x_118);
x_119 = lean_array_uset(x_112, x_113, x_118);
lean_ctor_set(x_108, 1, x_119);
lean_ctor_set(x_108, 0, x_118);
return x_108;
}
else
{
size_t x_120; size_t x_121; uint8_t x_122; 
x_120 = lean_ptr_addr(x_103);
lean_dec(x_103);
x_121 = lean_ptr_addr(x_110);
x_122 = lean_usize_dec_eq(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_114);
x_123 = l_Lean_Expr_forallE___override(x_101, x_106, x_110, x_104);
lean_inc(x_123);
x_124 = lean_array_uset(x_112, x_113, x_123);
lean_ctor_set(x_108, 1, x_124);
lean_ctor_set(x_108, 0, x_123);
return x_108;
}
else
{
uint8_t x_125; 
x_125 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_104, x_104);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_114);
x_126 = l_Lean_Expr_forallE___override(x_101, x_106, x_110, x_104);
lean_inc(x_126);
x_127 = lean_array_uset(x_112, x_113, x_126);
lean_ctor_set(x_108, 1, x_127);
lean_ctor_set(x_108, 0, x_126);
return x_108;
}
else
{
lean_object* x_128; 
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_101);
lean_inc(x_114);
x_128 = lean_array_uset(x_112, x_113, x_114);
lean_ctor_set(x_108, 1, x_128);
lean_ctor_set(x_108, 0, x_114);
return x_108;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; lean_object* x_133; size_t x_134; size_t x_135; uint8_t x_136; 
x_129 = lean_ctor_get(x_108, 0);
x_130 = lean_ctor_get(x_108, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_108);
x_131 = lean_array_uset(x_130, x_8, x_2);
x_132 = lean_usize_add(x_8, x_7);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_133 = l_Lean_Expr_forallE___override(x_101, x_102, x_103, x_104);
x_134 = lean_ptr_addr(x_102);
lean_dec(x_102);
x_135 = lean_ptr_addr(x_106);
x_136 = lean_usize_dec_eq(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_133);
lean_dec(x_103);
x_137 = l_Lean_Expr_forallE___override(x_101, x_106, x_129, x_104);
lean_inc(x_137);
x_138 = lean_array_uset(x_131, x_132, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
size_t x_140; size_t x_141; uint8_t x_142; 
x_140 = lean_ptr_addr(x_103);
lean_dec(x_103);
x_141 = lean_ptr_addr(x_129);
x_142 = lean_usize_dec_eq(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_133);
x_143 = l_Lean_Expr_forallE___override(x_101, x_106, x_129, x_104);
lean_inc(x_143);
x_144 = lean_array_uset(x_131, x_132, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
else
{
uint8_t x_146; 
x_146 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_104, x_104);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_133);
x_147 = l_Lean_Expr_forallE___override(x_101, x_106, x_129, x_104);
lean_inc(x_147);
x_148 = lean_array_uset(x_131, x_132, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_129);
lean_dec(x_106);
lean_dec(x_101);
lean_inc(x_133);
x_150 = lean_array_uset(x_131, x_132, x_133);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_133);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
}
case 8:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_152 = lean_ctor_get(x_2, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_2, 3);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_153);
x_157 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_153, x_3);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_154);
x_160 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_154, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_155);
x_163 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_155, x_162);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; size_t x_168; size_t x_169; size_t x_170; uint8_t x_171; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_2);
x_167 = lean_array_uset(x_166, x_8, x_2);
x_168 = lean_usize_add(x_8, x_7);
x_169 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_170 = lean_ptr_addr(x_158);
x_171 = lean_usize_dec_eq(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_2);
x_172 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_165, x_156);
lean_inc(x_172);
x_173 = lean_array_uset(x_167, x_168, x_172);
lean_ctor_set(x_163, 1, x_173);
lean_ctor_set(x_163, 0, x_172);
return x_163;
}
else
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_154);
lean_dec(x_154);
x_175 = lean_ptr_addr(x_161);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_155);
lean_dec(x_2);
x_177 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_165, x_156);
lean_inc(x_177);
x_178 = lean_array_uset(x_167, x_168, x_177);
lean_ctor_set(x_163, 1, x_178);
lean_ctor_set(x_163, 0, x_177);
return x_163;
}
else
{
size_t x_179; size_t x_180; uint8_t x_181; 
x_179 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_180 = lean_ptr_addr(x_165);
x_181 = lean_usize_dec_eq(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_2);
x_182 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_165, x_156);
lean_inc(x_182);
x_183 = lean_array_uset(x_167, x_168, x_182);
lean_ctor_set(x_163, 1, x_183);
lean_ctor_set(x_163, 0, x_182);
return x_163;
}
else
{
lean_object* x_184; 
lean_dec(x_165);
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_152);
lean_inc(x_2);
x_184 = lean_array_uset(x_167, x_168, x_2);
lean_ctor_set(x_163, 1, x_184);
lean_ctor_set(x_163, 0, x_2);
return x_163;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; size_t x_188; size_t x_189; size_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_163, 0);
x_186 = lean_ctor_get(x_163, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_163);
lean_inc(x_2);
x_187 = lean_array_uset(x_186, x_8, x_2);
x_188 = lean_usize_add(x_8, x_7);
x_189 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_190 = lean_ptr_addr(x_158);
x_191 = lean_usize_dec_eq(x_189, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_2);
x_192 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_185, x_156);
lean_inc(x_192);
x_193 = lean_array_uset(x_187, x_188, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
else
{
size_t x_195; size_t x_196; uint8_t x_197; 
x_195 = lean_ptr_addr(x_154);
lean_dec(x_154);
x_196 = lean_ptr_addr(x_161);
x_197 = lean_usize_dec_eq(x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_155);
lean_dec(x_2);
x_198 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_185, x_156);
lean_inc(x_198);
x_199 = lean_array_uset(x_187, x_188, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
else
{
size_t x_201; size_t x_202; uint8_t x_203; 
x_201 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_202 = lean_ptr_addr(x_185);
x_203 = lean_usize_dec_eq(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_2);
x_204 = l_Lean_Expr_letE___override(x_152, x_158, x_161, x_185, x_156);
lean_inc(x_204);
x_205 = lean_array_uset(x_187, x_188, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_185);
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_152);
lean_inc(x_2);
x_207 = lean_array_uset(x_187, x_188, x_2);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_2);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
}
case 10:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_2, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_2, 1);
lean_inc(x_210);
lean_inc(x_210);
x_211 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_210, x_3);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; size_t x_216; size_t x_217; size_t x_218; uint8_t x_219; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_2);
x_215 = lean_array_uset(x_214, x_8, x_2);
x_216 = lean_usize_add(x_8, x_7);
x_217 = lean_ptr_addr(x_210);
lean_dec(x_210);
x_218 = lean_ptr_addr(x_213);
x_219 = lean_usize_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_2);
x_220 = l_Lean_Expr_mdata___override(x_209, x_213);
lean_inc(x_220);
x_221 = lean_array_uset(x_215, x_216, x_220);
lean_ctor_set(x_211, 1, x_221);
lean_ctor_set(x_211, 0, x_220);
return x_211;
}
else
{
lean_object* x_222; 
lean_dec(x_213);
lean_dec(x_209);
lean_inc(x_2);
x_222 = lean_array_uset(x_215, x_216, x_2);
lean_ctor_set(x_211, 1, x_222);
lean_ctor_set(x_211, 0, x_2);
return x_211;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; size_t x_226; size_t x_227; size_t x_228; uint8_t x_229; 
x_223 = lean_ctor_get(x_211, 0);
x_224 = lean_ctor_get(x_211, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_211);
lean_inc(x_2);
x_225 = lean_array_uset(x_224, x_8, x_2);
x_226 = lean_usize_add(x_8, x_7);
x_227 = lean_ptr_addr(x_210);
lean_dec(x_210);
x_228 = lean_ptr_addr(x_223);
x_229 = lean_usize_dec_eq(x_227, x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_2);
x_230 = l_Lean_Expr_mdata___override(x_209, x_223);
lean_inc(x_230);
x_231 = lean_array_uset(x_225, x_226, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_223);
lean_dec(x_209);
lean_inc(x_2);
x_233 = lean_array_uset(x_225, x_226, x_2);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_2);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
case 11:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_2, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_2, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_2, 2);
lean_inc(x_237);
lean_inc(x_237);
x_238 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_MVarRenaming_apply___spec__1(x_1, x_237, x_3);
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; size_t x_243; size_t x_244; size_t x_245; uint8_t x_246; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_2);
x_242 = lean_array_uset(x_241, x_8, x_2);
x_243 = lean_usize_add(x_8, x_7);
x_244 = lean_ptr_addr(x_237);
lean_dec(x_237);
x_245 = lean_ptr_addr(x_240);
x_246 = lean_usize_dec_eq(x_244, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_2);
x_247 = l_Lean_Expr_proj___override(x_235, x_236, x_240);
lean_inc(x_247);
x_248 = lean_array_uset(x_242, x_243, x_247);
lean_ctor_set(x_238, 1, x_248);
lean_ctor_set(x_238, 0, x_247);
return x_238;
}
else
{
lean_object* x_249; 
lean_dec(x_240);
lean_dec(x_236);
lean_dec(x_235);
lean_inc(x_2);
x_249 = lean_array_uset(x_242, x_243, x_2);
lean_ctor_set(x_238, 1, x_249);
lean_ctor_set(x_238, 0, x_2);
return x_238;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; size_t x_253; size_t x_254; size_t x_255; uint8_t x_256; 
x_250 = lean_ctor_get(x_238, 0);
x_251 = lean_ctor_get(x_238, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_238);
lean_inc(x_2);
x_252 = lean_array_uset(x_251, x_8, x_2);
x_253 = lean_usize_add(x_8, x_7);
x_254 = lean_ptr_addr(x_237);
lean_dec(x_237);
x_255 = lean_ptr_addr(x_250);
x_256 = lean_usize_dec_eq(x_254, x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_2);
x_257 = l_Lean_Expr_proj___override(x_235, x_236, x_250);
lean_inc(x_257);
x_258 = lean_array_uset(x_252, x_253, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_250);
lean_dec(x_236);
lean_dec(x_235);
lean_inc(x_2);
x_260 = lean_array_uset(x_252, x_253, x_2);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_2);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
default: 
{
lean_object* x_262; 
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_2);
lean_ctor_set(x_262, 1, x_3);
return x_262;
}
}
}
block_269:
{
lean_object* x_265; size_t x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_array_uset(x_3, x_8, x_2);
x_266 = lean_usize_add(x_8, x_7);
lean_inc(x_264);
x_267 = lean_array_uset(x_265, x_266, x_264);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_267);
return x_268;
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
x_4 = l_Lean_Expr_ReplaceImpl_Cache_new;
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
