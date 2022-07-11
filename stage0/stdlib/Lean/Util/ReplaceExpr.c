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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__4;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceImpl_cacheSize;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_initCache;
static size_t _init_l_Lean_Expr_ReplaceImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_uset(x_6, x_1, x_2);
lean_inc(x_3);
x_9 = lean_array_uset(x_7, x_1, x_3);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_array_uset(x_11, x_1, x_2);
lean_inc(x_3);
x_14 = lean_array_uset(x_12, x_1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = lean_usize_mod(x_5, x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
lean_dec(x_7);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = lean_usize_dec_eq(x_9, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_11) == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_1);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_12, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_13, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_3);
x_20 = lean_expr_update_app(x_3, x_15, x_18);
x_21 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_20, x_19);
return x_21;
}
case 6:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_25 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_22, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_23, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
x_31 = lean_expr_update_lambda(x_3, x_24, x_26, x_29);
x_32 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_31, x_30);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_36 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_33, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_34, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_3);
x_42 = lean_expr_update_forall(x_3, x_35, x_37, x_40);
x_43 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_42, x_41);
return x_43;
}
case 8:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 3);
lean_inc(x_46);
lean_inc(x_1);
x_47 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_44, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_1);
x_50 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_45, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_46, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_3);
x_56 = lean_expr_update_let(x_3, x_48, x_51, x_54);
x_57 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_56, x_55);
return x_57;
}
case 10:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
x_59 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_58, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_3);
x_62 = lean_expr_update_mdata(x_3, x_60);
x_63 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_62, x_61);
return x_63;
}
case 11:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_3, 2);
lean_inc(x_64);
x_65 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_64, x_4);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_3);
x_68 = lean_expr_update_proj(x_3, x_66);
x_69 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_68, x_67);
return x_69;
}
default: 
{
lean_object* x_70; 
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_4);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_ctor_get(x_11, 0);
lean_inc(x_71);
lean_dec(x_11);
x_72 = l_Lean_Expr_ReplaceImpl_cache(x_6, x_3, x_71, x_4);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_3);
lean_dec(x_1);
x_73 = lean_ctor_get(x_4, 1);
lean_inc(x_73);
x_74 = lean_array_uget(x_73, x_6);
lean_dec(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_4);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__2;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
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
l_Lean_Expr_ReplaceImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__1);
l_Lean_Expr_ReplaceImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__2);
l_Lean_Expr_ReplaceImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__3);
l_Lean_Expr_ReplaceImpl_initCache___closed__4 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__4);
l_Lean_Expr_ReplaceImpl_initCache = _init_l_Lean_Expr_ReplaceImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
