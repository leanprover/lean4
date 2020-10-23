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
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_replace_match__2(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__2;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__2(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replace_match__1(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__3;
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4;
extern lean_object* l___private_Lean_Data_Format_0__Lean_Format_be___closed__1;
lean_object* l_Init_Control_Monad___instance__2___rarg(lean_object*, lean_object*);
size_t l_Lean_Expr_ReplaceImpl_cacheSize;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__1(lean_object*);
lean_object* l_Lean_Expr_replace_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replace_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11___closed__1;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__3;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_initCache;
static size_t _init_l_Lean_Expr_ReplaceImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_uset(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_3);
x_8 = lean_array_uset(x_7, x_1, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_6, x_10, x_11, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_4(x_3, x_15, x_16, x_17, x_19);
return x_20;
}
case 7:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_25 = lean_box_uint64(x_24);
x_26 = lean_apply_4(x_2, x_21, x_22, x_23, x_25);
return x_26;
}
case 8:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 3);
lean_inc(x_30);
x_31 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_32 = lean_box_uint64(x_31);
x_33 = lean_apply_5(x_5, x_27, x_28, x_29, x_30, x_32);
return x_33;
}
case 10:
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_3(x_4, x_34, x_35, x_37);
return x_38;
}
case 11:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_43 = lean_box_uint64(x_42);
x_44 = lean_apply_4(x_7, x_39, x_40, x_41, x_43);
return x_44;
}
case 12:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_49 = lean_box_uint64(x_48);
x_50 = lean_apply_4(x_8, x_45, x_46, x_47, x_49);
return x_50;
}
default: 
{
lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_apply_1(x_9, x_1);
return x_51;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Format_0__Lean_Format_be___closed__1;
x_2 = l_Lean_Expr_Lean_Expr___instance__11;
x_3 = l_Init_Control_Monad___instance__2___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Util.ReplaceExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.ReplaceImpl.replaceUnsafeM.visit");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2;
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__3;
x_3 = lean_unsigned_to_nat(42u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = x_9 == x_5;
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_12);
lean_inc(x_1);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_12, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
x_18 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_13, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set_uint64(x_22, sizeof(void*)*2, x_14);
x_23 = lean_expr_update_app(x_22, x_16, x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_array_uset(x_24, x_6, x_3);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
lean_inc(x_23);
x_27 = lean_array_uset(x_26, x_6, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set_uint64(x_31, sizeof(void*)*2, x_14);
x_32 = lean_expr_update_app(x_31, x_16, x_29);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_array_uset(x_33, x_6, x_3);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
lean_inc(x_32);
x_36 = lean_array_uset(x_35, x_6, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_40);
lean_inc(x_1);
x_43 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_40, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_41);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_41, x_45);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set_uint64(x_50, sizeof(void*)*3, x_42);
x_51 = (uint8_t)((x_42 << 24) >> 61);
x_52 = lean_expr_update_lambda(x_50, x_51, x_44, x_48);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_array_uset(x_53, x_6, x_3);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
lean_inc(x_52);
x_56 = lean_array_uset(x_55, x_6, x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_46, 1, x_57);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_60, 0, x_39);
lean_ctor_set(x_60, 1, x_40);
lean_ctor_set(x_60, 2, x_41);
lean_ctor_set_uint64(x_60, sizeof(void*)*3, x_42);
x_61 = (uint8_t)((x_42 << 24) >> 61);
x_62 = lean_expr_update_lambda(x_60, x_61, x_44, x_58);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_array_uset(x_63, x_6, x_3);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_inc(x_62);
x_66 = lean_array_uset(x_65, x_6, x_62);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
case 7:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_69 = lean_ctor_get(x_3, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 2);
lean_inc(x_71);
x_72 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_70);
lean_inc(x_1);
x_73 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_70, x_4);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_71);
x_76 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_71, x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
x_80 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_70);
lean_ctor_set(x_80, 2, x_71);
lean_ctor_set_uint64(x_80, sizeof(void*)*3, x_72);
x_81 = (uint8_t)((x_72 << 24) >> 61);
x_82 = lean_expr_update_forall(x_80, x_81, x_74, x_78);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
x_84 = lean_array_uset(x_83, x_6, x_3);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
lean_inc(x_82);
x_86 = lean_array_uset(x_85, x_6, x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_76, 1, x_87);
lean_ctor_set(x_76, 0, x_82);
return x_76;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_76, 0);
x_89 = lean_ctor_get(x_76, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_76);
x_90 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_90, 0, x_69);
lean_ctor_set(x_90, 1, x_70);
lean_ctor_set(x_90, 2, x_71);
lean_ctor_set_uint64(x_90, sizeof(void*)*3, x_72);
x_91 = (uint8_t)((x_72 << 24) >> 61);
x_92 = lean_expr_update_forall(x_90, x_91, x_74, x_88);
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_array_uset(x_93, x_6, x_3);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
lean_inc(x_92);
x_96 = lean_array_uset(x_95, x_6, x_92);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
case 8:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_99 = lean_ctor_get(x_3, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_3, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_3, 3);
lean_inc(x_102);
x_103 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_100);
lean_inc(x_1);
x_104 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_100, x_4);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_101);
lean_inc(x_1);
x_107 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_101, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_102);
x_110 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_102, x_109);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
x_114 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_114, 0, x_99);
lean_ctor_set(x_114, 1, x_100);
lean_ctor_set(x_114, 2, x_101);
lean_ctor_set(x_114, 3, x_102);
lean_ctor_set_uint64(x_114, sizeof(void*)*4, x_103);
x_115 = lean_expr_update_let(x_114, x_105, x_108, x_112);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_array_uset(x_116, x_6, x_3);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_dec(x_113);
lean_inc(x_115);
x_119 = lean_array_uset(x_118, x_6, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_110, 1, x_120);
lean_ctor_set(x_110, 0, x_115);
return x_110;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_121 = lean_ctor_get(x_110, 0);
x_122 = lean_ctor_get(x_110, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_110);
x_123 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_123, 0, x_99);
lean_ctor_set(x_123, 1, x_100);
lean_ctor_set(x_123, 2, x_101);
lean_ctor_set(x_123, 3, x_102);
lean_ctor_set_uint64(x_123, sizeof(void*)*4, x_103);
x_124 = lean_expr_update_let(x_123, x_105, x_108, x_121);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
x_126 = lean_array_uset(x_125, x_6, x_3);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_dec(x_122);
lean_inc(x_124);
x_128 = lean_array_uset(x_127, x_6, x_124);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
case 10:
{
lean_object* x_131; lean_object* x_132; uint64_t x_133; lean_object* x_134; uint8_t x_135; 
x_131 = lean_ctor_get(x_3, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_132);
x_134 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_132, x_4);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_138, 0, x_131);
lean_ctor_set(x_138, 1, x_132);
lean_ctor_set_uint64(x_138, sizeof(void*)*2, x_133);
x_139 = lean_expr_update_mdata(x_138, x_136);
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
x_141 = lean_array_uset(x_140, x_6, x_3);
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
lean_dec(x_137);
lean_inc(x_139);
x_143 = lean_array_uset(x_142, x_6, x_139);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_134, 1, x_144);
lean_ctor_set(x_134, 0, x_139);
return x_134;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_145 = lean_ctor_get(x_134, 0);
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_134);
x_147 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_147, 0, x_131);
lean_ctor_set(x_147, 1, x_132);
lean_ctor_set_uint64(x_147, sizeof(void*)*2, x_133);
x_148 = lean_expr_update_mdata(x_147, x_145);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_array_uset(x_149, x_6, x_3);
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
lean_inc(x_148);
x_152 = lean_array_uset(x_151, x_6, x_148);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
case 11:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint64_t x_158; lean_object* x_159; uint8_t x_160; 
x_155 = lean_ctor_get(x_3, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_3, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_3, 2);
lean_inc(x_157);
x_158 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_157);
x_159 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_157, x_4);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_ctor_get(x_159, 1);
x_163 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_156);
lean_ctor_set(x_163, 2, x_157);
lean_ctor_set_uint64(x_163, sizeof(void*)*3, x_158);
x_164 = lean_expr_update_proj(x_163, x_161);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
x_166 = lean_array_uset(x_165, x_6, x_3);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
lean_dec(x_162);
lean_inc(x_164);
x_168 = lean_array_uset(x_167, x_6, x_164);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_159, 1, x_169);
lean_ctor_set(x_159, 0, x_164);
return x_159;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_170 = lean_ctor_get(x_159, 0);
x_171 = lean_ctor_get(x_159, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_159);
x_172 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_172, 0, x_155);
lean_ctor_set(x_172, 1, x_156);
lean_ctor_set(x_172, 2, x_157);
lean_ctor_set_uint64(x_172, sizeof(void*)*3, x_158);
x_173 = lean_expr_update_proj(x_172, x_170);
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
x_175 = lean_array_uset(x_174, x_6, x_3);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_173);
x_177 = lean_array_uset(x_176, x_6, x_173);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
case 12:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_3);
lean_dec(x_1);
x_180 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1;
x_181 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4;
x_182 = lean_panic_fn(x_180, x_181);
x_183 = lean_apply_1(x_182, x_4);
return x_183;
}
default: 
{
lean_object* x_184; 
lean_dec(x_1);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_3);
lean_ctor_set(x_184, 1, x_4);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_1);
x_185 = lean_ctor_get(x_11, 0);
lean_inc(x_185);
lean_dec(x_11);
x_186 = lean_array_uset(x_7, x_6, x_3);
x_187 = lean_ctor_get(x_4, 1);
lean_inc(x_187);
lean_dec(x_4);
lean_inc(x_185);
x_188 = lean_array_uset(x_187, x_6, x_185);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_185);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_191 = lean_ctor_get(x_4, 1);
lean_inc(x_191);
x_192 = lean_array_uget(x_191, x_6);
lean_dec(x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_4);
return x_193;
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_Lean_Expr___instance__11___closed__1;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__2;
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
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__3;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Expr_replace_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_6, x_9, x_10, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_3, x_14, x_15, x_16, x_18);
return x_19;
}
case 7:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_2, x_20, x_21, x_22, x_24);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_5(x_5, x_26, x_27, x_28, x_29, x_31);
return x_32;
}
case 10:
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_3(x_4, x_33, x_34, x_36);
return x_37;
}
case 11:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_4(x_7, x_38, x_39, x_40, x_42);
return x_43;
}
default: 
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_apply_1(x_8, x_1);
return x_44;
}
}
}
}
lean_object* l_Lean_Expr_replace_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_replace_match__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_replace_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_replace_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_replace_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_replace(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Expr_replace(x_1, x_5);
lean_inc(x_6);
x_8 = l_Lean_Expr_replace(x_1, x_6);
x_9 = lean_expr_update_app(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_1);
x_13 = l_Lean_Expr_replace(x_1, x_10);
lean_inc(x_11);
x_14 = l_Lean_Expr_replace(x_1, x_11);
x_15 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint64(x_15, sizeof(void*)*2, x_12);
x_16 = lean_expr_update_app(x_15, x_13, x_14);
return x_16;
}
}
case 6:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_18);
lean_inc(x_1);
x_21 = l_Lean_Expr_replace(x_1, x_18);
lean_inc(x_19);
x_22 = l_Lean_Expr_replace(x_1, x_19);
x_23 = (uint8_t)((x_20 << 24) >> 61);
x_24 = lean_expr_update_lambda(x_2, x_23, x_21, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_26);
lean_inc(x_1);
x_29 = l_Lean_Expr_replace(x_1, x_26);
lean_inc(x_27);
x_30 = l_Lean_Expr_replace(x_1, x_27);
x_31 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_28);
x_32 = (uint8_t)((x_28 << 24) >> 61);
x_33 = lean_expr_update_lambda(x_31, x_32, x_29, x_30);
return x_33;
}
}
case 7:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_35);
lean_inc(x_1);
x_38 = l_Lean_Expr_replace(x_1, x_35);
lean_inc(x_36);
x_39 = l_Lean_Expr_replace(x_1, x_36);
x_40 = (uint8_t)((x_37 << 24) >> 61);
x_41 = lean_expr_update_forall(x_2, x_40, x_38, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
lean_inc(x_43);
lean_inc(x_1);
x_46 = l_Lean_Expr_replace(x_1, x_43);
lean_inc(x_44);
x_47 = l_Lean_Expr_replace(x_1, x_44);
x_48 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set_uint64(x_48, sizeof(void*)*3, x_45);
x_49 = (uint8_t)((x_45 << 24) >> 61);
x_50 = lean_expr_update_forall(x_48, x_49, x_46, x_47);
return x_50;
}
}
case 8:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_52);
lean_inc(x_1);
x_55 = l_Lean_Expr_replace(x_1, x_52);
lean_inc(x_53);
lean_inc(x_1);
x_56 = l_Lean_Expr_replace(x_1, x_53);
lean_inc(x_54);
x_57 = l_Lean_Expr_replace(x_1, x_54);
x_58 = lean_expr_update_let(x_2, x_55, x_56, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_ctor_get(x_2, 2);
x_62 = lean_ctor_get(x_2, 3);
x_63 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_60);
lean_inc(x_1);
x_64 = l_Lean_Expr_replace(x_1, x_60);
lean_inc(x_61);
lean_inc(x_1);
x_65 = l_Lean_Expr_replace(x_1, x_61);
lean_inc(x_62);
x_66 = l_Lean_Expr_replace(x_1, x_62);
x_67 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set_uint64(x_67, sizeof(void*)*4, x_63);
x_68 = lean_expr_update_let(x_67, x_64, x_65, x_66);
return x_68;
}
}
case 10:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = l_Lean_Expr_replace(x_1, x_70);
x_72 = lean_expr_update_mdata(x_2, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint64_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
lean_inc(x_74);
x_76 = l_Lean_Expr_replace(x_1, x_74);
x_77 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set_uint64(x_77, sizeof(void*)*2, x_75);
x_78 = lean_expr_update_mdata(x_77, x_76);
return x_78;
}
}
case 11:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_2);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_2, 2);
lean_inc(x_80);
x_81 = l_Lean_Expr_replace(x_1, x_80);
x_82 = lean_expr_update_proj(x_2, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get(x_2, 1);
x_85 = lean_ctor_get(x_2, 2);
x_86 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_2);
lean_inc(x_85);
x_87 = l_Lean_Expr_replace(x_1, x_85);
x_88 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_85);
lean_ctor_set_uint64(x_88, sizeof(void*)*3, x_86);
x_89 = lean_expr_update_proj(x_88, x_87);
return x_89;
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
lean_object* x_90; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
lean_dec(x_3);
return x_90;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_cacheSize = _init_l_Lean_Expr_ReplaceImpl_cacheSize();
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__3 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__3);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4);
l_Lean_Expr_ReplaceImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__1);
l_Lean_Expr_ReplaceImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__2);
l_Lean_Expr_ReplaceImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__3);
l_Lean_Expr_ReplaceImpl_initCache = _init_l_Lean_Expr_ReplaceImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
