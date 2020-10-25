// Lean compiler output
// Module: Lean.Util.ReplaceLevel
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
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceLevel_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Level_replace_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
lean_object* l_Lean_Expr_replaceLevel_match__1(lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__4;
size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* l_Lean_Level_replace_match__2(lean_object*);
lean_object* l_List_map___at_Lean_Expr_replaceLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Level_replace_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_match__1(lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Format_0__Lean_Format_be___closed__1;
lean_object* l_Init_Control_Monad___instance__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11___closed__1;
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
lean_object* l_Lean_Level_replace_match__1(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__2;
lean_object* l_Lean_Level_replace_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_2(x_4, x_6, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_2, x_10, x_11, x_13);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_3, x_15, x_16, x_18);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_5, x_1);
return x_20;
}
}
}
}
lean_object* l_Lean_Level_replace_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_replace_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Level_replace_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Level_replace_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_replace_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Level_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Level_replace(x_1, x_4);
x_6 = l_Lean_mkLevelSucc(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Level_replace(x_1, x_7);
x_10 = l_Lean_Level_replace(x_1, x_8);
x_11 = l_Lean_mkLevelMax(x_9, x_10);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Level_replace(x_1, x_12);
x_15 = l_Lean_Level_replace(x_1, x_13);
x_16 = l_Lean_mkLevelIMax(x_14, x_15);
return x_16;
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
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
return x_17;
}
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceLevelImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_2(x_8, x_12, x_14);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_3(x_9, x_16, x_17, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_3(x_6, x_21, x_22, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_4(x_3, x_26, x_27, x_28, x_30);
return x_31;
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_4(x_2, x_32, x_33, x_34, x_36);
return x_37;
}
case 8:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_43 = lean_box_uint64(x_42);
x_44 = lean_apply_5(x_5, x_38, x_39, x_40, x_41, x_43);
return x_44;
}
case 10:
{
lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_48 = lean_box_uint64(x_47);
x_49 = lean_apply_3(x_4, x_45, x_46, x_48);
return x_49;
}
case 11:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_54 = lean_box_uint64(x_53);
x_55 = lean_apply_4(x_7, x_50, x_51, x_52, x_54);
return x_55;
}
case 12:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_60 = lean_box_uint64(x_59);
x_61 = lean_apply_4(x_10, x_56, x_57, x_58, x_60);
return x_61;
}
default: 
{
lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_apply_1(x_11, x_1);
return x_62;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_match__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_Lean_Level_replace(x_1, x_5);
x_8 = l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Level_replace(x_1, x_9);
x_12 = l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Format_0__Lean_Format_be___closed__1;
x_2 = l_Lean_Expr_Lean_Expr___instance__11;
x_3 = l_Init_Control_Monad___instance__2___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Util.ReplaceLevel");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.ReplaceLevelImpl.replaceUnsafeM.visit");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__2;
x_2 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__3;
x_3 = lean_unsigned_to_nat(54u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_inc(x_11);
x_13 = l_Lean_Level_replace(x_1, x_11);
x_14 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set_uint64(x_14, sizeof(void*)*1, x_12);
x_15 = lean_expr_update_sort(x_14, x_13);
x_16 = lean_array_uset(x_7, x_6, x_3);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
lean_inc(x_15);
x_18 = lean_array_uset(x_17, x_6, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_22);
x_24 = l_List_map___at_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___spec__1(x_1, x_22);
x_25 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_23);
x_26 = lean_expr_update_const(x_25, x_24);
x_27 = lean_array_uset(x_7, x_6, x_3);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
lean_inc(x_26);
x_29 = lean_array_uset(x_28, x_6, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
case 5:
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_7);
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_32);
lean_inc(x_1);
x_35 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_32, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_33);
x_38 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_33, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set_uint64(x_42, sizeof(void*)*2, x_34);
x_43 = lean_expr_update_app(x_42, x_36, x_40);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
x_45 = lean_array_uset(x_44, x_6, x_3);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
lean_inc(x_43);
x_47 = lean_array_uset(x_46, x_6, x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_38, 1, x_48);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_51, 0, x_32);
lean_ctor_set(x_51, 1, x_33);
lean_ctor_set_uint64(x_51, sizeof(void*)*2, x_34);
x_52 = lean_expr_update_app(x_51, x_36, x_49);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_array_uset(x_53, x_6, x_3);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec(x_50);
lean_inc(x_52);
x_56 = lean_array_uset(x_55, x_6, x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
case 6:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_7);
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 2);
lean_inc(x_61);
x_62 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_60);
lean_inc(x_1);
x_63 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_60, x_4);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_61);
x_66 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_61, x_65);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_70, 2, x_61);
lean_ctor_set_uint64(x_70, sizeof(void*)*3, x_62);
x_71 = (uint8_t)((x_62 << 24) >> 61);
x_72 = lean_expr_update_lambda(x_70, x_71, x_64, x_68);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_array_uset(x_73, x_6, x_3);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
lean_inc(x_72);
x_76 = lean_array_uset(x_75, x_6, x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_66, 1, x_77);
lean_ctor_set(x_66, 0, x_72);
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_ctor_get(x_66, 0);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_66);
x_80 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_80, 0, x_59);
lean_ctor_set(x_80, 1, x_60);
lean_ctor_set(x_80, 2, x_61);
lean_ctor_set_uint64(x_80, sizeof(void*)*3, x_62);
x_81 = (uint8_t)((x_62 << 24) >> 61);
x_82 = lean_expr_update_lambda(x_80, x_81, x_64, x_78);
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
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
case 7:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_7);
x_89 = lean_ctor_get(x_3, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 2);
lean_inc(x_91);
x_92 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_90);
lean_inc(x_1);
x_93 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_90, x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_91);
x_96 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_91, x_95);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
x_100 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_90);
lean_ctor_set(x_100, 2, x_91);
lean_ctor_set_uint64(x_100, sizeof(void*)*3, x_92);
x_101 = (uint8_t)((x_92 << 24) >> 61);
x_102 = lean_expr_update_forall(x_100, x_101, x_94, x_98);
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_array_uset(x_103, x_6, x_3);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
lean_inc(x_102);
x_106 = lean_array_uset(x_105, x_6, x_102);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_96, 1, x_107);
lean_ctor_set(x_96, 0, x_102);
return x_96;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_108 = lean_ctor_get(x_96, 0);
x_109 = lean_ctor_get(x_96, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_96);
x_110 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_110, 0, x_89);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_91);
lean_ctor_set_uint64(x_110, sizeof(void*)*3, x_92);
x_111 = (uint8_t)((x_92 << 24) >> 61);
x_112 = lean_expr_update_forall(x_110, x_111, x_94, x_108);
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
x_114 = lean_array_uset(x_113, x_6, x_3);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_dec(x_109);
lean_inc(x_112);
x_116 = lean_array_uset(x_115, x_6, x_112);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
case 8:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint64_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_7);
x_119 = lean_ctor_get(x_3, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_3, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_3, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_3, 3);
lean_inc(x_122);
x_123 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_120);
lean_inc(x_1);
x_124 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_120, x_4);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_121);
lean_inc(x_1);
x_127 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_121, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_122);
x_130 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_122, x_129);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ctor_get(x_130, 1);
x_134 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_134, 0, x_119);
lean_ctor_set(x_134, 1, x_120);
lean_ctor_set(x_134, 2, x_121);
lean_ctor_set(x_134, 3, x_122);
lean_ctor_set_uint64(x_134, sizeof(void*)*4, x_123);
x_135 = lean_expr_update_let(x_134, x_125, x_128, x_132);
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
x_137 = lean_array_uset(x_136, x_6, x_3);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_dec(x_133);
lean_inc(x_135);
x_139 = lean_array_uset(x_138, x_6, x_135);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_130, 1, x_140);
lean_ctor_set(x_130, 0, x_135);
return x_130;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_141 = lean_ctor_get(x_130, 0);
x_142 = lean_ctor_get(x_130, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_130);
x_143 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_143, 0, x_119);
lean_ctor_set(x_143, 1, x_120);
lean_ctor_set(x_143, 2, x_121);
lean_ctor_set(x_143, 3, x_122);
lean_ctor_set_uint64(x_143, sizeof(void*)*4, x_123);
x_144 = lean_expr_update_let(x_143, x_125, x_128, x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_array_uset(x_145, x_6, x_3);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
lean_inc(x_144);
x_148 = lean_array_uset(x_147, x_6, x_144);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_144);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
case 10:
{
lean_object* x_151; lean_object* x_152; uint64_t x_153; lean_object* x_154; uint8_t x_155; 
lean_dec(x_7);
x_151 = lean_ctor_get(x_3, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_3, 1);
lean_inc(x_152);
x_153 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_152);
x_154 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_152, x_4);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_ctor_get(x_154, 1);
x_158 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set_uint64(x_158, sizeof(void*)*2, x_153);
x_159 = lean_expr_update_mdata(x_158, x_156);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_array_uset(x_160, x_6, x_3);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_dec(x_157);
lean_inc(x_159);
x_163 = lean_array_uset(x_162, x_6, x_159);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_154, 1, x_164);
lean_ctor_set(x_154, 0, x_159);
return x_154;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_154, 0);
x_166 = lean_ctor_get(x_154, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_154);
x_167 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_167, 0, x_151);
lean_ctor_set(x_167, 1, x_152);
lean_ctor_set_uint64(x_167, sizeof(void*)*2, x_153);
x_168 = lean_expr_update_mdata(x_167, x_165);
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
x_170 = lean_array_uset(x_169, x_6, x_3);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
lean_inc(x_168);
x_172 = lean_array_uset(x_171, x_6, x_168);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_168);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
case 11:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint64_t x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_7);
x_175 = lean_ctor_get(x_3, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_3, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_3, 2);
lean_inc(x_177);
x_178 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_177);
x_179 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_177, x_4);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
x_183 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_183, 0, x_175);
lean_ctor_set(x_183, 1, x_176);
lean_ctor_set(x_183, 2, x_177);
lean_ctor_set_uint64(x_183, sizeof(void*)*3, x_178);
x_184 = lean_expr_update_proj(x_183, x_181);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
x_186 = lean_array_uset(x_185, x_6, x_3);
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
lean_inc(x_184);
x_188 = lean_array_uset(x_187, x_6, x_184);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_179, 1, x_189);
lean_ctor_set(x_179, 0, x_184);
return x_179;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_190 = lean_ctor_get(x_179, 0);
x_191 = lean_ctor_get(x_179, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_179);
x_192 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_192, 0, x_175);
lean_ctor_set(x_192, 1, x_176);
lean_ctor_set(x_192, 2, x_177);
lean_ctor_set_uint64(x_192, sizeof(void*)*3, x_178);
x_193 = lean_expr_update_proj(x_192, x_190);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
x_195 = lean_array_uset(x_194, x_6, x_3);
x_196 = lean_ctor_get(x_191, 1);
lean_inc(x_196);
lean_dec(x_191);
lean_inc(x_193);
x_197 = lean_array_uset(x_196, x_6, x_193);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
case 12:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_200 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__1;
x_201 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__4;
x_202 = lean_panic_fn(x_200, x_201);
x_203 = lean_apply_1(x_202, x_4);
return x_203;
}
default: 
{
lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_1);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_3);
lean_ctor_set(x_204, 1, x_4);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_205 = lean_ctor_get(x_4, 1);
lean_inc(x_205);
x_206 = lean_array_uget(x_205, x_6);
lean_dec(x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_4);
return x_207;
}
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_Lean_Expr___instance__11___closed__1;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_replaceLevel_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_8, x_1, x_11, x_13);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_9, x_1, x_15, x_16, x_18);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_4(x_6, x_1, x_20, x_21, x_23);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_5(x_3, x_1, x_25, x_26, x_27, x_29);
return x_30;
}
case 7:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_35 = lean_box_uint64(x_34);
x_36 = lean_apply_5(x_2, x_1, x_31, x_32, x_33, x_35);
return x_36;
}
case 8:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_6(x_5, x_1, x_37, x_38, x_39, x_40, x_42);
return x_43;
}
case 10:
{
lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_4(x_4, x_1, x_44, x_45, x_47);
return x_48;
}
case 11:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_53 = lean_box_uint64(x_52);
x_54 = lean_apply_5(x_7, x_1, x_49, x_50, x_51, x_53);
return x_54;
}
default: 
{
lean_object* x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_apply_1(x_10, x_1);
return x_55;
}
}
}
}
lean_object* l_Lean_Expr_replaceLevel_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_replaceLevel_match__1___rarg), 10, 0);
return x_2;
}
}
lean_object* l_List_map___at_Lean_Expr_replaceLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_Lean_Level_replace(x_1, x_5);
x_8 = l_List_map___at_Lean_Expr_replaceLevel___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Level_replace(x_1, x_9);
x_12 = l_List_map___at_Lean_Expr_replaceLevel___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Expr_replaceLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Level_replace(x_1, x_4);
x_6 = lean_expr_update_sort(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_7);
x_9 = l_Lean_Level_replace(x_1, x_7);
x_10 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_8);
x_11 = lean_expr_update_sort(x_10, x_9);
return x_11;
}
}
case 4:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = l_List_map___at_Lean_Expr_replaceLevel___spec__1(x_1, x_13);
x_15 = lean_expr_update_const(x_2, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_17);
x_19 = l_List_map___at_Lean_Expr_replaceLevel___spec__1(x_1, x_17);
x_20 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set_uint64(x_20, sizeof(void*)*2, x_18);
x_21 = lean_expr_update_const(x_20, x_19);
return x_21;
}
}
case 5:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_1);
x_25 = l_Lean_Expr_replaceLevel(x_1, x_23);
lean_inc(x_24);
x_26 = l_Lean_Expr_replaceLevel(x_1, x_24);
x_27 = lean_expr_update_app(x_2, x_25, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
lean_inc(x_28);
lean_inc(x_1);
x_31 = l_Lean_Expr_replaceLevel(x_1, x_28);
lean_inc(x_29);
x_32 = l_Lean_Expr_replaceLevel(x_1, x_29);
x_33 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set_uint64(x_33, sizeof(void*)*2, x_30);
x_34 = lean_expr_update_app(x_33, x_31, x_32);
return x_34;
}
}
case 6:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_36);
lean_inc(x_1);
x_39 = l_Lean_Expr_replaceLevel(x_1, x_36);
lean_inc(x_37);
x_40 = l_Lean_Expr_replaceLevel(x_1, x_37);
x_41 = (uint8_t)((x_38 << 24) >> 61);
x_42 = lean_expr_update_lambda(x_2, x_41, x_39, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
lean_inc(x_44);
lean_inc(x_1);
x_47 = l_Lean_Expr_replaceLevel(x_1, x_44);
lean_inc(x_45);
x_48 = l_Lean_Expr_replaceLevel(x_1, x_45);
x_49 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_46);
x_50 = (uint8_t)((x_46 << 24) >> 61);
x_51 = lean_expr_update_lambda(x_49, x_50, x_47, x_48);
return x_51;
}
}
case 7:
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_2, 1);
x_54 = lean_ctor_get(x_2, 2);
x_55 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_53);
lean_inc(x_1);
x_56 = l_Lean_Expr_replaceLevel(x_1, x_53);
lean_inc(x_54);
x_57 = l_Lean_Expr_replaceLevel(x_1, x_54);
x_58 = (uint8_t)((x_55 << 24) >> 61);
x_59 = lean_expr_update_forall(x_2, x_58, x_56, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
x_62 = lean_ctor_get(x_2, 2);
x_63 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_2);
lean_inc(x_61);
lean_inc(x_1);
x_64 = l_Lean_Expr_replaceLevel(x_1, x_61);
lean_inc(x_62);
x_65 = l_Lean_Expr_replaceLevel(x_1, x_62);
x_66 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set_uint64(x_66, sizeof(void*)*3, x_63);
x_67 = (uint8_t)((x_63 << 24) >> 61);
x_68 = lean_expr_update_forall(x_66, x_67, x_64, x_65);
return x_68;
}
}
case 8:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
lean_inc(x_70);
lean_inc(x_1);
x_73 = l_Lean_Expr_replaceLevel(x_1, x_70);
lean_inc(x_71);
lean_inc(x_1);
x_74 = l_Lean_Expr_replaceLevel(x_1, x_71);
lean_inc(x_72);
x_75 = l_Lean_Expr_replaceLevel(x_1, x_72);
x_76 = lean_expr_update_let(x_2, x_73, x_74, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
x_79 = lean_ctor_get(x_2, 2);
x_80 = lean_ctor_get(x_2, 3);
x_81 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_2);
lean_inc(x_78);
lean_inc(x_1);
x_82 = l_Lean_Expr_replaceLevel(x_1, x_78);
lean_inc(x_79);
lean_inc(x_1);
x_83 = l_Lean_Expr_replaceLevel(x_1, x_79);
lean_inc(x_80);
x_84 = l_Lean_Expr_replaceLevel(x_1, x_80);
x_85 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_80);
lean_ctor_set_uint64(x_85, sizeof(void*)*4, x_81);
x_86 = lean_expr_update_let(x_85, x_82, x_83, x_84);
return x_86;
}
}
case 10:
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_2);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
x_89 = l_Lean_Expr_replaceLevel(x_1, x_88);
x_90 = lean_expr_update_mdata(x_2, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; uint64_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_2, 0);
x_92 = lean_ctor_get(x_2, 1);
x_93 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_2);
lean_inc(x_92);
x_94 = l_Lean_Expr_replaceLevel(x_1, x_92);
x_95 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_92);
lean_ctor_set_uint64(x_95, sizeof(void*)*2, x_93);
x_96 = lean_expr_update_mdata(x_95, x_94);
return x_96;
}
}
case 11:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_2);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_2, 2);
lean_inc(x_98);
x_99 = l_Lean_Expr_replaceLevel(x_1, x_98);
x_100 = lean_expr_update_proj(x_2, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_2, 0);
x_102 = lean_ctor_get(x_2, 1);
x_103 = lean_ctor_get(x_2, 2);
x_104 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_2);
lean_inc(x_103);
x_105 = l_Lean_Expr_replaceLevel(x_1, x_103);
x_106 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_102);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set_uint64(x_106, sizeof(void*)*3, x_104);
x_107 = lean_expr_update_proj(x_106, x_105);
return x_107;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_ReplaceLevel(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__1);
l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__2 = _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__2);
l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__3 = _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__3);
l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__4 = _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__4();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___closed__4);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3);
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
