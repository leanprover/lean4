// Lean compiler output
// Module: Lean.Meta.ForEachExpr
// Imports: Init Lean.Expr Lean.Util.MonadCache Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_forEachExpr_x27___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__2(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t l_UInt64_toUSize(uint64_t);
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___closed__1;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ForEachExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1(lean_object*);
static lean_object* l_Lean_Meta_ForEachExpr_visit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_forEachExpr_x27___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__2___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_1, x_5);
x_13 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(x_2, x_12, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 6:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_15 = lean_array_get_size(x_2);
x_16 = lean_expr_instantiate_rev_range(x_12, x_3, x_15, x_2);
lean_dec(x_15);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
lean_inc(x_1);
x_17 = l_Lean_Meta_ForEachExpr_visit(x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = (uint8_t)((x_14 << 24) >> 61);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___lambda__1), 11, 4);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_13);
x_21 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg(x_11, x_19, x_16, x_20, x_5, x_6, x_7, x_8, x_9, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_30 = lean_array_get_size(x_2);
x_31 = lean_expr_instantiate_rev_range(x_27, x_3, x_30, x_2);
lean_dec(x_30);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
lean_inc(x_1);
x_32 = l_Lean_Meta_ForEachExpr_visit(x_1, x_31, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = (uint8_t)((x_29 << 24) >> 61);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___lambda__1), 11, 4);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_1);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_28);
x_36 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg(x_26, x_34, x_31, x_35, x_5, x_6, x_7, x_8, x_9, x_33);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_4, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 3);
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_array_get_size(x_2);
x_46 = lean_expr_instantiate_rev_range(x_42, x_3, x_45, x_2);
lean_dec(x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_46);
lean_inc(x_1);
x_47 = l_Lean_Meta_ForEachExpr_visit(x_1, x_46, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_expr_instantiate_rev_range(x_43, x_3, x_45, x_2);
lean_dec(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_49);
lean_inc(x_1);
x_50 = l_Lean_Meta_ForEachExpr_visit(x_1, x_49, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___lambda__1), 11, 4);
lean_closure_set(x_52, 0, x_2);
lean_closure_set(x_52, 1, x_1);
lean_closure_set(x_52, 2, x_3);
lean_closure_set(x_52, 3, x_44);
x_53 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__2___rarg(x_41, x_46, x_49, x_52, x_5, x_6, x_7, x_8, x_9, x_51);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
default: 
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_array_get_size(x_2);
x_63 = lean_expr_instantiate_rev_range(x_4, x_3, x_62, x_2);
lean_dec(x_2);
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_4);
x_64 = l_Lean_Meta_ForEachExpr_visit(x_1, x_63, x_5, x_6, x_7, x_8, x_9, x_10);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_ForEachExpr_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ForEachExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_2);
x_15 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__1(x_13, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_32; 
lean_free_object(x_11);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_32 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_16 = x_36;
x_17 = x_35;
goto block_31;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_40 = l_Lean_Meta_ForEachExpr_visit(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_7);
lean_inc(x_3);
x_42 = l_Lean_Meta_ForEachExpr_visit(x_1, x_39, x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_16 = x_43;
x_17 = x_44;
goto block_31;
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_40);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_dec(x_32);
x_54 = l_Lean_Meta_ForEachExpr_visit___closed__1;
x_55 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_56 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(x_1, x_54, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_16 = x_57;
x_17 = x_58;
goto block_31;
}
else
{
uint8_t x_59; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 7:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_32, 1);
lean_inc(x_63);
lean_dec(x_32);
x_64 = l_Lean_Meta_ForEachExpr_visit___closed__1;
x_65 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(x_1, x_64, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_16 = x_67;
x_17 = x_68;
goto block_31;
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 8:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_32, 1);
lean_inc(x_73);
lean_dec(x_32);
x_74 = l_Lean_Meta_ForEachExpr_visit___closed__1;
x_75 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_76 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(x_1, x_74, x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_73);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_16 = x_77;
x_17 = x_78;
goto block_31;
}
else
{
uint8_t x_79; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_76);
if (x_79 == 0)
{
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_76);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_32, 1);
lean_inc(x_83);
lean_dec(x_32);
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_inc(x_7);
lean_inc(x_3);
x_85 = l_Lean_Meta_ForEachExpr_visit(x_1, x_84, x_3, x_4, x_5, x_6, x_7, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_16 = x_86;
x_17 = x_87;
goto block_31;
}
else
{
uint8_t x_88; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_85);
if (x_88 == 0)
{
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_85);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
case 11:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_32, 1);
lean_inc(x_92);
lean_dec(x_32);
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
lean_inc(x_7);
lean_inc(x_3);
x_94 = l_Lean_Meta_ForEachExpr_visit(x_1, x_93, x_3, x_4, x_5, x_6, x_7, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_16 = x_95;
x_17 = x_96;
goto block_31;
}
else
{
uint8_t x_97; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
default: 
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_101 = lean_ctor_get(x_32, 1);
lean_inc(x_101);
lean_dec(x_32);
x_102 = lean_box(0);
x_16 = x_102;
x_17 = x_101;
goto block_31;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_32);
if (x_103 == 0)
{
return x_32;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_32, 0);
x_105 = lean_ctor_get(x_32, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_32);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
block_31:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_3, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_instBEqExpr;
x_24 = l_Lean_Expr_instHashableExpr;
lean_inc(x_16);
x_25 = l_Std_HashMap_insert___rarg(x_23, x_24, x_21, x_2, x_16);
x_26 = lean_st_ref_set(x_3, x_25, x_22);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_16);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_107; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_15, 0);
lean_inc(x_107);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_107);
return x_11;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_11, 0);
x_109 = lean_ctor_get(x_11, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_11);
lean_inc(x_2);
x_110 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__1(x_108, x_2);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_126; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_126 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_box(0);
x_111 = x_130;
x_112 = x_129;
goto block_125;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_2, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_134 = l_Lean_Meta_ForEachExpr_visit(x_1, x_132, x_3, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
lean_inc(x_7);
lean_inc(x_3);
x_136 = l_Lean_Meta_ForEachExpr_visit(x_1, x_133, x_3, x_4, x_5, x_6, x_7, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_111 = x_137;
x_112 = x_138;
goto block_125;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_141 = x_136;
} else {
 lean_dec_ref(x_136);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_133);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_134, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_134, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_145 = x_134;
} else {
 lean_dec_ref(x_134);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
case 6:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_126, 1);
lean_inc(x_147);
lean_dec(x_126);
x_148 = l_Lean_Meta_ForEachExpr_visit___closed__1;
x_149 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_150 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(x_1, x_148, x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_147);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_111 = x_151;
x_112 = x_152;
goto block_125;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_155 = x_150;
} else {
 lean_dec_ref(x_150);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
case 7:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_126, 1);
lean_inc(x_157);
lean_dec(x_126);
x_158 = l_Lean_Meta_ForEachExpr_visit___closed__1;
x_159 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_160 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(x_1, x_158, x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_157);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_111 = x_161;
x_112 = x_162;
goto block_125;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_165 = x_160;
} else {
 lean_dec_ref(x_160);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
case 8:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_126, 1);
lean_inc(x_167);
lean_dec(x_126);
x_168 = l_Lean_Meta_ForEachExpr_visit___closed__1;
x_169 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_170 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder(x_1, x_168, x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_111 = x_171;
x_112 = x_172;
goto block_125;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_175 = x_170;
} else {
 lean_dec_ref(x_170);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
case 10:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_126, 1);
lean_inc(x_177);
lean_dec(x_126);
x_178 = lean_ctor_get(x_2, 1);
lean_inc(x_178);
lean_inc(x_7);
lean_inc(x_3);
x_179 = l_Lean_Meta_ForEachExpr_visit(x_1, x_178, x_3, x_4, x_5, x_6, x_7, x_177);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_111 = x_180;
x_112 = x_181;
goto block_125;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_ctor_get(x_179, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_184 = x_179;
} else {
 lean_dec_ref(x_179);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
case 11:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_126, 1);
lean_inc(x_186);
lean_dec(x_126);
x_187 = lean_ctor_get(x_2, 2);
lean_inc(x_187);
lean_inc(x_7);
lean_inc(x_3);
x_188 = l_Lean_Meta_ForEachExpr_visit(x_1, x_187, x_3, x_4, x_5, x_6, x_7, x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_111 = x_189;
x_112 = x_190;
goto block_125;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
default: 
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_195 = lean_ctor_get(x_126, 1);
lean_inc(x_195);
lean_dec(x_126);
x_196 = lean_box(0);
x_111 = x_196;
x_112 = x_195;
goto block_125;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_126, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_126, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_199 = x_126;
} else {
 lean_dec_ref(x_126);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
block_125:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_st_ref_get(x_7, x_112);
lean_dec(x_7);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_ref_take(x_3, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Expr_instBEqExpr;
x_119 = l_Lean_Expr_instHashableExpr;
lean_inc(x_111);
x_120 = l_Std_HashMap_insert___rarg(x_118, x_119, x_116, x_2, x_111);
x_121 = lean_st_ref_set(x_3, x_120, x_117);
lean_dec(x_3);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_111);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_110, 0);
lean_inc(x_201);
lean_dec(x_110);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_109);
return x_202;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_forEachExpr_x27___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_forEachExpr_x27___closed__1;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l_Lean_Meta_ForEachExpr_visit(x_2, x_1, x_12, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_6, x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_12, x_18);
lean_dec(x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_forEachExpr_x27___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Meta_forEachExpr_x27___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = 1;
x_12 = lean_box(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_forEachExpr_x27(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_Util_MonadCache(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ForEachExpr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_ForEachExpr_visit___closed__1 = _init_l_Lean_Meta_ForEachExpr_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_ForEachExpr_visit___closed__1);
l_Lean_Meta_forEachExpr_x27___closed__1 = _init_l_Lean_Meta_forEachExpr_x27___closed__1();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
