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
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_ForEachExpr_visit___main___spec__11___boxed(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_ForEachExpr_visit___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__9(lean_object*);
lean_object* l_Lean_Meta_forEachExpr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_27__withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExprImp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_ForEachExpr_visit___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_forEachExpr___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr(lean_object*);
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2;
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_28__withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_ForEachExpr_visit___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_ForEachExpr_visit___main___spec__5(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_forEachExpr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_forEachExpr___spec__1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_ForEachExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
lean_object* l_Lean_Meta_forEachExprImp_x27___closed__1;
extern lean_object* l_ReaderT_monadControl___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_ForEachExpr_visit___main___spec__11(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_ForEachExpr_visit___main___spec__3(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27(lean_object*);
lean_object* l_monadControlTrans___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_ForEachExpr_visit___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_ForEachExpr_visit___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ForEachExpr_visit___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_forEachExprImp_x27___spec__1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_1, x_5);
x_13 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main(x_2, x_12, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_2 = l_ReaderT_monadControl___closed__2;
x_3 = l_monadControlTrans___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
switch (lean_obj_tag(x_4)) {
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_20 = lean_array_get_size(x_2);
x_21 = lean_expr_instantiate_rev_range(x_17, x_3, x_20, x_2);
lean_dec(x_20);
lean_dec(x_17);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = lean_apply_7(x_1, x_21, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = (uint8_t)((x_19 << 24) >> 61);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___lambda__1), 11, 4);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_18);
x_26 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2;
x_27 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1;
x_28 = l_Lean_Meta_withLocalDecl___rarg(x_26, x_27, lean_box(0), x_16, x_24, x_21, x_25);
x_29 = lean_apply_6(x_28, x_5, x_6, x_7, x_8, x_9, x_23);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_38 = lean_array_get_size(x_2);
x_39 = lean_expr_instantiate_rev_range(x_35, x_3, x_38, x_2);
lean_dec(x_38);
lean_dec(x_35);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_39);
x_40 = lean_apply_7(x_1, x_39, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = (uint8_t)((x_37 << 24) >> 61);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___lambda__1), 11, 4);
lean_closure_set(x_43, 0, x_2);
lean_closure_set(x_43, 1, x_1);
lean_closure_set(x_43, 2, x_3);
lean_closure_set(x_43, 3, x_36);
x_44 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2;
x_45 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1;
x_46 = l_Lean_Meta_withLocalDecl___rarg(x_44, x_45, lean_box(0), x_34, x_42, x_39, x_43);
x_47 = lean_apply_6(x_46, x_5, x_6, x_7, x_8, x_9, x_41);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 3);
lean_inc(x_55);
lean_dec(x_4);
x_56 = lean_array_get_size(x_2);
x_57 = lean_expr_instantiate_rev_range(x_53, x_3, x_56, x_2);
lean_dec(x_53);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_57);
x_58 = lean_apply_7(x_1, x_57, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_expr_instantiate_rev_range(x_54, x_3, x_56, x_2);
lean_dec(x_56);
lean_dec(x_54);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
x_61 = lean_apply_7(x_1, x_60, x_5, x_6, x_7, x_8, x_9, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___lambda__1), 11, 4);
lean_closure_set(x_63, 0, x_2);
lean_closure_set(x_63, 1, x_1);
lean_closure_set(x_63, 2, x_3);
lean_closure_set(x_63, 3, x_55);
x_64 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2;
x_65 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1;
x_66 = l_Lean_Meta_withLetDecl___rarg(x_64, x_65, lean_box(0), x_52, x_57, x_60, x_63);
x_67 = lean_apply_6(x_66, x_5, x_6, x_7, x_8, x_9, x_62);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_58);
if (x_72 == 0)
{
return x_58;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_58, 0);
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_58);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
default: 
{
lean_object* x_76; 
x_76 = lean_box(0);
x_11 = x_76;
goto block_15;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_12 = lean_array_get_size(x_2);
x_13 = lean_expr_instantiate_rev_range(x_4, x_3, x_12, x_2);
lean_dec(x_2);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_4);
x_14 = lean_apply_7(x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_ForEachExpr_visit___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Std_AssocList_foldlM___main___at_Lean_Meta_ForEachExpr_visit___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_ForEachExpr_visit___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___main___at_Lean_Meta_ForEachExpr_visit___main___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_ForEachExpr_visit___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_ForEachExpr_visit___main___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at_Lean_Meta_ForEachExpr_visit___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_AssocList_replace___main___at_Lean_Meta_ForEachExpr_visit___main___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_AssocList_replace___main___at_Lean_Meta_ForEachExpr_visit___main___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_ForEachExpr_visit___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___main___at_Lean_Meta_ForEachExpr_visit___main___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_Meta_ForEachExpr_visit___main___spec__3(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___main___at_Lean_Meta_ForEachExpr_visit___main___spec__6(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___main___at_Lean_Meta_ForEachExpr_visit___main___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_Meta_ForEachExpr_visit___main___spec__3(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___main___at_Lean_Meta_ForEachExpr_visit___main___spec__6(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_27__withLocalDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_28__withLetDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__9___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_1, x_5);
x_13 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7(x_2, x_12, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
switch (lean_obj_tag(x_4)) {
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_20 = lean_array_get_size(x_2);
x_21 = lean_expr_instantiate_rev_range(x_17, x_3, x_20, x_2);
lean_dec(x_20);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
lean_inc(x_1);
x_22 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_21, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = (uint8_t)((x_19 << 24) >> 61);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7___lambda__1), 11, 4);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_18);
x_26 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg(x_16, x_24, x_21, x_25, x_5, x_6, x_7, x_8, x_9, x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
case 7:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_35 = lean_array_get_size(x_2);
x_36 = lean_expr_instantiate_rev_range(x_32, x_3, x_35, x_2);
lean_dec(x_35);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
lean_inc(x_1);
x_37 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_36, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = (uint8_t)((x_34 << 24) >> 61);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7___lambda__1), 11, 4);
lean_closure_set(x_40, 0, x_2);
lean_closure_set(x_40, 1, x_1);
lean_closure_set(x_40, 2, x_3);
lean_closure_set(x_40, 3, x_33);
x_41 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg(x_31, x_39, x_36, x_40, x_5, x_6, x_7, x_8, x_9, x_38);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 3);
lean_inc(x_49);
lean_dec(x_4);
x_50 = lean_array_get_size(x_2);
x_51 = lean_expr_instantiate_rev_range(x_47, x_3, x_50, x_2);
lean_dec(x_47);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_51);
lean_inc(x_1);
x_52 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_51, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_expr_instantiate_rev_range(x_48, x_3, x_50, x_2);
lean_dec(x_50);
lean_dec(x_48);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_54);
lean_inc(x_1);
x_55 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_54, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7___lambda__1), 11, 4);
lean_closure_set(x_57, 0, x_2);
lean_closure_set(x_57, 1, x_1);
lean_closure_set(x_57, 2, x_3);
lean_closure_set(x_57, 3, x_49);
x_58 = l_Lean_Meta_withLetDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__9___rarg(x_46, x_51, x_54, x_57, x_5, x_6, x_7, x_8, x_9, x_56);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
default: 
{
lean_object* x_67; 
x_67 = lean_box(0);
x_11 = x_67;
goto block_15;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_12 = lean_array_get_size(x_2);
x_13 = lean_expr_instantiate_rev_range(x_4, x_3, x_12, x_2);
lean_dec(x_2);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_4);
x_14 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_ForEachExpr_visit___main___spec__11(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_ForEachExpr_visit___main___spec__11(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_ForEachExpr_visit___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_21; lean_object* x_22; lean_object* x_71; uint8_t x_72; 
x_71 = lean_st_ref_get(x_3, x_8);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(x_73, x_2);
lean_dec(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_free_object(x_71);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_76 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = 1;
x_21 = x_80;
x_22 = x_79;
goto block_70;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_dec(x_76);
x_82 = 0;
x_21 = x_82;
x_22 = x_81;
goto block_70;
}
}
else
{
uint8_t x_83; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_76);
if (x_83 == 0)
{
return x_76;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_76, 0);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_76);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_75, 0);
lean_inc(x_87);
lean_dec(x_75);
lean_ctor_set(x_71, 0, x_87);
return x_71;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_71, 0);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_71);
x_90 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(x_88, x_2);
lean_dec(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_91 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = 1;
x_21 = x_95;
x_22 = x_94;
goto block_70;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = 0;
x_21 = x_97;
x_22 = x_96;
goto block_70;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_91, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_100 = x_91;
} else {
 lean_dec_ref(x_91);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
lean_dec(x_90);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_89);
return x_103;
}
}
block_20:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l_Std_HashMapImp_insert___at_Lean_Meta_ForEachExpr_visit___main___spec__1(x_12, x_2, x_9);
x_15 = lean_st_ref_set(x_3, x_14, x_13);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
block_70:
{
lean_object* x_23; 
if (x_21 == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_36 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_3);
x_38 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_9 = x_39;
x_10 = x_40;
goto block_20;
}
else
{
uint8_t x_41; 
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_36);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 6:
{
lean_object* x_49; 
x_49 = lean_box(0);
x_23 = x_49;
goto block_33;
}
case 7:
{
lean_object* x_50; 
x_50 = lean_box(0);
x_23 = x_50;
goto block_33;
}
case 8:
{
lean_object* x_51; 
x_51 = lean_box(0);
x_23 = x_51;
goto block_33;
}
case 10:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_inc(x_3);
x_53 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_52, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_9 = x_54;
x_10 = x_55;
goto block_20;
}
else
{
uint8_t x_56; 
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 11:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_inc(x_3);
x_61 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_60, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_9 = x_62;
x_10 = x_63;
goto block_20;
}
else
{
uint8_t x_64; 
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
default: 
{
lean_object* x_68; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_68 = lean_box(0);
x_9 = x_68;
x_10 = x_22;
goto block_20;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = lean_box(0);
x_9 = x_69;
x_10 = x_22;
goto block_20;
}
block_33:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
x_24 = l_Array_empty___closed__1;
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___at_Lean_Meta_ForEachExpr_visit___main___spec__7(x_1, x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_9 = x_27;
x_10 = x_28;
goto block_20;
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
lean_object* l_Std_AssocList_contains___main___at_Lean_Meta_ForEachExpr_visit___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at_Lean_Meta_ForEachExpr_visit___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_ForEachExpr_visit___main___spec__8___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_ForEachExpr_visit___main___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_ForEachExpr_visit___main___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_ForEachExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_ForEachExpr_visit___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Meta_forEachExprImp_x27___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_forEachExprImp_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_forEachExprImp_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_forEachExprImp_x27___closed__1;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_ForEachExpr_visit___main(x_2, x_1, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExprImp_x27), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_forEachExpr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExprImp_x27), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_forEachExpr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_forEachExpr___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forEachExpr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_forEachExpr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___rarg___lambda__1), 7, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_forEachExpr___spec__1___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_forEachExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_Util_MonadCache(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_ForEachExpr(lean_object* w) {
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
l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1 = _init_l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__1);
l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2 = _init_l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_ForEachExpr_1__visitBinder___main___closed__2);
l_Lean_Meta_forEachExprImp_x27___closed__1 = _init_l_Lean_Meta_forEachExprImp_x27___closed__1();
lean_mark_persistent(l_Lean_Meta_forEachExprImp_x27___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
