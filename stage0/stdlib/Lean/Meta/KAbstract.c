// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Init Lean.Data.Occurrences Lean.HeadIndex Lean.Meta.ExprDefEq
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
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
extern lean_object* l_Lean_Meta_isLevelDefEqAux___closed__6;
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit_match__1(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__1___rarg(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_2, x_9, x_10, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_19 = lean_apply_4(x_6, x_14, x_15, x_16, x_18);
return x_19;
}
case 7:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_7, x_20, x_21, x_22, x_24);
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
lean_dec(x_4);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_3(x_3, x_33, x_34, x_36);
return x_37;
}
case 11:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_43 = lean_apply_4(x_4, x_38, x_39, x_40, x_42);
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
lean_object* l_Lean_Meta_kabstract_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract_visit_match__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_42, 0, x_58);
return x_42;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_dec(x_42);
x_20 = x_63;
x_21 = x_64;
goto block_27;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_dec(x_28);
x_20 = x_65;
x_21 = x_66;
goto block_27;
}
block_27:
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_42, 0, x_58);
return x_42;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_dec(x_42);
x_20 = x_63;
x_21 = x_64;
goto block_27;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_dec(x_28);
x_20 = x_65;
x_21 = x_66;
goto block_27;
}
block_27:
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_18; lean_object* x_19; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_423 = lean_st_ref_get(x_7, x_8);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_424, 3);
lean_inc(x_425);
lean_dec(x_424);
x_426 = lean_ctor_get_uint8(x_425, sizeof(void*)*1);
lean_dec(x_425);
if (x_426 == 0)
{
lean_object* x_427; uint8_t x_428; 
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
lean_dec(x_423);
x_428 = 0;
x_18 = x_428;
x_19 = x_427;
goto block_422;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_429 = lean_ctor_get(x_423, 1);
lean_inc(x_429);
lean_dec(x_423);
x_430 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_431 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_430, x_4, x_5, x_6, x_7, x_429);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_unbox(x_432);
lean_dec(x_432);
x_18 = x_434;
x_19 = x_433;
goto block_422;
}
block_17:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
block_422:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_st_ref_get(x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
lean_dec(x_22);
x_25 = lean_st_ref_take(x_7, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 3);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_84; lean_object* x_85; 
x_32 = 0;
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_32);
x_33 = lean_st_ref_set(x_7, x_26, x_28);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_84 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_85 = l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2(x_1, x_2, x_84, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_116 = lean_st_ref_get(x_7, x_87);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 3);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_dec(x_116);
x_88 = x_32;
x_89 = x_120;
goto block_115;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_123 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_122, x_4, x_5, x_6, x_7, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_unbox(x_124);
lean_dec(x_124);
x_88 = x_126;
x_89 = x_125;
goto block_115;
}
block_115:
{
if (x_88 == 0)
{
uint8_t x_90; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_unbox(x_86);
lean_dec(x_86);
x_35 = x_90;
x_36 = x_89;
goto block_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_1);
x_92 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_2);
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_unbox(x_86);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_101 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_92);
x_104 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_105 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_104, x_103, x_4, x_5, x_6, x_7, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_unbox(x_86);
lean_dec(x_86);
x_35 = x_107;
x_36 = x_106;
goto block_83;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_108 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_92);
x_111 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_112 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_111, x_110, x_4, x_5, x_6, x_7, x_89);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_unbox(x_86);
lean_dec(x_86);
x_35 = x_114;
x_36 = x_113;
goto block_83;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_ctor_get(x_85, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_85, 1);
lean_inc(x_128);
lean_dec(x_85);
x_129 = lean_st_ref_get(x_7, x_128);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_st_ref_take(x_7, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = !lean_is_exclusive(x_132);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_132, 3);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_133);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_24);
x_138 = lean_st_ref_set(x_7, x_132, x_134);
lean_dec(x_7);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set_tag(x_138, 1);
lean_ctor_set(x_138, 0, x_127);
return x_138;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_127);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_133, 0);
lean_inc(x_143);
lean_dec(x_133);
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_24);
lean_ctor_set(x_132, 3, x_144);
x_145 = lean_st_ref_set(x_7, x_132, x_134);
lean_dec(x_7);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_127);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_149 = lean_ctor_get(x_132, 0);
x_150 = lean_ctor_get(x_132, 1);
x_151 = lean_ctor_get(x_132, 2);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_132);
x_152 = lean_ctor_get(x_133, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_153 = x_133;
} else {
 lean_dec_ref(x_133);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 1, 1);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_24);
x_155 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_150);
lean_ctor_set(x_155, 2, x_151);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_st_ref_set(x_7, x_155, x_134);
lean_dec(x_7);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_127);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
block_83:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_37 = lean_st_ref_get(x_7, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 3);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
lean_dec(x_40);
x_42 = lean_st_ref_take(x_7, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 3);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_24);
x_49 = lean_st_ref_set(x_7, x_43, x_45);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(x_35);
x_53 = lean_box(x_41);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_49, 0, x_54);
x_9 = x_49;
goto block_17;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_box(x_35);
x_57 = lean_box(x_41);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_9 = x_59;
goto block_17;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
lean_dec(x_44);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_24);
lean_ctor_set(x_43, 3, x_61);
x_62 = lean_st_ref_set(x_7, x_43, x_45);
lean_dec(x_7);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(x_35);
x_66 = lean_box(x_41);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
x_9 = x_68;
goto block_17;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_43, 0);
x_70 = lean_ctor_get(x_43, 1);
x_71 = lean_ctor_get(x_43, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_43);
x_72 = lean_ctor_get(x_44, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_73 = x_44;
} else {
 lean_dec_ref(x_44);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 1, 1);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_24);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_st_ref_set(x_7, x_75, x_45);
lean_dec(x_7);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(x_35);
x_80 = lean_box(x_41);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
x_9 = x_82;
goto block_17;
}
}
}
else
{
lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; uint8_t x_192; lean_object* x_193; 
x_160 = lean_ctor_get(x_27, 0);
lean_inc(x_160);
lean_dec(x_27);
x_161 = 0;
x_162 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_161);
lean_ctor_set(x_26, 3, x_162);
x_163 = lean_st_ref_set(x_7, x_26, x_28);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_192 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_193 = l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2(x_1, x_2, x_192, x_4, x_5, x_6, x_7, x_164);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_224 = lean_st_ref_get(x_7, x_195);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 3);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get_uint8(x_226, sizeof(void*)*1);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
lean_dec(x_224);
x_196 = x_161;
x_197 = x_228;
goto block_223;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_dec(x_224);
x_230 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_231 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_230, x_4, x_5, x_6, x_7, x_229);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_unbox(x_232);
lean_dec(x_232);
x_196 = x_234;
x_197 = x_233;
goto block_223;
}
block_223:
{
if (x_196 == 0)
{
uint8_t x_198; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_unbox(x_194);
lean_dec(x_194);
x_165 = x_198;
x_166 = x_197;
goto block_191;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_199 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_199, 0, x_1);
x_200 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_204, 0, x_2);
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_unbox(x_194);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_209 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_200);
x_212 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_213 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_212, x_211, x_4, x_5, x_6, x_7, x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_unbox(x_194);
lean_dec(x_194);
x_165 = x_215;
x_166 = x_214;
goto block_191;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_216 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_217 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_200);
x_219 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_220 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_219, x_218, x_4, x_5, x_6, x_7, x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_unbox(x_194);
lean_dec(x_194);
x_165 = x_222;
x_166 = x_221;
goto block_191;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_ctor_get(x_193, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_193, 1);
lean_inc(x_236);
lean_dec(x_193);
x_237 = lean_st_ref_get(x_7, x_236);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_st_ref_take(x_7, x_238);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_240, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
x_243 = lean_ctor_get(x_240, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 2);
lean_inc(x_245);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 lean_ctor_release(x_240, 3);
 x_246 = x_240;
} else {
 lean_dec_ref(x_240);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_241, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_248 = x_241;
} else {
 lean_dec_ref(x_241);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(0, 1, 1);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*1, x_24);
if (lean_is_scalar(x_246)) {
 x_250 = lean_alloc_ctor(0, 4, 0);
} else {
 x_250 = x_246;
}
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_244);
lean_ctor_set(x_250, 2, x_245);
lean_ctor_set(x_250, 3, x_249);
x_251 = lean_st_ref_set(x_7, x_250, x_242);
lean_dec(x_7);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
 lean_ctor_set_tag(x_254, 1);
}
lean_ctor_set(x_254, 0, x_235);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
block_191:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_167 = lean_st_ref_get(x_7, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 3);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get_uint8(x_170, sizeof(void*)*1);
lean_dec(x_170);
x_172 = lean_st_ref_take(x_7, x_169);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 2);
lean_inc(x_178);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 lean_ctor_release(x_173, 3);
 x_179 = x_173;
} else {
 lean_dec_ref(x_173);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 1, 1);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_24);
if (lean_is_scalar(x_179)) {
 x_183 = lean_alloc_ctor(0, 4, 0);
} else {
 x_183 = x_179;
}
lean_ctor_set(x_183, 0, x_176);
lean_ctor_set(x_183, 1, x_177);
lean_ctor_set(x_183, 2, x_178);
lean_ctor_set(x_183, 3, x_182);
x_184 = lean_st_ref_set(x_7, x_183, x_175);
lean_dec(x_7);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
x_187 = lean_box(x_165);
x_188 = lean_box(x_171);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
if (lean_is_scalar(x_186)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_186;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_185);
x_9 = x_190;
goto block_17;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; uint8_t x_292; lean_object* x_293; 
x_255 = lean_ctor_get(x_26, 0);
x_256 = lean_ctor_get(x_26, 1);
x_257 = lean_ctor_get(x_26, 2);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_26);
x_258 = lean_ctor_get(x_27, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_259 = x_27;
} else {
 lean_dec_ref(x_27);
 x_259 = lean_box(0);
}
x_260 = 0;
if (lean_is_scalar(x_259)) {
 x_261 = lean_alloc_ctor(0, 1, 1);
} else {
 x_261 = x_259;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set_uint8(x_261, sizeof(void*)*1, x_260);
x_262 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_262, 0, x_255);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set(x_262, 2, x_257);
lean_ctor_set(x_262, 3, x_261);
x_263 = lean_st_ref_set(x_7, x_262, x_28);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_292 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_293 = l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2(x_1, x_2, x_292, x_4, x_5, x_6, x_7, x_264);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_324 = lean_st_ref_get(x_7, x_295);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 3);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_ctor_get_uint8(x_326, sizeof(void*)*1);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; 
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec(x_324);
x_296 = x_260;
x_297 = x_328;
goto block_323;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_324, 1);
lean_inc(x_329);
lean_dec(x_324);
x_330 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_331 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_330, x_4, x_5, x_6, x_7, x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_unbox(x_332);
lean_dec(x_332);
x_296 = x_334;
x_297 = x_333;
goto block_323;
}
block_323:
{
if (x_296 == 0)
{
uint8_t x_298; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_298 = lean_unbox(x_294);
lean_dec(x_294);
x_265 = x_298;
x_266 = x_297;
goto block_291;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_299 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_299, 0, x_1);
x_300 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_301 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_299);
x_302 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_303 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_304, 0, x_2);
x_305 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_307 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_unbox(x_294);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_309 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_300);
x_312 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_313 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_312, x_311, x_4, x_5, x_6, x_7, x_297);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_unbox(x_294);
lean_dec(x_294);
x_265 = x_315;
x_266 = x_314;
goto block_291;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_316 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_317 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_317, 0, x_307);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_300);
x_319 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_320 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_319, x_318, x_4, x_5, x_6, x_7, x_297);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_unbox(x_294);
lean_dec(x_294);
x_265 = x_322;
x_266 = x_321;
goto block_291;
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_335 = lean_ctor_get(x_293, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_293, 1);
lean_inc(x_336);
lean_dec(x_293);
x_337 = lean_st_ref_get(x_7, x_336);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
x_339 = lean_st_ref_take(x_7, x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_340, 3);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec(x_339);
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_340, 2);
lean_inc(x_345);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_346 = x_340;
} else {
 lean_dec_ref(x_340);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_341, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_348 = x_341;
} else {
 lean_dec_ref(x_341);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 1, 1);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*1, x_24);
if (lean_is_scalar(x_346)) {
 x_350 = lean_alloc_ctor(0, 4, 0);
} else {
 x_350 = x_346;
}
lean_ctor_set(x_350, 0, x_343);
lean_ctor_set(x_350, 1, x_344);
lean_ctor_set(x_350, 2, x_345);
lean_ctor_set(x_350, 3, x_349);
x_351 = lean_st_ref_set(x_7, x_350, x_342);
lean_dec(x_7);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_353 = x_351;
} else {
 lean_dec_ref(x_351);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
 lean_ctor_set_tag(x_354, 1);
}
lean_ctor_set(x_354, 0, x_335);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
block_291:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_267 = lean_st_ref_get(x_7, x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_ctor_get(x_268, 3);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get_uint8(x_270, sizeof(void*)*1);
lean_dec(x_270);
x_272 = lean_st_ref_take(x_7, x_269);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_273, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
lean_dec(x_272);
x_276 = lean_ctor_get(x_273, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_273, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_273, 2);
lean_inc(x_278);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 lean_ctor_release(x_273, 3);
 x_279 = x_273;
} else {
 lean_dec_ref(x_273);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_274, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 x_281 = x_274;
} else {
 lean_dec_ref(x_274);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 1, 1);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set_uint8(x_282, sizeof(void*)*1, x_24);
if (lean_is_scalar(x_279)) {
 x_283 = lean_alloc_ctor(0, 4, 0);
} else {
 x_283 = x_279;
}
lean_ctor_set(x_283, 0, x_276);
lean_ctor_set(x_283, 1, x_277);
lean_ctor_set(x_283, 2, x_278);
lean_ctor_set(x_283, 3, x_282);
x_284 = lean_st_ref_set(x_7, x_283, x_275);
lean_dec(x_7);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
x_287 = lean_box(x_265);
x_288 = lean_box(x_271);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
if (lean_is_scalar(x_286)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_286;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_285);
x_9 = x_290;
goto block_17;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_370; lean_object* x_371; 
x_355 = lean_ctor_get(x_6, 3);
lean_inc(x_355);
x_356 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__1___rarg(x_7, x_19);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_370 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_371 = l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__3(x_1, x_2, x_370, x_4, x_5, x_6, x_7, x_358);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec(x_371);
x_402 = lean_st_ref_get(x_7, x_373);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_403, 3);
lean_inc(x_404);
lean_dec(x_403);
x_405 = lean_ctor_get_uint8(x_404, sizeof(void*)*1);
lean_dec(x_404);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_ctor_get(x_402, 1);
lean_inc(x_406);
lean_dec(x_402);
x_407 = 0;
x_374 = x_407;
x_375 = x_406;
goto block_401;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_408 = lean_ctor_get(x_402, 1);
lean_inc(x_408);
lean_dec(x_402);
x_409 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_410 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_409, x_4, x_5, x_6, x_7, x_408);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_unbox(x_411);
lean_dec(x_411);
x_374 = x_413;
x_375 = x_412;
goto block_401;
}
block_401:
{
if (x_374 == 0)
{
uint8_t x_376; 
lean_dec(x_2);
lean_dec(x_1);
x_376 = lean_unbox(x_372);
lean_dec(x_372);
x_359 = x_376;
x_360 = x_375;
goto block_369;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_377 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_377, 0, x_1);
x_378 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_379 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_381 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_382, 0, x_2);
x_383 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_385 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_unbox(x_372);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_387 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_388 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_378);
x_390 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_391 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_390, x_389, x_4, x_5, x_6, x_7, x_375);
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
lean_dec(x_391);
x_393 = lean_unbox(x_372);
lean_dec(x_372);
x_359 = x_393;
x_360 = x_392;
goto block_369;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_394 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_395 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_395, 0, x_385);
lean_ctor_set(x_395, 1, x_394);
x_396 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_378);
x_397 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_398 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_397, x_396, x_4, x_5, x_6, x_7, x_375);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_unbox(x_372);
lean_dec(x_372);
x_359 = x_400;
x_360 = x_399;
goto block_369;
}
}
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_2);
lean_dec(x_1);
x_414 = lean_ctor_get(x_371, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_371, 1);
lean_inc(x_415);
lean_dec(x_371);
x_416 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_417 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(x_357, x_416, x_355, x_4, x_5, x_6, x_7, x_415);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_417, 0);
lean_dec(x_419);
lean_ctor_set_tag(x_417, 1);
lean_ctor_set(x_417, 0, x_414);
return x_417;
}
else
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_417, 1);
lean_inc(x_420);
lean_dec(x_417);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_414);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
block_369:
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_361 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_362 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(x_357, x_361, x_355, x_4, x_5, x_6, x_7, x_360);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_362, 0);
lean_dec(x_364);
x_365 = lean_box(x_359);
lean_ctor_set(x_362, 0, x_365);
return x_362;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
lean_dec(x_362);
x_367 = lean_box(x_359);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
}
}
}
lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_290; 
x_290 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = l_Lean_Expr_toHeadIndex(x_5);
x_292 = l_Lean_HeadIndex_HeadIndex_beq(x_291, x_3);
lean_dec(x_291);
x_293 = lean_unsigned_to_nat(0u);
x_294 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_5, x_293);
x_295 = lean_nat_dec_eq(x_294, x_4);
lean_dec(x_294);
if (x_292 == 0)
{
lean_object* x_296; 
x_296 = lean_box(0);
x_13 = x_296;
goto block_289;
}
else
{
if (x_295 == 0)
{
lean_object* x_297; 
x_297 = lean_box(0);
x_13 = x_297;
goto block_289;
}
else
{
lean_object* x_298; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_298 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = !lean_is_exclusive(x_5);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_5, 0);
x_304 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_303);
lean_inc(x_1);
x_305 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_303, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
lean_inc(x_304);
x_308 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_304, x_6, x_7, x_8, x_9, x_10, x_11, x_307);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_expr_update_app(x_5, x_306, x_310);
lean_ctor_set(x_308, 0, x_311);
return x_308;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_308, 0);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_308);
x_314 = lean_expr_update_app(x_5, x_306, x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
else
{
uint8_t x_316; 
lean_dec(x_306);
lean_free_object(x_5);
lean_dec(x_304);
lean_dec(x_303);
x_316 = !lean_is_exclusive(x_308);
if (x_316 == 0)
{
return x_308;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_308, 0);
x_318 = lean_ctor_get(x_308, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_308);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
else
{
uint8_t x_320; 
lean_free_object(x_5);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_305);
if (x_320 == 0)
{
return x_305;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_305, 0);
x_322 = lean_ctor_get(x_305, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_305);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; uint64_t x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_5, 0);
x_325 = lean_ctor_get(x_5, 1);
x_326 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_324);
lean_inc(x_1);
x_327 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_324, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
lean_inc(x_325);
x_330 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_325, x_6, x_7, x_8, x_9, x_10, x_11, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
x_334 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_334, 0, x_324);
lean_ctor_set(x_334, 1, x_325);
lean_ctor_set_uint64(x_334, sizeof(void*)*2, x_326);
x_335 = lean_expr_update_app(x_334, x_328, x_331);
if (lean_is_scalar(x_333)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_333;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_332);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_328);
lean_dec(x_325);
lean_dec(x_324);
x_337 = lean_ctor_get(x_330, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_330, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_339 = x_330;
} else {
 lean_dec_ref(x_330);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_341 = lean_ctor_get(x_327, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
}
case 6:
{
lean_object* x_345; uint8_t x_346; 
x_345 = lean_ctor_get(x_298, 1);
lean_inc(x_345);
lean_dec(x_298);
x_346 = !lean_is_exclusive(x_5);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint64_t x_350; lean_object* x_351; 
x_347 = lean_ctor_get(x_5, 0);
x_348 = lean_ctor_get(x_5, 1);
x_349 = lean_ctor_get(x_5, 2);
x_350 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_348);
lean_inc(x_1);
x_351 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_348, x_6, x_7, x_8, x_9, x_10, x_11, x_345);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_unsigned_to_nat(1u);
x_355 = lean_nat_add(x_6, x_354);
lean_dec(x_6);
lean_inc(x_349);
x_356 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_349, x_355, x_7, x_8, x_9, x_10, x_11, x_353);
if (lean_obj_tag(x_356) == 0)
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_356, 0);
x_359 = (uint8_t)((x_350 << 24) >> 61);
x_360 = lean_expr_update_lambda(x_5, x_359, x_352, x_358);
lean_ctor_set(x_356, 0, x_360);
return x_356;
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; 
x_361 = lean_ctor_get(x_356, 0);
x_362 = lean_ctor_get(x_356, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_356);
x_363 = (uint8_t)((x_350 << 24) >> 61);
x_364 = lean_expr_update_lambda(x_5, x_363, x_352, x_361);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_362);
return x_365;
}
}
else
{
uint8_t x_366; 
lean_dec(x_352);
lean_free_object(x_5);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
x_366 = !lean_is_exclusive(x_356);
if (x_366 == 0)
{
return x_356;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_356, 0);
x_368 = lean_ctor_get(x_356, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_356);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
uint8_t x_370; 
lean_free_object(x_5);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_370 = !lean_is_exclusive(x_351);
if (x_370 == 0)
{
return x_351;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_351, 0);
x_372 = lean_ctor_get(x_351, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_351);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint64_t x_377; lean_object* x_378; 
x_374 = lean_ctor_get(x_5, 0);
x_375 = lean_ctor_get(x_5, 1);
x_376 = lean_ctor_get(x_5, 2);
x_377 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_376);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_375);
lean_inc(x_1);
x_378 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_375, x_6, x_7, x_8, x_9, x_10, x_11, x_345);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_6, x_381);
lean_dec(x_6);
lean_inc(x_376);
x_383 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_376, x_382, x_7, x_8, x_9, x_10, x_11, x_380);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_386 = x_383;
} else {
 lean_dec_ref(x_383);
 x_386 = lean_box(0);
}
x_387 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_387, 0, x_374);
lean_ctor_set(x_387, 1, x_375);
lean_ctor_set(x_387, 2, x_376);
lean_ctor_set_uint64(x_387, sizeof(void*)*3, x_377);
x_388 = (uint8_t)((x_377 << 24) >> 61);
x_389 = lean_expr_update_lambda(x_387, x_388, x_379, x_384);
if (lean_is_scalar(x_386)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_386;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_385);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_379);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
x_391 = lean_ctor_get(x_383, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_383, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_393 = x_383;
} else {
 lean_dec_ref(x_383);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_395 = lean_ctor_get(x_378, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_378, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_397 = x_378;
} else {
 lean_dec_ref(x_378);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
}
case 7:
{
lean_object* x_399; uint8_t x_400; 
x_399 = lean_ctor_get(x_298, 1);
lean_inc(x_399);
lean_dec(x_298);
x_400 = !lean_is_exclusive(x_5);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint64_t x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_5, 0);
x_402 = lean_ctor_get(x_5, 1);
x_403 = lean_ctor_get(x_5, 2);
x_404 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_402);
lean_inc(x_1);
x_405 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_402, x_6, x_7, x_8, x_9, x_10, x_11, x_399);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_unsigned_to_nat(1u);
x_409 = lean_nat_add(x_6, x_408);
lean_dec(x_6);
lean_inc(x_403);
x_410 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_403, x_409, x_7, x_8, x_9, x_10, x_11, x_407);
if (lean_obj_tag(x_410) == 0)
{
uint8_t x_411; 
x_411 = !lean_is_exclusive(x_410);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_410, 0);
x_413 = (uint8_t)((x_404 << 24) >> 61);
x_414 = lean_expr_update_forall(x_5, x_413, x_406, x_412);
lean_ctor_set(x_410, 0, x_414);
return x_410;
}
else
{
lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_410, 0);
x_416 = lean_ctor_get(x_410, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_410);
x_417 = (uint8_t)((x_404 << 24) >> 61);
x_418 = lean_expr_update_forall(x_5, x_417, x_406, x_415);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_416);
return x_419;
}
}
else
{
uint8_t x_420; 
lean_dec(x_406);
lean_free_object(x_5);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
x_420 = !lean_is_exclusive(x_410);
if (x_420 == 0)
{
return x_410;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_410, 0);
x_422 = lean_ctor_get(x_410, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_410);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
else
{
uint8_t x_424; 
lean_free_object(x_5);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_424 = !lean_is_exclusive(x_405);
if (x_424 == 0)
{
return x_405;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_405, 0);
x_426 = lean_ctor_get(x_405, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_405);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; uint64_t x_431; lean_object* x_432; 
x_428 = lean_ctor_get(x_5, 0);
x_429 = lean_ctor_get(x_5, 1);
x_430 = lean_ctor_get(x_5, 2);
x_431 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_429);
lean_inc(x_1);
x_432 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_429, x_6, x_7, x_8, x_9, x_10, x_11, x_399);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_unsigned_to_nat(1u);
x_436 = lean_nat_add(x_6, x_435);
lean_dec(x_6);
lean_inc(x_430);
x_437 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_430, x_436, x_7, x_8, x_9, x_10, x_11, x_434);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_440 = x_437;
} else {
 lean_dec_ref(x_437);
 x_440 = lean_box(0);
}
x_441 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_441, 0, x_428);
lean_ctor_set(x_441, 1, x_429);
lean_ctor_set(x_441, 2, x_430);
lean_ctor_set_uint64(x_441, sizeof(void*)*3, x_431);
x_442 = (uint8_t)((x_431 << 24) >> 61);
x_443 = lean_expr_update_forall(x_441, x_442, x_433, x_438);
if (lean_is_scalar(x_440)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_440;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_439);
return x_444;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_433);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
x_445 = lean_ctor_get(x_437, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_437, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_447 = x_437;
} else {
 lean_dec_ref(x_437);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_449 = lean_ctor_get(x_432, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_432, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_451 = x_432;
} else {
 lean_dec_ref(x_432);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_450);
return x_452;
}
}
}
case 8:
{
lean_object* x_453; uint8_t x_454; 
x_453 = lean_ctor_get(x_298, 1);
lean_inc(x_453);
lean_dec(x_298);
x_454 = !lean_is_exclusive(x_5);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_455 = lean_ctor_get(x_5, 0);
x_456 = lean_ctor_get(x_5, 1);
x_457 = lean_ctor_get(x_5, 2);
x_458 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_456);
lean_inc(x_1);
x_459 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_456, x_6, x_7, x_8, x_9, x_10, x_11, x_453);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_457);
lean_inc(x_1);
x_462 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_457, x_6, x_7, x_8, x_9, x_10, x_11, x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_unsigned_to_nat(1u);
x_466 = lean_nat_add(x_6, x_465);
lean_dec(x_6);
lean_inc(x_458);
x_467 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_458, x_466, x_7, x_8, x_9, x_10, x_11, x_464);
if (lean_obj_tag(x_467) == 0)
{
uint8_t x_468; 
x_468 = !lean_is_exclusive(x_467);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_467, 0);
x_470 = lean_expr_update_let(x_5, x_460, x_463, x_469);
lean_ctor_set(x_467, 0, x_470);
return x_467;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_467, 0);
x_472 = lean_ctor_get(x_467, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_467);
x_473 = lean_expr_update_let(x_5, x_460, x_463, x_471);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
else
{
uint8_t x_475; 
lean_dec(x_463);
lean_dec(x_460);
lean_free_object(x_5);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
x_475 = !lean_is_exclusive(x_467);
if (x_475 == 0)
{
return x_467;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_467, 0);
x_477 = lean_ctor_get(x_467, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_467);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
else
{
uint8_t x_479; 
lean_dec(x_460);
lean_free_object(x_5);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_479 = !lean_is_exclusive(x_462);
if (x_479 == 0)
{
return x_462;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_462, 0);
x_481 = lean_ctor_get(x_462, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_462);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
uint8_t x_483; 
lean_free_object(x_5);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_483 = !lean_is_exclusive(x_459);
if (x_483 == 0)
{
return x_459;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_459, 0);
x_485 = lean_ctor_get(x_459, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_459);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint64_t x_491; lean_object* x_492; 
x_487 = lean_ctor_get(x_5, 0);
x_488 = lean_ctor_get(x_5, 1);
x_489 = lean_ctor_get(x_5, 2);
x_490 = lean_ctor_get(x_5, 3);
x_491 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_488);
lean_inc(x_1);
x_492 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_488, x_6, x_7, x_8, x_9, x_10, x_11, x_453);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_489);
lean_inc(x_1);
x_495 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_489, x_6, x_7, x_8, x_9, x_10, x_11, x_494);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_unsigned_to_nat(1u);
x_499 = lean_nat_add(x_6, x_498);
lean_dec(x_6);
lean_inc(x_490);
x_500 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_490, x_499, x_7, x_8, x_9, x_10, x_11, x_497);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_503 = x_500;
} else {
 lean_dec_ref(x_500);
 x_503 = lean_box(0);
}
x_504 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_504, 0, x_487);
lean_ctor_set(x_504, 1, x_488);
lean_ctor_set(x_504, 2, x_489);
lean_ctor_set(x_504, 3, x_490);
lean_ctor_set_uint64(x_504, sizeof(void*)*4, x_491);
x_505 = lean_expr_update_let(x_504, x_493, x_496, x_501);
if (lean_is_scalar(x_503)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_503;
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_502);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_496);
lean_dec(x_493);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
x_507 = lean_ctor_get(x_500, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_500, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_509 = x_500;
} else {
 lean_dec_ref(x_500);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_493);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_511 = lean_ctor_get(x_495, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_495, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_513 = x_495;
} else {
 lean_dec_ref(x_495);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_515 = lean_ctor_get(x_492, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_492, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_517 = x_492;
} else {
 lean_dec_ref(x_492);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
}
case 10:
{
lean_object* x_519; uint8_t x_520; 
x_519 = lean_ctor_get(x_298, 1);
lean_inc(x_519);
lean_dec(x_298);
x_520 = !lean_is_exclusive(x_5);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_5, 0);
x_522 = lean_ctor_get(x_5, 1);
lean_inc(x_522);
x_523 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_522, x_6, x_7, x_8, x_9, x_10, x_11, x_519);
if (lean_obj_tag(x_523) == 0)
{
uint8_t x_524; 
x_524 = !lean_is_exclusive(x_523);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_523, 0);
x_526 = lean_expr_update_mdata(x_5, x_525);
lean_ctor_set(x_523, 0, x_526);
return x_523;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_527 = lean_ctor_get(x_523, 0);
x_528 = lean_ctor_get(x_523, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_523);
x_529 = lean_expr_update_mdata(x_5, x_527);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
else
{
uint8_t x_531; 
lean_free_object(x_5);
lean_dec(x_522);
lean_dec(x_521);
x_531 = !lean_is_exclusive(x_523);
if (x_531 == 0)
{
return x_523;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_523, 0);
x_533 = lean_ctor_get(x_523, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_523);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
else
{
lean_object* x_535; lean_object* x_536; uint64_t x_537; lean_object* x_538; 
x_535 = lean_ctor_get(x_5, 0);
x_536 = lean_ctor_get(x_5, 1);
x_537 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_5);
lean_inc(x_536);
x_538 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_536, x_6, x_7, x_8, x_9, x_10, x_11, x_519);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_541 = x_538;
} else {
 lean_dec_ref(x_538);
 x_541 = lean_box(0);
}
x_542 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_542, 0, x_535);
lean_ctor_set(x_542, 1, x_536);
lean_ctor_set_uint64(x_542, sizeof(void*)*2, x_537);
x_543 = lean_expr_update_mdata(x_542, x_539);
if (lean_is_scalar(x_541)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_541;
}
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_540);
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_536);
lean_dec(x_535);
x_545 = lean_ctor_get(x_538, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_538, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_547 = x_538;
} else {
 lean_dec_ref(x_538);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_545);
lean_ctor_set(x_548, 1, x_546);
return x_548;
}
}
}
case 11:
{
lean_object* x_549; uint8_t x_550; 
x_549 = lean_ctor_get(x_298, 1);
lean_inc(x_549);
lean_dec(x_298);
x_550 = !lean_is_exclusive(x_5);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_551 = lean_ctor_get(x_5, 0);
x_552 = lean_ctor_get(x_5, 1);
x_553 = lean_ctor_get(x_5, 2);
lean_inc(x_553);
x_554 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_553, x_6, x_7, x_8, x_9, x_10, x_11, x_549);
if (lean_obj_tag(x_554) == 0)
{
uint8_t x_555; 
x_555 = !lean_is_exclusive(x_554);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; 
x_556 = lean_ctor_get(x_554, 0);
x_557 = lean_expr_update_proj(x_5, x_556);
lean_ctor_set(x_554, 0, x_557);
return x_554;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_558 = lean_ctor_get(x_554, 0);
x_559 = lean_ctor_get(x_554, 1);
lean_inc(x_559);
lean_inc(x_558);
lean_dec(x_554);
x_560 = lean_expr_update_proj(x_5, x_558);
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
else
{
uint8_t x_562; 
lean_free_object(x_5);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_551);
x_562 = !lean_is_exclusive(x_554);
if (x_562 == 0)
{
return x_554;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_554, 0);
x_564 = lean_ctor_get(x_554, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_554);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; uint64_t x_569; lean_object* x_570; 
x_566 = lean_ctor_get(x_5, 0);
x_567 = lean_ctor_get(x_5, 1);
x_568 = lean_ctor_get(x_5, 2);
x_569 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_568);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_5);
lean_inc(x_568);
x_570 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_568, x_6, x_7, x_8, x_9, x_10, x_11, x_549);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_573 = x_570;
} else {
 lean_dec_ref(x_570);
 x_573 = lean_box(0);
}
x_574 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_574, 0, x_566);
lean_ctor_set(x_574, 1, x_567);
lean_ctor_set(x_574, 2, x_568);
lean_ctor_set_uint64(x_574, sizeof(void*)*3, x_569);
x_575 = lean_expr_update_proj(x_574, x_571);
if (lean_is_scalar(x_573)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_573;
}
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_572);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_566);
x_577 = lean_ctor_get(x_570, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_570, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_579 = x_570;
} else {
 lean_dec_ref(x_570);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
}
}
default: 
{
uint8_t x_581; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_581 = !lean_is_exclusive(x_298);
if (x_581 == 0)
{
lean_object* x_582; 
x_582 = lean_ctor_get(x_298, 0);
lean_dec(x_582);
lean_ctor_set(x_298, 0, x_5);
return x_298;
}
else
{
lean_object* x_583; lean_object* x_584; 
x_583 = lean_ctor_get(x_298, 1);
lean_inc(x_583);
lean_dec(x_298);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_5);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; 
x_585 = lean_ctor_get(x_298, 1);
lean_inc(x_585);
lean_dec(x_298);
x_586 = lean_st_ref_get(x_7, x_585);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_unsigned_to_nat(1u);
x_590 = lean_nat_add(x_587, x_589);
x_591 = lean_st_ref_set(x_7, x_590, x_588);
x_592 = !lean_is_exclusive(x_591);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; 
x_593 = lean_ctor_get(x_591, 1);
x_594 = lean_ctor_get(x_591, 0);
lean_dec(x_594);
x_595 = l_Lean_Occurrences_contains(x_2, x_587);
lean_dec(x_587);
if (x_595 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_596; 
lean_free_object(x_591);
x_596 = !lean_is_exclusive(x_5);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_5, 0);
x_598 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_597);
lean_inc(x_1);
x_599 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_597, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
lean_inc(x_598);
x_602 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_598, x_6, x_7, x_8, x_9, x_10, x_11, x_601);
if (lean_obj_tag(x_602) == 0)
{
uint8_t x_603; 
x_603 = !lean_is_exclusive(x_602);
if (x_603 == 0)
{
lean_object* x_604; lean_object* x_605; 
x_604 = lean_ctor_get(x_602, 0);
x_605 = lean_expr_update_app(x_5, x_600, x_604);
lean_ctor_set(x_602, 0, x_605);
return x_602;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_606 = lean_ctor_get(x_602, 0);
x_607 = lean_ctor_get(x_602, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_602);
x_608 = lean_expr_update_app(x_5, x_600, x_606);
x_609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
else
{
uint8_t x_610; 
lean_dec(x_600);
lean_free_object(x_5);
lean_dec(x_598);
lean_dec(x_597);
x_610 = !lean_is_exclusive(x_602);
if (x_610 == 0)
{
return x_602;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_602, 0);
x_612 = lean_ctor_get(x_602, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_602);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
}
}
else
{
uint8_t x_614; 
lean_free_object(x_5);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_614 = !lean_is_exclusive(x_599);
if (x_614 == 0)
{
return x_599;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_599, 0);
x_616 = lean_ctor_get(x_599, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_599);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
return x_617;
}
}
}
else
{
lean_object* x_618; lean_object* x_619; uint64_t x_620; lean_object* x_621; 
x_618 = lean_ctor_get(x_5, 0);
x_619 = lean_ctor_get(x_5, 1);
x_620 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_618);
lean_inc(x_1);
x_621 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_618, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
lean_inc(x_619);
x_624 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_619, x_6, x_7, x_8, x_9, x_10, x_11, x_623);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_627 = x_624;
} else {
 lean_dec_ref(x_624);
 x_627 = lean_box(0);
}
x_628 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_628, 0, x_618);
lean_ctor_set(x_628, 1, x_619);
lean_ctor_set_uint64(x_628, sizeof(void*)*2, x_620);
x_629 = lean_expr_update_app(x_628, x_622, x_625);
if (lean_is_scalar(x_627)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_627;
}
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_626);
return x_630;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_622);
lean_dec(x_619);
lean_dec(x_618);
x_631 = lean_ctor_get(x_624, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_624, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_633 = x_624;
} else {
 lean_dec_ref(x_624);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_631);
lean_ctor_set(x_634, 1, x_632);
return x_634;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_635 = lean_ctor_get(x_621, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_621, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_637 = x_621;
} else {
 lean_dec_ref(x_621);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
}
case 6:
{
uint8_t x_639; 
lean_free_object(x_591);
x_639 = !lean_is_exclusive(x_5);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; uint64_t x_643; lean_object* x_644; 
x_640 = lean_ctor_get(x_5, 0);
x_641 = lean_ctor_get(x_5, 1);
x_642 = lean_ctor_get(x_5, 2);
x_643 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_641);
lean_inc(x_1);
x_644 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_641, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec(x_644);
x_647 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_642);
x_648 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_642, x_647, x_7, x_8, x_9, x_10, x_11, x_646);
if (lean_obj_tag(x_648) == 0)
{
uint8_t x_649; 
x_649 = !lean_is_exclusive(x_648);
if (x_649 == 0)
{
lean_object* x_650; uint8_t x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_648, 0);
x_651 = (uint8_t)((x_643 << 24) >> 61);
x_652 = lean_expr_update_lambda(x_5, x_651, x_645, x_650);
lean_ctor_set(x_648, 0, x_652);
return x_648;
}
else
{
lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; 
x_653 = lean_ctor_get(x_648, 0);
x_654 = lean_ctor_get(x_648, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_648);
x_655 = (uint8_t)((x_643 << 24) >> 61);
x_656 = lean_expr_update_lambda(x_5, x_655, x_645, x_653);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_654);
return x_657;
}
}
else
{
uint8_t x_658; 
lean_dec(x_645);
lean_free_object(x_5);
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
x_658 = !lean_is_exclusive(x_648);
if (x_658 == 0)
{
return x_648;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_648, 0);
x_660 = lean_ctor_get(x_648, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_648);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
else
{
uint8_t x_662; 
lean_free_object(x_5);
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_640);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_662 = !lean_is_exclusive(x_644);
if (x_662 == 0)
{
return x_644;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_644, 0);
x_664 = lean_ctor_get(x_644, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_644);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; uint64_t x_669; lean_object* x_670; 
x_666 = lean_ctor_get(x_5, 0);
x_667 = lean_ctor_get(x_5, 1);
x_668 = lean_ctor_get(x_5, 2);
x_669 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_668);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_667);
lean_inc(x_1);
x_670 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_667, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
lean_dec(x_670);
x_673 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_668);
x_674 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_668, x_673, x_7, x_8, x_9, x_10, x_11, x_672);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; lean_object* x_680; lean_object* x_681; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_677 = x_674;
} else {
 lean_dec_ref(x_674);
 x_677 = lean_box(0);
}
x_678 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_678, 0, x_666);
lean_ctor_set(x_678, 1, x_667);
lean_ctor_set(x_678, 2, x_668);
lean_ctor_set_uint64(x_678, sizeof(void*)*3, x_669);
x_679 = (uint8_t)((x_669 << 24) >> 61);
x_680 = lean_expr_update_lambda(x_678, x_679, x_671, x_675);
if (lean_is_scalar(x_677)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_677;
}
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_676);
return x_681;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
lean_dec(x_671);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
x_682 = lean_ctor_get(x_674, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_674, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_684 = x_674;
} else {
 lean_dec_ref(x_674);
 x_684 = lean_box(0);
}
if (lean_is_scalar(x_684)) {
 x_685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_685 = x_684;
}
lean_ctor_set(x_685, 0, x_682);
lean_ctor_set(x_685, 1, x_683);
return x_685;
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_686 = lean_ctor_get(x_670, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_670, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_688 = x_670;
} else {
 lean_dec_ref(x_670);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_686);
lean_ctor_set(x_689, 1, x_687);
return x_689;
}
}
}
case 7:
{
uint8_t x_690; 
lean_free_object(x_591);
x_690 = !lean_is_exclusive(x_5);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; uint64_t x_694; lean_object* x_695; 
x_691 = lean_ctor_get(x_5, 0);
x_692 = lean_ctor_get(x_5, 1);
x_693 = lean_ctor_get(x_5, 2);
x_694 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_692);
lean_inc(x_1);
x_695 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_692, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_693);
x_699 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_693, x_698, x_7, x_8, x_9, x_10, x_11, x_697);
if (lean_obj_tag(x_699) == 0)
{
uint8_t x_700; 
x_700 = !lean_is_exclusive(x_699);
if (x_700 == 0)
{
lean_object* x_701; uint8_t x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_699, 0);
x_702 = (uint8_t)((x_694 << 24) >> 61);
x_703 = lean_expr_update_forall(x_5, x_702, x_696, x_701);
lean_ctor_set(x_699, 0, x_703);
return x_699;
}
else
{
lean_object* x_704; lean_object* x_705; uint8_t x_706; lean_object* x_707; lean_object* x_708; 
x_704 = lean_ctor_get(x_699, 0);
x_705 = lean_ctor_get(x_699, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_699);
x_706 = (uint8_t)((x_694 << 24) >> 61);
x_707 = lean_expr_update_forall(x_5, x_706, x_696, x_704);
x_708 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_705);
return x_708;
}
}
else
{
uint8_t x_709; 
lean_dec(x_696);
lean_free_object(x_5);
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
x_709 = !lean_is_exclusive(x_699);
if (x_709 == 0)
{
return x_699;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_710 = lean_ctor_get(x_699, 0);
x_711 = lean_ctor_get(x_699, 1);
lean_inc(x_711);
lean_inc(x_710);
lean_dec(x_699);
x_712 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_712, 0, x_710);
lean_ctor_set(x_712, 1, x_711);
return x_712;
}
}
}
else
{
uint8_t x_713; 
lean_free_object(x_5);
lean_dec(x_693);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_713 = !lean_is_exclusive(x_695);
if (x_713 == 0)
{
return x_695;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_695, 0);
x_715 = lean_ctor_get(x_695, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_695);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; uint64_t x_720; lean_object* x_721; 
x_717 = lean_ctor_get(x_5, 0);
x_718 = lean_ctor_get(x_5, 1);
x_719 = lean_ctor_get(x_5, 2);
x_720 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_719);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_718);
lean_inc(x_1);
x_721 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_718, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_724 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_719);
x_725 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_719, x_724, x_7, x_8, x_9, x_10, x_11, x_723);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_728 = x_725;
} else {
 lean_dec_ref(x_725);
 x_728 = lean_box(0);
}
x_729 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_729, 0, x_717);
lean_ctor_set(x_729, 1, x_718);
lean_ctor_set(x_729, 2, x_719);
lean_ctor_set_uint64(x_729, sizeof(void*)*3, x_720);
x_730 = (uint8_t)((x_720 << 24) >> 61);
x_731 = lean_expr_update_forall(x_729, x_730, x_722, x_726);
if (lean_is_scalar(x_728)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_728;
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_727);
return x_732;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_722);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_717);
x_733 = lean_ctor_get(x_725, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_725, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_735 = x_725;
} else {
 lean_dec_ref(x_725);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_717);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_737 = lean_ctor_get(x_721, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_721, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_739 = x_721;
} else {
 lean_dec_ref(x_721);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
}
}
case 8:
{
uint8_t x_741; 
lean_free_object(x_591);
x_741 = !lean_is_exclusive(x_5);
if (x_741 == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_742 = lean_ctor_get(x_5, 0);
x_743 = lean_ctor_get(x_5, 1);
x_744 = lean_ctor_get(x_5, 2);
x_745 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_743);
lean_inc(x_1);
x_746 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_743, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec(x_746);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_744);
lean_inc(x_1);
x_749 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_744, x_6, x_7, x_8, x_9, x_10, x_11, x_748);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec(x_749);
x_752 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_745);
x_753 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_745, x_752, x_7, x_8, x_9, x_10, x_11, x_751);
if (lean_obj_tag(x_753) == 0)
{
uint8_t x_754; 
x_754 = !lean_is_exclusive(x_753);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_753, 0);
x_756 = lean_expr_update_let(x_5, x_747, x_750, x_755);
lean_ctor_set(x_753, 0, x_756);
return x_753;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_757 = lean_ctor_get(x_753, 0);
x_758 = lean_ctor_get(x_753, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_753);
x_759 = lean_expr_update_let(x_5, x_747, x_750, x_757);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
}
else
{
uint8_t x_761; 
lean_dec(x_750);
lean_dec(x_747);
lean_free_object(x_5);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
x_761 = !lean_is_exclusive(x_753);
if (x_761 == 0)
{
return x_753;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_762 = lean_ctor_get(x_753, 0);
x_763 = lean_ctor_get(x_753, 1);
lean_inc(x_763);
lean_inc(x_762);
lean_dec(x_753);
x_764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_764, 0, x_762);
lean_ctor_set(x_764, 1, x_763);
return x_764;
}
}
}
else
{
uint8_t x_765; 
lean_dec(x_747);
lean_free_object(x_5);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_765 = !lean_is_exclusive(x_749);
if (x_765 == 0)
{
return x_749;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_749, 0);
x_767 = lean_ctor_get(x_749, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_749);
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
return x_768;
}
}
}
else
{
uint8_t x_769; 
lean_free_object(x_5);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_746);
if (x_769 == 0)
{
return x_746;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_746, 0);
x_771 = lean_ctor_get(x_746, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_746);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint64_t x_777; lean_object* x_778; 
x_773 = lean_ctor_get(x_5, 0);
x_774 = lean_ctor_get(x_5, 1);
x_775 = lean_ctor_get(x_5, 2);
x_776 = lean_ctor_get(x_5, 3);
x_777 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_776);
lean_inc(x_775);
lean_inc(x_774);
lean_inc(x_773);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_774);
lean_inc(x_1);
x_778 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_774, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
lean_dec(x_778);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_775);
lean_inc(x_1);
x_781 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_775, x_6, x_7, x_8, x_9, x_10, x_11, x_780);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
lean_dec(x_781);
x_784 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_776);
x_785 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_776, x_784, x_7, x_8, x_9, x_10, x_11, x_783);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_785, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_788 = x_785;
} else {
 lean_dec_ref(x_785);
 x_788 = lean_box(0);
}
x_789 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_789, 0, x_773);
lean_ctor_set(x_789, 1, x_774);
lean_ctor_set(x_789, 2, x_775);
lean_ctor_set(x_789, 3, x_776);
lean_ctor_set_uint64(x_789, sizeof(void*)*4, x_777);
x_790 = lean_expr_update_let(x_789, x_779, x_782, x_786);
if (lean_is_scalar(x_788)) {
 x_791 = lean_alloc_ctor(0, 2, 0);
} else {
 x_791 = x_788;
}
lean_ctor_set(x_791, 0, x_790);
lean_ctor_set(x_791, 1, x_787);
return x_791;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_782);
lean_dec(x_779);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
x_792 = lean_ctor_get(x_785, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_785, 1);
lean_inc(x_793);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_794 = x_785;
} else {
 lean_dec_ref(x_785);
 x_794 = lean_box(0);
}
if (lean_is_scalar(x_794)) {
 x_795 = lean_alloc_ctor(1, 2, 0);
} else {
 x_795 = x_794;
}
lean_ctor_set(x_795, 0, x_792);
lean_ctor_set(x_795, 1, x_793);
return x_795;
}
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_779);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_796 = lean_ctor_get(x_781, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_781, 1);
lean_inc(x_797);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_798 = x_781;
} else {
 lean_dec_ref(x_781);
 x_798 = lean_box(0);
}
if (lean_is_scalar(x_798)) {
 x_799 = lean_alloc_ctor(1, 2, 0);
} else {
 x_799 = x_798;
}
lean_ctor_set(x_799, 0, x_796);
lean_ctor_set(x_799, 1, x_797);
return x_799;
}
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_800 = lean_ctor_get(x_778, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_778, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_802 = x_778;
} else {
 lean_dec_ref(x_778);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(1, 2, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_800);
lean_ctor_set(x_803, 1, x_801);
return x_803;
}
}
}
case 10:
{
uint8_t x_804; 
lean_free_object(x_591);
x_804 = !lean_is_exclusive(x_5);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_5, 0);
x_806 = lean_ctor_get(x_5, 1);
lean_inc(x_806);
x_807 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_806, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_807) == 0)
{
uint8_t x_808; 
x_808 = !lean_is_exclusive(x_807);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_ctor_get(x_807, 0);
x_810 = lean_expr_update_mdata(x_5, x_809);
lean_ctor_set(x_807, 0, x_810);
return x_807;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_807, 0);
x_812 = lean_ctor_get(x_807, 1);
lean_inc(x_812);
lean_inc(x_811);
lean_dec(x_807);
x_813 = lean_expr_update_mdata(x_5, x_811);
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
else
{
uint8_t x_815; 
lean_free_object(x_5);
lean_dec(x_806);
lean_dec(x_805);
x_815 = !lean_is_exclusive(x_807);
if (x_815 == 0)
{
return x_807;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = lean_ctor_get(x_807, 0);
x_817 = lean_ctor_get(x_807, 1);
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_807);
x_818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set(x_818, 1, x_817);
return x_818;
}
}
}
else
{
lean_object* x_819; lean_object* x_820; uint64_t x_821; lean_object* x_822; 
x_819 = lean_ctor_get(x_5, 0);
x_820 = lean_ctor_get(x_5, 1);
x_821 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_820);
lean_inc(x_819);
lean_dec(x_5);
lean_inc(x_820);
x_822 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_820, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_825 = x_822;
} else {
 lean_dec_ref(x_822);
 x_825 = lean_box(0);
}
x_826 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_826, 0, x_819);
lean_ctor_set(x_826, 1, x_820);
lean_ctor_set_uint64(x_826, sizeof(void*)*2, x_821);
x_827 = lean_expr_update_mdata(x_826, x_823);
if (lean_is_scalar(x_825)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_825;
}
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_824);
return x_828;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_820);
lean_dec(x_819);
x_829 = lean_ctor_get(x_822, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_822, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_831 = x_822;
} else {
 lean_dec_ref(x_822);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_830);
return x_832;
}
}
}
case 11:
{
uint8_t x_833; 
lean_free_object(x_591);
x_833 = !lean_is_exclusive(x_5);
if (x_833 == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_ctor_get(x_5, 0);
x_835 = lean_ctor_get(x_5, 1);
x_836 = lean_ctor_get(x_5, 2);
lean_inc(x_836);
x_837 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_836, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_837) == 0)
{
uint8_t x_838; 
x_838 = !lean_is_exclusive(x_837);
if (x_838 == 0)
{
lean_object* x_839; lean_object* x_840; 
x_839 = lean_ctor_get(x_837, 0);
x_840 = lean_expr_update_proj(x_5, x_839);
lean_ctor_set(x_837, 0, x_840);
return x_837;
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_841 = lean_ctor_get(x_837, 0);
x_842 = lean_ctor_get(x_837, 1);
lean_inc(x_842);
lean_inc(x_841);
lean_dec(x_837);
x_843 = lean_expr_update_proj(x_5, x_841);
x_844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_842);
return x_844;
}
}
else
{
uint8_t x_845; 
lean_free_object(x_5);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_834);
x_845 = !lean_is_exclusive(x_837);
if (x_845 == 0)
{
return x_837;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_837, 0);
x_847 = lean_ctor_get(x_837, 1);
lean_inc(x_847);
lean_inc(x_846);
lean_dec(x_837);
x_848 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_848, 0, x_846);
lean_ctor_set(x_848, 1, x_847);
return x_848;
}
}
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; uint64_t x_852; lean_object* x_853; 
x_849 = lean_ctor_get(x_5, 0);
x_850 = lean_ctor_get(x_5, 1);
x_851 = lean_ctor_get(x_5, 2);
x_852 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_851);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_5);
lean_inc(x_851);
x_853 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_851, x_6, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_856 = x_853;
} else {
 lean_dec_ref(x_853);
 x_856 = lean_box(0);
}
x_857 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_857, 0, x_849);
lean_ctor_set(x_857, 1, x_850);
lean_ctor_set(x_857, 2, x_851);
lean_ctor_set_uint64(x_857, sizeof(void*)*3, x_852);
x_858 = lean_expr_update_proj(x_857, x_854);
if (lean_is_scalar(x_856)) {
 x_859 = lean_alloc_ctor(0, 2, 0);
} else {
 x_859 = x_856;
}
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_855);
return x_859;
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
x_860 = lean_ctor_get(x_853, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_853, 1);
lean_inc(x_861);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_862 = x_853;
} else {
 lean_dec_ref(x_853);
 x_862 = lean_box(0);
}
if (lean_is_scalar(x_862)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_862;
}
lean_ctor_set(x_863, 0, x_860);
lean_ctor_set(x_863, 1, x_861);
return x_863;
}
}
}
default: 
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_591, 0, x_5);
return x_591;
}
}
}
else
{
lean_object* x_864; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_864 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_591, 0, x_864);
return x_591;
}
}
else
{
lean_object* x_865; uint8_t x_866; 
x_865 = lean_ctor_get(x_591, 1);
lean_inc(x_865);
lean_dec(x_591);
x_866 = l_Lean_Occurrences_contains(x_2, x_587);
lean_dec(x_587);
if (x_866 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_867; lean_object* x_868; uint64_t x_869; lean_object* x_870; lean_object* x_871; 
x_867 = lean_ctor_get(x_5, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_5, 1);
lean_inc(x_868);
x_869 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_870 = x_5;
} else {
 lean_dec_ref(x_5);
 x_870 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_867);
lean_inc(x_1);
x_871 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_867, x_6, x_7, x_8, x_9, x_10, x_11, x_865);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
lean_inc(x_868);
x_874 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_868, x_6, x_7, x_8, x_9, x_10, x_11, x_873);
if (lean_obj_tag(x_874) == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_877 = x_874;
} else {
 lean_dec_ref(x_874);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_878 = lean_alloc_ctor(5, 2, 8);
} else {
 x_878 = x_870;
}
lean_ctor_set(x_878, 0, x_867);
lean_ctor_set(x_878, 1, x_868);
lean_ctor_set_uint64(x_878, sizeof(void*)*2, x_869);
x_879 = lean_expr_update_app(x_878, x_872, x_875);
if (lean_is_scalar(x_877)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_877;
}
lean_ctor_set(x_880, 0, x_879);
lean_ctor_set(x_880, 1, x_876);
return x_880;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_872);
lean_dec(x_870);
lean_dec(x_868);
lean_dec(x_867);
x_881 = lean_ctor_get(x_874, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_874, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_883 = x_874;
} else {
 lean_dec_ref(x_874);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_882);
return x_884;
}
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_dec(x_870);
lean_dec(x_868);
lean_dec(x_867);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_885 = lean_ctor_get(x_871, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_871, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_887 = x_871;
} else {
 lean_dec_ref(x_871);
 x_887 = lean_box(0);
}
if (lean_is_scalar(x_887)) {
 x_888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_888 = x_887;
}
lean_ctor_set(x_888, 0, x_885);
lean_ctor_set(x_888, 1, x_886);
return x_888;
}
}
case 6:
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; uint64_t x_892; lean_object* x_893; lean_object* x_894; 
x_889 = lean_ctor_get(x_5, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_5, 1);
lean_inc(x_890);
x_891 = lean_ctor_get(x_5, 2);
lean_inc(x_891);
x_892 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_893 = x_5;
} else {
 lean_dec_ref(x_5);
 x_893 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_890);
lean_inc(x_1);
x_894 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_890, x_6, x_7, x_8, x_9, x_10, x_11, x_865);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
lean_dec(x_894);
x_897 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_891);
x_898 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_891, x_897, x_7, x_8, x_9, x_10, x_11, x_896);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; uint8_t x_903; lean_object* x_904; lean_object* x_905; 
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_901 = x_898;
} else {
 lean_dec_ref(x_898);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_902 = lean_alloc_ctor(6, 3, 8);
} else {
 x_902 = x_893;
}
lean_ctor_set(x_902, 0, x_889);
lean_ctor_set(x_902, 1, x_890);
lean_ctor_set(x_902, 2, x_891);
lean_ctor_set_uint64(x_902, sizeof(void*)*3, x_892);
x_903 = (uint8_t)((x_892 << 24) >> 61);
x_904 = lean_expr_update_lambda(x_902, x_903, x_895, x_899);
if (lean_is_scalar(x_901)) {
 x_905 = lean_alloc_ctor(0, 2, 0);
} else {
 x_905 = x_901;
}
lean_ctor_set(x_905, 0, x_904);
lean_ctor_set(x_905, 1, x_900);
return x_905;
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
lean_dec(x_895);
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
x_906 = lean_ctor_get(x_898, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_898, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_908 = x_898;
} else {
 lean_dec_ref(x_898);
 x_908 = lean_box(0);
}
if (lean_is_scalar(x_908)) {
 x_909 = lean_alloc_ctor(1, 2, 0);
} else {
 x_909 = x_908;
}
lean_ctor_set(x_909, 0, x_906);
lean_ctor_set(x_909, 1, x_907);
return x_909;
}
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_893);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_910 = lean_ctor_get(x_894, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_894, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_912 = x_894;
} else {
 lean_dec_ref(x_894);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_910);
lean_ctor_set(x_913, 1, x_911);
return x_913;
}
}
case 7:
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; uint64_t x_917; lean_object* x_918; lean_object* x_919; 
x_914 = lean_ctor_get(x_5, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_5, 1);
lean_inc(x_915);
x_916 = lean_ctor_get(x_5, 2);
lean_inc(x_916);
x_917 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_918 = x_5;
} else {
 lean_dec_ref(x_5);
 x_918 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_915);
lean_inc(x_1);
x_919 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_915, x_6, x_7, x_8, x_9, x_10, x_11, x_865);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
lean_dec(x_919);
x_922 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_916);
x_923 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_916, x_922, x_7, x_8, x_9, x_10, x_11, x_921);
if (lean_obj_tag(x_923) == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; uint8_t x_928; lean_object* x_929; lean_object* x_930; 
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_923, 1);
lean_inc(x_925);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 lean_ctor_release(x_923, 1);
 x_926 = x_923;
} else {
 lean_dec_ref(x_923);
 x_926 = lean_box(0);
}
if (lean_is_scalar(x_918)) {
 x_927 = lean_alloc_ctor(7, 3, 8);
} else {
 x_927 = x_918;
}
lean_ctor_set(x_927, 0, x_914);
lean_ctor_set(x_927, 1, x_915);
lean_ctor_set(x_927, 2, x_916);
lean_ctor_set_uint64(x_927, sizeof(void*)*3, x_917);
x_928 = (uint8_t)((x_917 << 24) >> 61);
x_929 = lean_expr_update_forall(x_927, x_928, x_920, x_924);
if (lean_is_scalar(x_926)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_926;
}
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_925);
return x_930;
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_920);
lean_dec(x_918);
lean_dec(x_916);
lean_dec(x_915);
lean_dec(x_914);
x_931 = lean_ctor_get(x_923, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_923, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 lean_ctor_release(x_923, 1);
 x_933 = x_923;
} else {
 lean_dec_ref(x_923);
 x_933 = lean_box(0);
}
if (lean_is_scalar(x_933)) {
 x_934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_934 = x_933;
}
lean_ctor_set(x_934, 0, x_931);
lean_ctor_set(x_934, 1, x_932);
return x_934;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_918);
lean_dec(x_916);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_935 = lean_ctor_get(x_919, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_919, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 x_937 = x_919;
} else {
 lean_dec_ref(x_919);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_936);
return x_938;
}
}
case 8:
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint64_t x_943; lean_object* x_944; lean_object* x_945; 
x_939 = lean_ctor_get(x_5, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_5, 1);
lean_inc(x_940);
x_941 = lean_ctor_get(x_5, 2);
lean_inc(x_941);
x_942 = lean_ctor_get(x_5, 3);
lean_inc(x_942);
x_943 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_944 = x_5;
} else {
 lean_dec_ref(x_5);
 x_944 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_940);
lean_inc(x_1);
x_945 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_940, x_6, x_7, x_8, x_9, x_10, x_11, x_865);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_941);
lean_inc(x_1);
x_948 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_941, x_6, x_7, x_8, x_9, x_10, x_11, x_947);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
lean_inc(x_942);
x_952 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_942, x_951, x_7, x_8, x_9, x_10, x_11, x_950);
if (lean_obj_tag(x_952) == 0)
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_955 = x_952;
} else {
 lean_dec_ref(x_952);
 x_955 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_956 = lean_alloc_ctor(8, 4, 8);
} else {
 x_956 = x_944;
}
lean_ctor_set(x_956, 0, x_939);
lean_ctor_set(x_956, 1, x_940);
lean_ctor_set(x_956, 2, x_941);
lean_ctor_set(x_956, 3, x_942);
lean_ctor_set_uint64(x_956, sizeof(void*)*4, x_943);
x_957 = lean_expr_update_let(x_956, x_946, x_949, x_953);
if (lean_is_scalar(x_955)) {
 x_958 = lean_alloc_ctor(0, 2, 0);
} else {
 x_958 = x_955;
}
lean_ctor_set(x_958, 0, x_957);
lean_ctor_set(x_958, 1, x_954);
return x_958;
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_949);
lean_dec(x_946);
lean_dec(x_944);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_939);
x_959 = lean_ctor_get(x_952, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_952, 1);
lean_inc(x_960);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_961 = x_952;
} else {
 lean_dec_ref(x_952);
 x_961 = lean_box(0);
}
if (lean_is_scalar(x_961)) {
 x_962 = lean_alloc_ctor(1, 2, 0);
} else {
 x_962 = x_961;
}
lean_ctor_set(x_962, 0, x_959);
lean_ctor_set(x_962, 1, x_960);
return x_962;
}
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_946);
lean_dec(x_944);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_963 = lean_ctor_get(x_948, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_948, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_965 = x_948;
} else {
 lean_dec_ref(x_948);
 x_965 = lean_box(0);
}
if (lean_is_scalar(x_965)) {
 x_966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_966 = x_965;
}
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_964);
return x_966;
}
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_944);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_967 = lean_ctor_get(x_945, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_945, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_969 = x_945;
} else {
 lean_dec_ref(x_945);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_967);
lean_ctor_set(x_970, 1, x_968);
return x_970;
}
}
case 10:
{
lean_object* x_971; lean_object* x_972; uint64_t x_973; lean_object* x_974; lean_object* x_975; 
x_971 = lean_ctor_get(x_5, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_5, 1);
lean_inc(x_972);
x_973 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_974 = x_5;
} else {
 lean_dec_ref(x_5);
 x_974 = lean_box(0);
}
lean_inc(x_972);
x_975 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_972, x_6, x_7, x_8, x_9, x_10, x_11, x_865);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_978 = x_975;
} else {
 lean_dec_ref(x_975);
 x_978 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_979 = lean_alloc_ctor(10, 2, 8);
} else {
 x_979 = x_974;
}
lean_ctor_set(x_979, 0, x_971);
lean_ctor_set(x_979, 1, x_972);
lean_ctor_set_uint64(x_979, sizeof(void*)*2, x_973);
x_980 = lean_expr_update_mdata(x_979, x_976);
if (lean_is_scalar(x_978)) {
 x_981 = lean_alloc_ctor(0, 2, 0);
} else {
 x_981 = x_978;
}
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_977);
return x_981;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
lean_dec(x_974);
lean_dec(x_972);
lean_dec(x_971);
x_982 = lean_ctor_get(x_975, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_975, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_984 = x_975;
} else {
 lean_dec_ref(x_975);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_983);
return x_985;
}
}
case 11:
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; uint64_t x_989; lean_object* x_990; lean_object* x_991; 
x_986 = lean_ctor_get(x_5, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_5, 1);
lean_inc(x_987);
x_988 = lean_ctor_get(x_5, 2);
lean_inc(x_988);
x_989 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_990 = x_5;
} else {
 lean_dec_ref(x_5);
 x_990 = lean_box(0);
}
lean_inc(x_988);
x_991 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_988, x_6, x_7, x_8, x_9, x_10, x_11, x_865);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_994 = x_991;
} else {
 lean_dec_ref(x_991);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_995 = lean_alloc_ctor(11, 3, 8);
} else {
 x_995 = x_990;
}
lean_ctor_set(x_995, 0, x_986);
lean_ctor_set(x_995, 1, x_987);
lean_ctor_set(x_995, 2, x_988);
lean_ctor_set_uint64(x_995, sizeof(void*)*3, x_989);
x_996 = lean_expr_update_proj(x_995, x_992);
if (lean_is_scalar(x_994)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_994;
}
lean_ctor_set(x_997, 0, x_996);
lean_ctor_set(x_997, 1, x_993);
return x_997;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_990);
lean_dec(x_988);
lean_dec(x_987);
lean_dec(x_986);
x_998 = lean_ctor_get(x_991, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_991, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1000 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1000 = lean_box(0);
}
if (lean_is_scalar(x_1000)) {
 x_1001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1001 = x_1000;
}
lean_ctor_set(x_1001, 0, x_998);
lean_ctor_set(x_1001, 1, x_999);
return x_1001;
}
}
default: 
{
lean_object* x_1002; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_5);
lean_ctor_set(x_1002, 1, x_865);
return x_1002;
}
}
}
else
{
lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_1003 = l_Lean_mkBVar(x_6);
x_1004 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_865);
return x_1004;
}
}
}
}
else
{
uint8_t x_1005; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1005 = !lean_is_exclusive(x_298);
if (x_1005 == 0)
{
return x_298;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_298, 0);
x_1007 = lean_ctor_get(x_298, 1);
lean_inc(x_1007);
lean_inc(x_1006);
lean_dec(x_298);
x_1008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1008, 0, x_1006);
lean_ctor_set(x_1008, 1, x_1007);
return x_1008;
}
}
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_1009; 
x_1009 = !lean_is_exclusive(x_5);
if (x_1009 == 0)
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_5, 0);
x_1011 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1010);
lean_inc(x_1);
x_1012 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1010, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
lean_dec(x_1012);
lean_inc(x_1011);
x_1015 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1011, x_6, x_7, x_8, x_9, x_10, x_11, x_1014);
if (lean_obj_tag(x_1015) == 0)
{
uint8_t x_1016; 
x_1016 = !lean_is_exclusive(x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; lean_object* x_1018; 
x_1017 = lean_ctor_get(x_1015, 0);
x_1018 = lean_expr_update_app(x_5, x_1013, x_1017);
lean_ctor_set(x_1015, 0, x_1018);
return x_1015;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1019 = lean_ctor_get(x_1015, 0);
x_1020 = lean_ctor_get(x_1015, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_1015);
x_1021 = lean_expr_update_app(x_5, x_1013, x_1019);
x_1022 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_1020);
return x_1022;
}
}
else
{
uint8_t x_1023; 
lean_dec(x_1013);
lean_free_object(x_5);
lean_dec(x_1011);
lean_dec(x_1010);
x_1023 = !lean_is_exclusive(x_1015);
if (x_1023 == 0)
{
return x_1015;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1024 = lean_ctor_get(x_1015, 0);
x_1025 = lean_ctor_get(x_1015, 1);
lean_inc(x_1025);
lean_inc(x_1024);
lean_dec(x_1015);
x_1026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1026, 0, x_1024);
lean_ctor_set(x_1026, 1, x_1025);
return x_1026;
}
}
}
else
{
uint8_t x_1027; 
lean_free_object(x_5);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1027 = !lean_is_exclusive(x_1012);
if (x_1027 == 0)
{
return x_1012;
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1028 = lean_ctor_get(x_1012, 0);
x_1029 = lean_ctor_get(x_1012, 1);
lean_inc(x_1029);
lean_inc(x_1028);
lean_dec(x_1012);
x_1030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set(x_1030, 1, x_1029);
return x_1030;
}
}
}
else
{
lean_object* x_1031; lean_object* x_1032; uint64_t x_1033; lean_object* x_1034; 
x_1031 = lean_ctor_get(x_5, 0);
x_1032 = lean_ctor_get(x_5, 1);
x_1033 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_1032);
lean_inc(x_1031);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1031);
lean_inc(x_1);
x_1034 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1031, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1034, 1);
lean_inc(x_1036);
lean_dec(x_1034);
lean_inc(x_1032);
x_1037 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1032, x_6, x_7, x_8, x_9, x_10, x_11, x_1036);
if (lean_obj_tag(x_1037) == 0)
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
if (lean_is_exclusive(x_1037)) {
 lean_ctor_release(x_1037, 0);
 lean_ctor_release(x_1037, 1);
 x_1040 = x_1037;
} else {
 lean_dec_ref(x_1037);
 x_1040 = lean_box(0);
}
x_1041 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_1041, 0, x_1031);
lean_ctor_set(x_1041, 1, x_1032);
lean_ctor_set_uint64(x_1041, sizeof(void*)*2, x_1033);
x_1042 = lean_expr_update_app(x_1041, x_1035, x_1038);
if (lean_is_scalar(x_1040)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_1040;
}
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_1039);
return x_1043;
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_1035);
lean_dec(x_1032);
lean_dec(x_1031);
x_1044 = lean_ctor_get(x_1037, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1037, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_1037)) {
 lean_ctor_release(x_1037, 0);
 lean_ctor_release(x_1037, 1);
 x_1046 = x_1037;
} else {
 lean_dec_ref(x_1037);
 x_1046 = lean_box(0);
}
if (lean_is_scalar(x_1046)) {
 x_1047 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1047 = x_1046;
}
lean_ctor_set(x_1047, 0, x_1044);
lean_ctor_set(x_1047, 1, x_1045);
return x_1047;
}
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1048 = lean_ctor_get(x_1034, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1034, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1050 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
}
case 6:
{
uint8_t x_1052; 
x_1052 = !lean_is_exclusive(x_5);
if (x_1052 == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; uint64_t x_1056; lean_object* x_1057; 
x_1053 = lean_ctor_get(x_5, 0);
x_1054 = lean_ctor_get(x_5, 1);
x_1055 = lean_ctor_get(x_5, 2);
x_1056 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1054);
lean_inc(x_1);
x_1057 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1054, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
lean_dec(x_1057);
x_1060 = lean_unsigned_to_nat(1u);
x_1061 = lean_nat_add(x_6, x_1060);
lean_dec(x_6);
lean_inc(x_1055);
x_1062 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1055, x_1061, x_7, x_8, x_9, x_10, x_11, x_1059);
if (lean_obj_tag(x_1062) == 0)
{
uint8_t x_1063; 
x_1063 = !lean_is_exclusive(x_1062);
if (x_1063 == 0)
{
lean_object* x_1064; uint8_t x_1065; lean_object* x_1066; 
x_1064 = lean_ctor_get(x_1062, 0);
x_1065 = (uint8_t)((x_1056 << 24) >> 61);
x_1066 = lean_expr_update_lambda(x_5, x_1065, x_1058, x_1064);
lean_ctor_set(x_1062, 0, x_1066);
return x_1062;
}
else
{
lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; lean_object* x_1070; lean_object* x_1071; 
x_1067 = lean_ctor_get(x_1062, 0);
x_1068 = lean_ctor_get(x_1062, 1);
lean_inc(x_1068);
lean_inc(x_1067);
lean_dec(x_1062);
x_1069 = (uint8_t)((x_1056 << 24) >> 61);
x_1070 = lean_expr_update_lambda(x_5, x_1069, x_1058, x_1067);
x_1071 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_1068);
return x_1071;
}
}
else
{
uint8_t x_1072; 
lean_dec(x_1058);
lean_free_object(x_5);
lean_dec(x_1055);
lean_dec(x_1054);
lean_dec(x_1053);
x_1072 = !lean_is_exclusive(x_1062);
if (x_1072 == 0)
{
return x_1062;
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1073 = lean_ctor_get(x_1062, 0);
x_1074 = lean_ctor_get(x_1062, 1);
lean_inc(x_1074);
lean_inc(x_1073);
lean_dec(x_1062);
x_1075 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1075, 0, x_1073);
lean_ctor_set(x_1075, 1, x_1074);
return x_1075;
}
}
}
else
{
uint8_t x_1076; 
lean_free_object(x_5);
lean_dec(x_1055);
lean_dec(x_1054);
lean_dec(x_1053);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1076 = !lean_is_exclusive(x_1057);
if (x_1076 == 0)
{
return x_1057;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1077 = lean_ctor_get(x_1057, 0);
x_1078 = lean_ctor_get(x_1057, 1);
lean_inc(x_1078);
lean_inc(x_1077);
lean_dec(x_1057);
x_1079 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1079, 0, x_1077);
lean_ctor_set(x_1079, 1, x_1078);
return x_1079;
}
}
}
else
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; uint64_t x_1083; lean_object* x_1084; 
x_1080 = lean_ctor_get(x_5, 0);
x_1081 = lean_ctor_get(x_5, 1);
x_1082 = lean_ctor_get(x_5, 2);
x_1083 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1082);
lean_inc(x_1081);
lean_inc(x_1080);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1081);
lean_inc(x_1);
x_1084 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1081, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
lean_dec(x_1084);
x_1087 = lean_unsigned_to_nat(1u);
x_1088 = lean_nat_add(x_6, x_1087);
lean_dec(x_6);
lean_inc(x_1082);
x_1089 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1082, x_1088, x_7, x_8, x_9, x_10, x_11, x_1086);
if (lean_obj_tag(x_1089) == 0)
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; uint8_t x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1090 = lean_ctor_get(x_1089, 0);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1089, 1);
lean_inc(x_1091);
if (lean_is_exclusive(x_1089)) {
 lean_ctor_release(x_1089, 0);
 lean_ctor_release(x_1089, 1);
 x_1092 = x_1089;
} else {
 lean_dec_ref(x_1089);
 x_1092 = lean_box(0);
}
x_1093 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_1093, 0, x_1080);
lean_ctor_set(x_1093, 1, x_1081);
lean_ctor_set(x_1093, 2, x_1082);
lean_ctor_set_uint64(x_1093, sizeof(void*)*3, x_1083);
x_1094 = (uint8_t)((x_1083 << 24) >> 61);
x_1095 = lean_expr_update_lambda(x_1093, x_1094, x_1085, x_1090);
if (lean_is_scalar(x_1092)) {
 x_1096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1096 = x_1092;
}
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1091);
return x_1096;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_1085);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
x_1097 = lean_ctor_get(x_1089, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1089, 1);
lean_inc(x_1098);
if (lean_is_exclusive(x_1089)) {
 lean_ctor_release(x_1089, 0);
 lean_ctor_release(x_1089, 1);
 x_1099 = x_1089;
} else {
 lean_dec_ref(x_1089);
 x_1099 = lean_box(0);
}
if (lean_is_scalar(x_1099)) {
 x_1100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1100 = x_1099;
}
lean_ctor_set(x_1100, 0, x_1097);
lean_ctor_set(x_1100, 1, x_1098);
return x_1100;
}
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1101 = lean_ctor_get(x_1084, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1084, 1);
lean_inc(x_1102);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1103 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1103 = lean_box(0);
}
if (lean_is_scalar(x_1103)) {
 x_1104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1104 = x_1103;
}
lean_ctor_set(x_1104, 0, x_1101);
lean_ctor_set(x_1104, 1, x_1102);
return x_1104;
}
}
}
case 7:
{
uint8_t x_1105; 
x_1105 = !lean_is_exclusive(x_5);
if (x_1105 == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; uint64_t x_1109; lean_object* x_1110; 
x_1106 = lean_ctor_get(x_5, 0);
x_1107 = lean_ctor_get(x_5, 1);
x_1108 = lean_ctor_get(x_5, 2);
x_1109 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1107);
lean_inc(x_1);
x_1110 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1107, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1110) == 0)
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1111 = lean_ctor_get(x_1110, 0);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1110, 1);
lean_inc(x_1112);
lean_dec(x_1110);
x_1113 = lean_unsigned_to_nat(1u);
x_1114 = lean_nat_add(x_6, x_1113);
lean_dec(x_6);
lean_inc(x_1108);
x_1115 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1108, x_1114, x_7, x_8, x_9, x_10, x_11, x_1112);
if (lean_obj_tag(x_1115) == 0)
{
uint8_t x_1116; 
x_1116 = !lean_is_exclusive(x_1115);
if (x_1116 == 0)
{
lean_object* x_1117; uint8_t x_1118; lean_object* x_1119; 
x_1117 = lean_ctor_get(x_1115, 0);
x_1118 = (uint8_t)((x_1109 << 24) >> 61);
x_1119 = lean_expr_update_forall(x_5, x_1118, x_1111, x_1117);
lean_ctor_set(x_1115, 0, x_1119);
return x_1115;
}
else
{
lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1120 = lean_ctor_get(x_1115, 0);
x_1121 = lean_ctor_get(x_1115, 1);
lean_inc(x_1121);
lean_inc(x_1120);
lean_dec(x_1115);
x_1122 = (uint8_t)((x_1109 << 24) >> 61);
x_1123 = lean_expr_update_forall(x_5, x_1122, x_1111, x_1120);
x_1124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1124, 0, x_1123);
lean_ctor_set(x_1124, 1, x_1121);
return x_1124;
}
}
else
{
uint8_t x_1125; 
lean_dec(x_1111);
lean_free_object(x_5);
lean_dec(x_1108);
lean_dec(x_1107);
lean_dec(x_1106);
x_1125 = !lean_is_exclusive(x_1115);
if (x_1125 == 0)
{
return x_1115;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1115, 0);
x_1127 = lean_ctor_get(x_1115, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1115);
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1126);
lean_ctor_set(x_1128, 1, x_1127);
return x_1128;
}
}
}
else
{
uint8_t x_1129; 
lean_free_object(x_5);
lean_dec(x_1108);
lean_dec(x_1107);
lean_dec(x_1106);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1129 = !lean_is_exclusive(x_1110);
if (x_1129 == 0)
{
return x_1110;
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = lean_ctor_get(x_1110, 0);
x_1131 = lean_ctor_get(x_1110, 1);
lean_inc(x_1131);
lean_inc(x_1130);
lean_dec(x_1110);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; uint64_t x_1136; lean_object* x_1137; 
x_1133 = lean_ctor_get(x_5, 0);
x_1134 = lean_ctor_get(x_5, 1);
x_1135 = lean_ctor_get(x_5, 2);
x_1136 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1135);
lean_inc(x_1134);
lean_inc(x_1133);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1134);
lean_inc(x_1);
x_1137 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1134, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
x_1140 = lean_unsigned_to_nat(1u);
x_1141 = lean_nat_add(x_6, x_1140);
lean_dec(x_6);
lean_inc(x_1135);
x_1142 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1135, x_1141, x_7, x_8, x_9, x_10, x_11, x_1139);
if (lean_obj_tag(x_1142) == 0)
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; uint8_t x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1143 = lean_ctor_get(x_1142, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1142, 1);
lean_inc(x_1144);
if (lean_is_exclusive(x_1142)) {
 lean_ctor_release(x_1142, 0);
 lean_ctor_release(x_1142, 1);
 x_1145 = x_1142;
} else {
 lean_dec_ref(x_1142);
 x_1145 = lean_box(0);
}
x_1146 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_1146, 0, x_1133);
lean_ctor_set(x_1146, 1, x_1134);
lean_ctor_set(x_1146, 2, x_1135);
lean_ctor_set_uint64(x_1146, sizeof(void*)*3, x_1136);
x_1147 = (uint8_t)((x_1136 << 24) >> 61);
x_1148 = lean_expr_update_forall(x_1146, x_1147, x_1138, x_1143);
if (lean_is_scalar(x_1145)) {
 x_1149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1149 = x_1145;
}
lean_ctor_set(x_1149, 0, x_1148);
lean_ctor_set(x_1149, 1, x_1144);
return x_1149;
}
else
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
lean_dec(x_1138);
lean_dec(x_1135);
lean_dec(x_1134);
lean_dec(x_1133);
x_1150 = lean_ctor_get(x_1142, 0);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1142, 1);
lean_inc(x_1151);
if (lean_is_exclusive(x_1142)) {
 lean_ctor_release(x_1142, 0);
 lean_ctor_release(x_1142, 1);
 x_1152 = x_1142;
} else {
 lean_dec_ref(x_1142);
 x_1152 = lean_box(0);
}
if (lean_is_scalar(x_1152)) {
 x_1153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1153 = x_1152;
}
lean_ctor_set(x_1153, 0, x_1150);
lean_ctor_set(x_1153, 1, x_1151);
return x_1153;
}
}
else
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
lean_dec(x_1135);
lean_dec(x_1134);
lean_dec(x_1133);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1154 = lean_ctor_get(x_1137, 0);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1137, 1);
lean_inc(x_1155);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 lean_ctor_release(x_1137, 1);
 x_1156 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1156 = lean_box(0);
}
if (lean_is_scalar(x_1156)) {
 x_1157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1157 = x_1156;
}
lean_ctor_set(x_1157, 0, x_1154);
lean_ctor_set(x_1157, 1, x_1155);
return x_1157;
}
}
}
case 8:
{
uint8_t x_1158; 
x_1158 = !lean_is_exclusive(x_5);
if (x_1158 == 0)
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1159 = lean_ctor_get(x_5, 0);
x_1160 = lean_ctor_get(x_5, 1);
x_1161 = lean_ctor_get(x_5, 2);
x_1162 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1160);
lean_inc(x_1);
x_1163 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1160, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1163) == 0)
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
x_1164 = lean_ctor_get(x_1163, 0);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1163, 1);
lean_inc(x_1165);
lean_dec(x_1163);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1161);
lean_inc(x_1);
x_1166 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1161, x_6, x_7, x_8, x_9, x_10, x_11, x_1165);
if (lean_obj_tag(x_1166) == 0)
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
x_1167 = lean_ctor_get(x_1166, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1166, 1);
lean_inc(x_1168);
lean_dec(x_1166);
x_1169 = lean_unsigned_to_nat(1u);
x_1170 = lean_nat_add(x_6, x_1169);
lean_dec(x_6);
lean_inc(x_1162);
x_1171 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1162, x_1170, x_7, x_8, x_9, x_10, x_11, x_1168);
if (lean_obj_tag(x_1171) == 0)
{
uint8_t x_1172; 
x_1172 = !lean_is_exclusive(x_1171);
if (x_1172 == 0)
{
lean_object* x_1173; lean_object* x_1174; 
x_1173 = lean_ctor_get(x_1171, 0);
x_1174 = lean_expr_update_let(x_5, x_1164, x_1167, x_1173);
lean_ctor_set(x_1171, 0, x_1174);
return x_1171;
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1175 = lean_ctor_get(x_1171, 0);
x_1176 = lean_ctor_get(x_1171, 1);
lean_inc(x_1176);
lean_inc(x_1175);
lean_dec(x_1171);
x_1177 = lean_expr_update_let(x_5, x_1164, x_1167, x_1175);
x_1178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1178, 0, x_1177);
lean_ctor_set(x_1178, 1, x_1176);
return x_1178;
}
}
else
{
uint8_t x_1179; 
lean_dec(x_1167);
lean_dec(x_1164);
lean_free_object(x_5);
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_1159);
x_1179 = !lean_is_exclusive(x_1171);
if (x_1179 == 0)
{
return x_1171;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1171, 0);
x_1181 = lean_ctor_get(x_1171, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_1171);
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1180);
lean_ctor_set(x_1182, 1, x_1181);
return x_1182;
}
}
}
else
{
uint8_t x_1183; 
lean_dec(x_1164);
lean_free_object(x_5);
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_1159);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1183 = !lean_is_exclusive(x_1166);
if (x_1183 == 0)
{
return x_1166;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1166, 0);
x_1185 = lean_ctor_get(x_1166, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1166);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
else
{
uint8_t x_1187; 
lean_free_object(x_5);
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_1159);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1187 = !lean_is_exclusive(x_1163);
if (x_1187 == 0)
{
return x_1163;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1188 = lean_ctor_get(x_1163, 0);
x_1189 = lean_ctor_get(x_1163, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1163);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
return x_1190;
}
}
}
else
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; uint64_t x_1195; lean_object* x_1196; 
x_1191 = lean_ctor_get(x_5, 0);
x_1192 = lean_ctor_get(x_5, 1);
x_1193 = lean_ctor_get(x_5, 2);
x_1194 = lean_ctor_get(x_5, 3);
x_1195 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_1194);
lean_inc(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1192);
lean_inc(x_1);
x_1196 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1192, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1196, 1);
lean_inc(x_1198);
lean_dec(x_1196);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1193);
lean_inc(x_1);
x_1199 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1193, x_6, x_7, x_8, x_9, x_10, x_11, x_1198);
if (lean_obj_tag(x_1199) == 0)
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1199, 1);
lean_inc(x_1201);
lean_dec(x_1199);
x_1202 = lean_unsigned_to_nat(1u);
x_1203 = lean_nat_add(x_6, x_1202);
lean_dec(x_6);
lean_inc(x_1194);
x_1204 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1194, x_1203, x_7, x_8, x_9, x_10, x_11, x_1201);
if (lean_obj_tag(x_1204) == 0)
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
x_1205 = lean_ctor_get(x_1204, 0);
lean_inc(x_1205);
x_1206 = lean_ctor_get(x_1204, 1);
lean_inc(x_1206);
if (lean_is_exclusive(x_1204)) {
 lean_ctor_release(x_1204, 0);
 lean_ctor_release(x_1204, 1);
 x_1207 = x_1204;
} else {
 lean_dec_ref(x_1204);
 x_1207 = lean_box(0);
}
x_1208 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_1208, 0, x_1191);
lean_ctor_set(x_1208, 1, x_1192);
lean_ctor_set(x_1208, 2, x_1193);
lean_ctor_set(x_1208, 3, x_1194);
lean_ctor_set_uint64(x_1208, sizeof(void*)*4, x_1195);
x_1209 = lean_expr_update_let(x_1208, x_1197, x_1200, x_1205);
if (lean_is_scalar(x_1207)) {
 x_1210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1210 = x_1207;
}
lean_ctor_set(x_1210, 0, x_1209);
lean_ctor_set(x_1210, 1, x_1206);
return x_1210;
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
x_1211 = lean_ctor_get(x_1204, 0);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1204, 1);
lean_inc(x_1212);
if (lean_is_exclusive(x_1204)) {
 lean_ctor_release(x_1204, 0);
 lean_ctor_release(x_1204, 1);
 x_1213 = x_1204;
} else {
 lean_dec_ref(x_1204);
 x_1213 = lean_box(0);
}
if (lean_is_scalar(x_1213)) {
 x_1214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1214 = x_1213;
}
lean_ctor_set(x_1214, 0, x_1211);
lean_ctor_set(x_1214, 1, x_1212);
return x_1214;
}
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
lean_dec(x_1197);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1215 = lean_ctor_get(x_1199, 0);
lean_inc(x_1215);
x_1216 = lean_ctor_get(x_1199, 1);
lean_inc(x_1216);
if (lean_is_exclusive(x_1199)) {
 lean_ctor_release(x_1199, 0);
 lean_ctor_release(x_1199, 1);
 x_1217 = x_1199;
} else {
 lean_dec_ref(x_1199);
 x_1217 = lean_box(0);
}
if (lean_is_scalar(x_1217)) {
 x_1218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1218 = x_1217;
}
lean_ctor_set(x_1218, 0, x_1215);
lean_ctor_set(x_1218, 1, x_1216);
return x_1218;
}
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1219 = lean_ctor_get(x_1196, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1196, 1);
lean_inc(x_1220);
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 lean_ctor_release(x_1196, 1);
 x_1221 = x_1196;
} else {
 lean_dec_ref(x_1196);
 x_1221 = lean_box(0);
}
if (lean_is_scalar(x_1221)) {
 x_1222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1222 = x_1221;
}
lean_ctor_set(x_1222, 0, x_1219);
lean_ctor_set(x_1222, 1, x_1220);
return x_1222;
}
}
}
case 10:
{
uint8_t x_1223; 
x_1223 = !lean_is_exclusive(x_5);
if (x_1223 == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1224 = lean_ctor_get(x_5, 0);
x_1225 = lean_ctor_get(x_5, 1);
lean_inc(x_1225);
x_1226 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1225, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1226) == 0)
{
uint8_t x_1227; 
x_1227 = !lean_is_exclusive(x_1226);
if (x_1227 == 0)
{
lean_object* x_1228; lean_object* x_1229; 
x_1228 = lean_ctor_get(x_1226, 0);
x_1229 = lean_expr_update_mdata(x_5, x_1228);
lean_ctor_set(x_1226, 0, x_1229);
return x_1226;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
x_1230 = lean_ctor_get(x_1226, 0);
x_1231 = lean_ctor_get(x_1226, 1);
lean_inc(x_1231);
lean_inc(x_1230);
lean_dec(x_1226);
x_1232 = lean_expr_update_mdata(x_5, x_1230);
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_1232);
lean_ctor_set(x_1233, 1, x_1231);
return x_1233;
}
}
else
{
uint8_t x_1234; 
lean_free_object(x_5);
lean_dec(x_1225);
lean_dec(x_1224);
x_1234 = !lean_is_exclusive(x_1226);
if (x_1234 == 0)
{
return x_1226;
}
else
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1235 = lean_ctor_get(x_1226, 0);
x_1236 = lean_ctor_get(x_1226, 1);
lean_inc(x_1236);
lean_inc(x_1235);
lean_dec(x_1226);
x_1237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1237, 0, x_1235);
lean_ctor_set(x_1237, 1, x_1236);
return x_1237;
}
}
}
else
{
lean_object* x_1238; lean_object* x_1239; uint64_t x_1240; lean_object* x_1241; 
x_1238 = lean_ctor_get(x_5, 0);
x_1239 = lean_ctor_get(x_5, 1);
x_1240 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_1239);
lean_inc(x_1238);
lean_dec(x_5);
lean_inc(x_1239);
x_1241 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1239, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1241, 1);
lean_inc(x_1243);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 lean_ctor_release(x_1241, 1);
 x_1244 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1244 = lean_box(0);
}
x_1245 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_1245, 0, x_1238);
lean_ctor_set(x_1245, 1, x_1239);
lean_ctor_set_uint64(x_1245, sizeof(void*)*2, x_1240);
x_1246 = lean_expr_update_mdata(x_1245, x_1242);
if (lean_is_scalar(x_1244)) {
 x_1247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1247 = x_1244;
}
lean_ctor_set(x_1247, 0, x_1246);
lean_ctor_set(x_1247, 1, x_1243);
return x_1247;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_1239);
lean_dec(x_1238);
x_1248 = lean_ctor_get(x_1241, 0);
lean_inc(x_1248);
x_1249 = lean_ctor_get(x_1241, 1);
lean_inc(x_1249);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 lean_ctor_release(x_1241, 1);
 x_1250 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1250 = lean_box(0);
}
if (lean_is_scalar(x_1250)) {
 x_1251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1251 = x_1250;
}
lean_ctor_set(x_1251, 0, x_1248);
lean_ctor_set(x_1251, 1, x_1249);
return x_1251;
}
}
}
case 11:
{
uint8_t x_1252; 
x_1252 = !lean_is_exclusive(x_5);
if (x_1252 == 0)
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1253 = lean_ctor_get(x_5, 0);
x_1254 = lean_ctor_get(x_5, 1);
x_1255 = lean_ctor_get(x_5, 2);
lean_inc(x_1255);
x_1256 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1255, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1256) == 0)
{
uint8_t x_1257; 
x_1257 = !lean_is_exclusive(x_1256);
if (x_1257 == 0)
{
lean_object* x_1258; lean_object* x_1259; 
x_1258 = lean_ctor_get(x_1256, 0);
x_1259 = lean_expr_update_proj(x_5, x_1258);
lean_ctor_set(x_1256, 0, x_1259);
return x_1256;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
x_1260 = lean_ctor_get(x_1256, 0);
x_1261 = lean_ctor_get(x_1256, 1);
lean_inc(x_1261);
lean_inc(x_1260);
lean_dec(x_1256);
x_1262 = lean_expr_update_proj(x_5, x_1260);
x_1263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1263, 0, x_1262);
lean_ctor_set(x_1263, 1, x_1261);
return x_1263;
}
}
else
{
uint8_t x_1264; 
lean_free_object(x_5);
lean_dec(x_1255);
lean_dec(x_1254);
lean_dec(x_1253);
x_1264 = !lean_is_exclusive(x_1256);
if (x_1264 == 0)
{
return x_1256;
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1265 = lean_ctor_get(x_1256, 0);
x_1266 = lean_ctor_get(x_1256, 1);
lean_inc(x_1266);
lean_inc(x_1265);
lean_dec(x_1256);
x_1267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1267, 0, x_1265);
lean_ctor_set(x_1267, 1, x_1266);
return x_1267;
}
}
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; uint64_t x_1271; lean_object* x_1272; 
x_1268 = lean_ctor_get(x_5, 0);
x_1269 = lean_ctor_get(x_5, 1);
x_1270 = lean_ctor_get(x_5, 2);
x_1271 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1270);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_5);
lean_inc(x_1270);
x_1272 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1270, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1272) == 0)
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1273 = lean_ctor_get(x_1272, 0);
lean_inc(x_1273);
x_1274 = lean_ctor_get(x_1272, 1);
lean_inc(x_1274);
if (lean_is_exclusive(x_1272)) {
 lean_ctor_release(x_1272, 0);
 lean_ctor_release(x_1272, 1);
 x_1275 = x_1272;
} else {
 lean_dec_ref(x_1272);
 x_1275 = lean_box(0);
}
x_1276 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_1276, 0, x_1268);
lean_ctor_set(x_1276, 1, x_1269);
lean_ctor_set(x_1276, 2, x_1270);
lean_ctor_set_uint64(x_1276, sizeof(void*)*3, x_1271);
x_1277 = lean_expr_update_proj(x_1276, x_1273);
if (lean_is_scalar(x_1275)) {
 x_1278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1278 = x_1275;
}
lean_ctor_set(x_1278, 0, x_1277);
lean_ctor_set(x_1278, 1, x_1274);
return x_1278;
}
else
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_1270);
lean_dec(x_1269);
lean_dec(x_1268);
x_1279 = lean_ctor_get(x_1272, 0);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1272, 1);
lean_inc(x_1280);
if (lean_is_exclusive(x_1272)) {
 lean_ctor_release(x_1272, 0);
 lean_ctor_release(x_1272, 1);
 x_1281 = x_1272;
} else {
 lean_dec_ref(x_1272);
 x_1281 = lean_box(0);
}
if (lean_is_scalar(x_1281)) {
 x_1282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1282 = x_1281;
}
lean_ctor_set(x_1282, 0, x_1279);
lean_ctor_set(x_1282, 1, x_1280);
return x_1282;
}
}
}
default: 
{
lean_object* x_1283; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1283, 0, x_5);
lean_ctor_set(x_1283, 1, x_12);
return x_1283;
}
}
}
block_289:
{
lean_dec(x_13);
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_15);
lean_inc(x_1);
x_17 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_16);
x_20 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_expr_update_app(x_5, x_18, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_expr_update_app(x_5, x_18, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
x_38 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_36);
lean_inc(x_1);
x_39 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_37);
x_42 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_37, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set_uint64(x_46, sizeof(void*)*2, x_38);
x_47 = lean_expr_update_app(x_46, x_40, x_43);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_55 = x_39;
} else {
 lean_dec_ref(x_39);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
case 6:
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_5, 1);
x_60 = lean_ctor_get(x_5, 2);
x_61 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_59);
lean_inc(x_1);
x_62 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_59, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_6, x_65);
lean_dec(x_6);
lean_inc(x_60);
x_67 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_60, x_66, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = (uint8_t)((x_61 << 24) >> 61);
x_71 = lean_expr_update_lambda(x_5, x_70, x_63, x_69);
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = (uint8_t)((x_61 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_5, x_74, x_63, x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_free_object(x_5);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
x_77 = !lean_is_exclusive(x_67);
if (x_77 == 0)
{
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_5);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_62);
if (x_81 == 0)
{
return x_62;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_62, 0);
x_83 = lean_ctor_get(x_62, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_62);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_5, 0);
x_86 = lean_ctor_get(x_5, 1);
x_87 = lean_ctor_get(x_5, 2);
x_88 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_86);
lean_inc(x_1);
x_89 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_86, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_6, x_92);
lean_dec(x_6);
lean_inc(x_87);
x_94 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_87, x_93, x_7, x_8, x_9, x_10, x_11, x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_98, 0, x_85);
lean_ctor_set(x_98, 1, x_86);
lean_ctor_set(x_98, 2, x_87);
lean_ctor_set_uint64(x_98, sizeof(void*)*3, x_88);
x_99 = (uint8_t)((x_88 << 24) >> 61);
x_100 = lean_expr_update_lambda(x_98, x_99, x_90, x_95);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
x_102 = lean_ctor_get(x_94, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_104 = x_94;
} else {
 lean_dec_ref(x_94);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_106 = lean_ctor_get(x_89, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_89, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_108 = x_89;
} else {
 lean_dec_ref(x_89);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
case 7:
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_5);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint64_t x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_5, 0);
x_112 = lean_ctor_get(x_5, 1);
x_113 = lean_ctor_get(x_5, 2);
x_114 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_112);
lean_inc(x_1);
x_115 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_112, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_6, x_118);
lean_dec(x_6);
lean_inc(x_113);
x_120 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_113, x_119, x_7, x_8, x_9, x_10, x_11, x_117);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = (uint8_t)((x_114 << 24) >> 61);
x_124 = lean_expr_update_forall(x_5, x_123, x_116, x_122);
lean_ctor_set(x_120, 0, x_124);
return x_120;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_120, 0);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_120);
x_127 = (uint8_t)((x_114 << 24) >> 61);
x_128 = lean_expr_update_forall(x_5, x_127, x_116, x_125);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_116);
lean_free_object(x_5);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
x_130 = !lean_is_exclusive(x_120);
if (x_130 == 0)
{
return x_120;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_120, 0);
x_132 = lean_ctor_get(x_120, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_120);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_free_object(x_5);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_115);
if (x_134 == 0)
{
return x_115;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_115, 0);
x_136 = lean_ctor_get(x_115, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_115);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint64_t x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_5, 0);
x_139 = lean_ctor_get(x_5, 1);
x_140 = lean_ctor_get(x_5, 2);
x_141 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_139);
lean_inc(x_1);
x_142 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_139, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_6, x_145);
lean_dec(x_6);
lean_inc(x_140);
x_147 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_140, x_146, x_7, x_8, x_9, x_10, x_11, x_144);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_151, 0, x_138);
lean_ctor_set(x_151, 1, x_139);
lean_ctor_set(x_151, 2, x_140);
lean_ctor_set_uint64(x_151, sizeof(void*)*3, x_141);
x_152 = (uint8_t)((x_141 << 24) >> 61);
x_153 = lean_expr_update_forall(x_151, x_152, x_143, x_148);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_143);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_155 = lean_ctor_get(x_147, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_147, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_157 = x_147;
} else {
 lean_dec_ref(x_147);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_159 = lean_ctor_get(x_142, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_142, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_161 = x_142;
} else {
 lean_dec_ref(x_142);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
case 8:
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_5);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_5, 0);
x_165 = lean_ctor_get(x_5, 1);
x_166 = lean_ctor_get(x_5, 2);
x_167 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_165);
lean_inc(x_1);
x_168 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_165, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_166);
lean_inc(x_1);
x_171 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_166, x_6, x_7, x_8, x_9, x_10, x_11, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_add(x_6, x_174);
lean_dec(x_6);
lean_inc(x_167);
x_176 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_167, x_175, x_7, x_8, x_9, x_10, x_11, x_173);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_expr_update_let(x_5, x_169, x_172, x_178);
lean_ctor_set(x_176, 0, x_179);
return x_176;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_176, 0);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_176);
x_182 = lean_expr_update_let(x_5, x_169, x_172, x_180);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_172);
lean_dec(x_169);
lean_free_object(x_5);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
x_184 = !lean_is_exclusive(x_176);
if (x_184 == 0)
{
return x_176;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_176, 0);
x_186 = lean_ctor_get(x_176, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_176);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_169);
lean_free_object(x_5);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_171);
if (x_188 == 0)
{
return x_171;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_171, 0);
x_190 = lean_ctor_get(x_171, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_171);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_free_object(x_5);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_168);
if (x_192 == 0)
{
return x_168;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_168, 0);
x_194 = lean_ctor_get(x_168, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_168);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_5, 0);
x_197 = lean_ctor_get(x_5, 1);
x_198 = lean_ctor_get(x_5, 2);
x_199 = lean_ctor_get(x_5, 3);
x_200 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_197);
lean_inc(x_1);
x_201 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_197, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_198);
lean_inc(x_1);
x_204 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_198, x_6, x_7, x_8, x_9, x_10, x_11, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_add(x_6, x_207);
lean_dec(x_6);
lean_inc(x_199);
x_209 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_199, x_208, x_7, x_8, x_9, x_10, x_11, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_213, 0, x_196);
lean_ctor_set(x_213, 1, x_197);
lean_ctor_set(x_213, 2, x_198);
lean_ctor_set(x_213, 3, x_199);
lean_ctor_set_uint64(x_213, sizeof(void*)*4, x_200);
x_214 = lean_expr_update_let(x_213, x_202, x_205, x_210);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_211);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_205);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
x_216 = lean_ctor_get(x_209, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_209, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_218 = x_209;
} else {
 lean_dec_ref(x_209);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_220 = lean_ctor_get(x_204, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_204, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_222 = x_204;
} else {
 lean_dec_ref(x_204);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_224 = lean_ctor_get(x_201, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_201, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_226 = x_201;
} else {
 lean_dec_ref(x_201);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
}
case 10:
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_5);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_5, 0);
x_230 = lean_ctor_get(x_5, 1);
lean_inc(x_230);
x_231 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_230, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_231) == 0)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = lean_expr_update_mdata(x_5, x_233);
lean_ctor_set(x_231, 0, x_234);
return x_231;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_231, 0);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_231);
x_237 = lean_expr_update_mdata(x_5, x_235);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
uint8_t x_239; 
lean_free_object(x_5);
lean_dec(x_230);
lean_dec(x_229);
x_239 = !lean_is_exclusive(x_231);
if (x_239 == 0)
{
return x_231;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_231, 0);
x_241 = lean_ctor_get(x_231, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_231);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; uint64_t x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_5, 0);
x_244 = lean_ctor_get(x_5, 1);
x_245 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_5);
lean_inc(x_244);
x_246 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_244, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_244);
lean_ctor_set_uint64(x_250, sizeof(void*)*2, x_245);
x_251 = lean_expr_update_mdata(x_250, x_247);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_248);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_244);
lean_dec(x_243);
x_253 = lean_ctor_get(x_246, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_246, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_255 = x_246;
} else {
 lean_dec_ref(x_246);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
case 11:
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_5);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_5, 0);
x_259 = lean_ctor_get(x_5, 1);
x_260 = lean_ctor_get(x_5, 2);
lean_inc(x_260);
x_261 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_260, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_expr_update_proj(x_5, x_263);
lean_ctor_set(x_261, 0, x_264);
return x_261;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_261, 0);
x_266 = lean_ctor_get(x_261, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_261);
x_267 = lean_expr_update_proj(x_5, x_265);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
else
{
uint8_t x_269; 
lean_free_object(x_5);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
x_269 = !lean_is_exclusive(x_261);
if (x_269 == 0)
{
return x_261;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_261, 0);
x_271 = lean_ctor_get(x_261, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_261);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint64_t x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_5, 0);
x_274 = lean_ctor_get(x_5, 1);
x_275 = lean_ctor_get(x_5, 2);
x_276 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_5);
lean_inc(x_275);
x_277 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_275, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_280 = x_277;
} else {
 lean_dec_ref(x_277);
 x_280 = lean_box(0);
}
x_281 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_281, 0, x_273);
lean_ctor_set(x_281, 1, x_274);
lean_ctor_set(x_281, 2, x_275);
lean_ctor_set_uint64(x_281, sizeof(void*)*3, x_276);
x_282 = lean_expr_update_proj(x_281, x_278);
if (lean_is_scalar(x_280)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_280;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_279);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
x_284 = lean_ctor_get(x_277, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_277, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_286 = x_277;
} else {
 lean_dec_ref(x_277);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
}
default: 
{
lean_object* x_288; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_5);
lean_ctor_set(x_288, 1, x_12);
return x_288;
}
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_commitWhen___at_Lean_Meta_kabstract_visit___spec__3(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isFVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = l_Lean_Expr_toHeadIndex(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_st_mk_ref(x_13, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_10, x_12, x_3, x_11, x_15, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = l_Lean_Occurrences_beq(x_2, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = l_Lean_Expr_toHeadIndex(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_st_mk_ref(x_34, x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_31, x_33, x_3, x_32, x_36, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_33);
lean_dec(x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_36, x_40);
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_36);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = l_Lean_mkOptionalNode___closed__2;
x_51 = lean_array_push(x_50, x_1);
x_52 = lean_expr_abstract(x_3, x_51);
lean_dec(x_51);
lean_dec(x_3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_8);
return x_53;
}
}
}
}
lean_object* l_Lean_Meta_kabstract___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1), 6, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_kabstract(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Occurrences(lean_object*);
lean_object* initialize_Lean_HeadIndex(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_KAbstract(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Occurrences(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_HeadIndex(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
