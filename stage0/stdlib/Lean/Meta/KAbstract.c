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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__6___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_isLevelDefEq___spec__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
extern lean_object* l_Lean_Meta_isLevelDefEqAux___closed__6;
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit_match__1(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; 
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 8, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
x_440 = lean_st_ref_get(x_7, x_8);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_441, 3);
lean_inc(x_442);
lean_dec(x_441);
x_443 = lean_ctor_get_uint8(x_442, sizeof(void*)*1);
lean_dec(x_442);
if (x_443 == 0)
{
lean_object* x_444; uint8_t x_445; 
x_444 = lean_ctor_get(x_440, 1);
lean_inc(x_444);
lean_dec(x_440);
x_445 = 0;
x_23 = x_445;
x_24 = x_444;
goto block_439;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_446 = lean_ctor_get(x_440, 1);
lean_inc(x_446);
lean_dec(x_440);
x_447 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_448 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_447, x_4, x_5, x_6, x_7, x_446);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_unbox(x_449);
lean_dec(x_449);
x_23 = x_451;
x_24 = x_450;
goto block_439;
}
block_21:
{
if (lean_obj_tag(x_9) == 0)
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
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
block_439:
{
uint8_t x_25; 
if (x_23 == 0)
{
uint8_t x_437; 
x_437 = 1;
x_25 = x_437;
goto block_436;
}
else
{
uint8_t x_438; 
x_438 = 0;
x_25 = x_438;
goto block_436;
}
block_436:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_41; lean_object* x_42; lean_object* x_50; 
x_26 = lean_ctor_get(x_6, 3);
lean_inc(x_26);
x_27 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_isLevelDefEq___spec__2___rarg(x_7, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_50 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_22, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_81 = lean_st_ref_get(x_7, x_52);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = 0;
x_53 = x_86;
x_54 = x_85;
goto block_80;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_89 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_88, x_4, x_5, x_6, x_7, x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_53 = x_92;
x_54 = x_91;
goto block_80;
}
block_80:
{
if (x_53 == 0)
{
uint8_t x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_unbox(x_51);
lean_dec(x_51);
x_30 = x_55;
x_31 = x_54;
goto block_40;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_1);
x_57 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_2);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_unbox(x_51);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_66 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_57);
x_69 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_70 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_69, x_68, x_4, x_5, x_6, x_7, x_54);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_unbox(x_51);
lean_dec(x_51);
x_30 = x_72;
x_31 = x_71;
goto block_40;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_76 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_77 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_76, x_75, x_4, x_5, x_6, x_7, x_54);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_unbox(x_51);
lean_dec(x_51);
x_30 = x_79;
x_31 = x_78;
goto block_40;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_50, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_50, 1);
lean_inc(x_94);
lean_dec(x_50);
x_41 = x_93;
x_42 = x_94;
goto block_49;
}
block_40:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_33 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(x_28, x_32, x_26, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(x_30);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(x_30);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
block_49:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_44 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__3(x_28, x_43, x_26, x_4, x_5, x_6, x_7, x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_95 = lean_st_ref_get(x_7, x_24);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 3);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_ctor_get_uint8(x_97, sizeof(void*)*1);
lean_dec(x_97);
x_100 = lean_st_ref_take(x_7, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_101, 3);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_102);
if (x_106 == 0)
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_159; lean_object* x_160; lean_object* x_193; 
x_107 = 0;
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_107);
x_108 = lean_st_ref_set(x_7, x_101, x_103);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_193 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_22, x_4, x_5, x_6, x_7, x_109);
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
x_196 = x_107;
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
x_231 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_230, x_4, x_5, x_6, x_7, x_229);
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
x_110 = x_198;
x_111 = x_197;
goto block_158;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_199 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_199, 0, x_1);
x_200 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_206 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_unbox(x_194);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_209 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_200);
x_212 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_213 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_212, x_211, x_4, x_5, x_6, x_7, x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_unbox(x_194);
lean_dec(x_194);
x_110 = x_215;
x_111 = x_214;
goto block_158;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_216 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_217 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_200);
x_219 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_220 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_219, x_218, x_4, x_5, x_6, x_7, x_197);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_unbox(x_194);
lean_dec(x_194);
x_110 = x_222;
x_111 = x_221;
goto block_158;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; 
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
x_159 = x_235;
x_160 = x_236;
goto block_192;
}
block_158:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_112 = lean_st_ref_get(x_7, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 3);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*1);
lean_dec(x_115);
x_117 = lean_st_ref_take(x_7, x_114);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = !lean_is_exclusive(x_118);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_118, 3);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_119);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_99);
x_124 = lean_st_ref_set(x_7, x_118, x_120);
lean_dec(x_7);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_124, 0);
lean_dec(x_126);
x_127 = lean_box(x_110);
x_128 = lean_box(x_116);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_124, 0, x_129);
x_9 = x_124;
goto block_21;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_dec(x_124);
x_131 = lean_box(x_110);
x_132 = lean_box(x_116);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_130);
x_9 = x_134;
goto block_21;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
lean_dec(x_119);
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_99);
lean_ctor_set(x_118, 3, x_136);
x_137 = lean_st_ref_set(x_7, x_118, x_120);
lean_dec(x_7);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = lean_box(x_110);
x_141 = lean_box(x_116);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_138);
x_9 = x_143;
goto block_21;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_144 = lean_ctor_get(x_118, 0);
x_145 = lean_ctor_get(x_118, 1);
x_146 = lean_ctor_get(x_118, 2);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_118);
x_147 = lean_ctor_get(x_119, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_148 = x_119;
} else {
 lean_dec_ref(x_119);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 1, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_99);
x_150 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_150, 0, x_144);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set(x_150, 2, x_146);
lean_ctor_set(x_150, 3, x_149);
x_151 = lean_st_ref_set(x_7, x_150, x_120);
lean_dec(x_7);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_box(x_110);
x_155 = lean_box(x_116);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
x_9 = x_157;
goto block_21;
}
}
block_192:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_161 = lean_st_ref_get(x_7, x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_st_ref_take(x_7, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = !lean_is_exclusive(x_164);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_164, 3);
lean_dec(x_168);
x_169 = !lean_is_exclusive(x_165);
if (x_169 == 0)
{
lean_object* x_170; uint8_t x_171; 
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_99);
x_170 = lean_st_ref_set(x_7, x_164, x_166);
lean_dec(x_7);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_170, 0);
lean_dec(x_172);
lean_ctor_set_tag(x_170, 1);
lean_ctor_set(x_170, 0, x_159);
x_9 = x_170;
goto block_21;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_159);
lean_ctor_set(x_174, 1, x_173);
x_9 = x_174;
goto block_21;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_165, 0);
lean_inc(x_175);
lean_dec(x_165);
x_176 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_99);
lean_ctor_set(x_164, 3, x_176);
x_177 = lean_st_ref_set(x_7, x_164, x_166);
lean_dec(x_7);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
 lean_ctor_set_tag(x_180, 1);
}
lean_ctor_set(x_180, 0, x_159);
lean_ctor_set(x_180, 1, x_178);
x_9 = x_180;
goto block_21;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_181 = lean_ctor_get(x_164, 0);
x_182 = lean_ctor_get(x_164, 1);
x_183 = lean_ctor_get(x_164, 2);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_164);
x_184 = lean_ctor_get(x_165, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_185 = x_165;
} else {
 lean_dec_ref(x_165);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 1, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_99);
x_187 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_182);
lean_ctor_set(x_187, 2, x_183);
lean_ctor_set(x_187, 3, x_186);
x_188 = lean_st_ref_set(x_7, x_187, x_166);
lean_dec(x_7);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_159);
lean_ctor_set(x_191, 1, x_189);
x_9 = x_191;
goto block_21;
}
}
}
else
{
lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_269; lean_object* x_270; lean_object* x_290; 
x_237 = lean_ctor_get(x_102, 0);
lean_inc(x_237);
lean_dec(x_102);
x_238 = 0;
x_239 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set_uint8(x_239, sizeof(void*)*1, x_238);
lean_ctor_set(x_101, 3, x_239);
x_240 = lean_st_ref_set(x_7, x_101, x_103);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_290 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_22, x_4, x_5, x_6, x_7, x_241);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_321 = lean_st_ref_get(x_7, x_292);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_322, 3);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_ctor_get_uint8(x_323, sizeof(void*)*1);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
lean_dec(x_321);
x_293 = x_238;
x_294 = x_325;
goto block_320;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_326 = lean_ctor_get(x_321, 1);
lean_inc(x_326);
lean_dec(x_321);
x_327 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_328 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_327, x_4, x_5, x_6, x_7, x_326);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_unbox(x_329);
lean_dec(x_329);
x_293 = x_331;
x_294 = x_330;
goto block_320;
}
block_320:
{
if (x_293 == 0)
{
uint8_t x_295; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_unbox(x_291);
lean_dec(x_291);
x_242 = x_295;
x_243 = x_294;
goto block_268;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_296 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_296, 0, x_1);
x_297 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_298 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
x_299 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_300 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_301, 0, x_2);
x_302 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_304 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_unbox(x_291);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_306 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_307 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_297);
x_309 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_310 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_309, x_308, x_4, x_5, x_6, x_7, x_294);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_unbox(x_291);
lean_dec(x_291);
x_242 = x_312;
x_243 = x_311;
goto block_268;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_313 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_314 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_314, 0, x_304);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_297);
x_316 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_317 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_316, x_315, x_4, x_5, x_6, x_7, x_294);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = lean_unbox(x_291);
lean_dec(x_291);
x_242 = x_319;
x_243 = x_318;
goto block_268;
}
}
}
}
else
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_332 = lean_ctor_get(x_290, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_290, 1);
lean_inc(x_333);
lean_dec(x_290);
x_269 = x_332;
x_270 = x_333;
goto block_289;
}
block_268:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_244 = lean_st_ref_get(x_7, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 3);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get_uint8(x_247, sizeof(void*)*1);
lean_dec(x_247);
x_249 = lean_st_ref_take(x_7, x_246);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_250, 3);
lean_inc(x_251);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
x_253 = lean_ctor_get(x_250, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_250, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_250, 2);
lean_inc(x_255);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_256 = x_250;
} else {
 lean_dec_ref(x_250);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_251, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_258 = x_251;
} else {
 lean_dec_ref(x_251);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 1, 1);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_99);
if (lean_is_scalar(x_256)) {
 x_260 = lean_alloc_ctor(0, 4, 0);
} else {
 x_260 = x_256;
}
lean_ctor_set(x_260, 0, x_253);
lean_ctor_set(x_260, 1, x_254);
lean_ctor_set(x_260, 2, x_255);
lean_ctor_set(x_260, 3, x_259);
x_261 = lean_st_ref_set(x_7, x_260, x_252);
lean_dec(x_7);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
x_264 = lean_box(x_242);
x_265 = lean_box(x_248);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
if (lean_is_scalar(x_263)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_263;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_262);
x_9 = x_267;
goto block_21;
}
block_289:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_271 = lean_st_ref_get(x_7, x_270);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_st_ref_take(x_7, x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_274, 3);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_277 = lean_ctor_get(x_274, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 2);
lean_inc(x_279);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 lean_ctor_release(x_274, 3);
 x_280 = x_274;
} else {
 lean_dec_ref(x_274);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_282 = x_275;
} else {
 lean_dec_ref(x_275);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 1, 1);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set_uint8(x_283, sizeof(void*)*1, x_99);
if (lean_is_scalar(x_280)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_280;
}
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set(x_284, 1, x_278);
lean_ctor_set(x_284, 2, x_279);
lean_ctor_set(x_284, 3, x_283);
x_285 = lean_st_ref_set(x_7, x_284, x_276);
lean_dec(x_7);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
 lean_ctor_set_tag(x_288, 1);
}
lean_ctor_set(x_288, 0, x_269);
lean_ctor_set(x_288, 1, x_286);
x_9 = x_288;
goto block_21;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_371; lean_object* x_372; lean_object* x_392; 
x_334 = lean_ctor_get(x_101, 0);
x_335 = lean_ctor_get(x_101, 1);
x_336 = lean_ctor_get(x_101, 2);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_101);
x_337 = lean_ctor_get(x_102, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_338 = x_102;
} else {
 lean_dec_ref(x_102);
 x_338 = lean_box(0);
}
x_339 = 0;
if (lean_is_scalar(x_338)) {
 x_340 = lean_alloc_ctor(0, 1, 1);
} else {
 x_340 = x_338;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set_uint8(x_340, sizeof(void*)*1, x_339);
x_341 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_341, 0, x_334);
lean_ctor_set(x_341, 1, x_335);
lean_ctor_set(x_341, 2, x_336);
lean_ctor_set(x_341, 3, x_340);
x_342 = lean_st_ref_set(x_7, x_341, x_103);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_392 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_22, x_4, x_5, x_6, x_7, x_343);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_423 = lean_st_ref_get(x_7, x_394);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_424, 3);
lean_inc(x_425);
lean_dec(x_424);
x_426 = lean_ctor_get_uint8(x_425, sizeof(void*)*1);
lean_dec(x_425);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
lean_dec(x_423);
x_395 = x_339;
x_396 = x_427;
goto block_422;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_428 = lean_ctor_get(x_423, 1);
lean_inc(x_428);
lean_dec(x_423);
x_429 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_430 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_429, x_4, x_5, x_6, x_7, x_428);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_unbox(x_431);
lean_dec(x_431);
x_395 = x_433;
x_396 = x_432;
goto block_422;
}
block_422:
{
if (x_395 == 0)
{
uint8_t x_397; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_397 = lean_unbox(x_393);
lean_dec(x_393);
x_344 = x_397;
x_345 = x_396;
goto block_370;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_398 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_398, 0, x_1);
x_399 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_400 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_401 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_402 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_403, 0, x_2);
x_404 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
x_405 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_406 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_unbox(x_393);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_408 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_409 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_399);
x_411 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_412 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_411, x_410, x_4, x_5, x_6, x_7, x_396);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
lean_dec(x_412);
x_414 = lean_unbox(x_393);
lean_dec(x_393);
x_344 = x_414;
x_345 = x_413;
goto block_370;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_415 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_416 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_416, 0, x_406);
lean_ctor_set(x_416, 1, x_415);
x_417 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_399);
x_418 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_419 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__4(x_418, x_417, x_4, x_5, x_6, x_7, x_396);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = lean_unbox(x_393);
lean_dec(x_393);
x_344 = x_421;
x_345 = x_420;
goto block_370;
}
}
}
}
else
{
lean_object* x_434; lean_object* x_435; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_434 = lean_ctor_get(x_392, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_392, 1);
lean_inc(x_435);
lean_dec(x_392);
x_371 = x_434;
x_372 = x_435;
goto block_391;
}
block_370:
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_346 = lean_st_ref_get(x_7, x_345);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_ctor_get(x_347, 3);
lean_inc(x_349);
lean_dec(x_347);
x_350 = lean_ctor_get_uint8(x_349, sizeof(void*)*1);
lean_dec(x_349);
x_351 = lean_st_ref_take(x_7, x_348);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_352, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec(x_351);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_352, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_358 = x_352;
} else {
 lean_dec_ref(x_352);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_353, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_360 = x_353;
} else {
 lean_dec_ref(x_353);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(0, 1, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*1, x_99);
if (lean_is_scalar(x_358)) {
 x_362 = lean_alloc_ctor(0, 4, 0);
} else {
 x_362 = x_358;
}
lean_ctor_set(x_362, 0, x_355);
lean_ctor_set(x_362, 1, x_356);
lean_ctor_set(x_362, 2, x_357);
lean_ctor_set(x_362, 3, x_361);
x_363 = lean_st_ref_set(x_7, x_362, x_354);
lean_dec(x_7);
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
x_366 = lean_box(x_344);
x_367 = lean_box(x_350);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
if (lean_is_scalar(x_365)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_365;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_364);
x_9 = x_369;
goto block_21;
}
block_391:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_373 = lean_st_ref_get(x_7, x_372);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
lean_dec(x_373);
x_375 = lean_st_ref_take(x_7, x_374);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_376, 3);
lean_inc(x_377);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
lean_dec(x_375);
x_379 = lean_ctor_get(x_376, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_376, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_376, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_382 = x_376;
} else {
 lean_dec_ref(x_376);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_377, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_384 = x_377;
} else {
 lean_dec_ref(x_377);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(0, 1, 1);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set_uint8(x_385, sizeof(void*)*1, x_99);
if (lean_is_scalar(x_382)) {
 x_386 = lean_alloc_ctor(0, 4, 0);
} else {
 x_386 = x_382;
}
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_385);
x_387 = lean_st_ref_set(x_7, x_386, x_378);
lean_dec(x_7);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
 lean_ctor_set_tag(x_390, 1);
}
lean_ctor_set(x_390, 0, x_371);
lean_ctor_set(x_390, 1, x_388);
x_9 = x_390;
goto block_21;
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_1001; 
x_1001 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_1001 == 0)
{
lean_object* x_1002; uint8_t x_1003; 
x_1002 = l_Lean_Expr_toHeadIndex(x_5);
x_1003 = l_Lean_HeadIndex_HeadIndex_beq(x_1002, x_3);
lean_dec(x_1002);
if (x_1003 == 0)
{
uint8_t x_1004; 
x_1004 = 1;
x_13 = x_1004;
goto block_1000;
}
else
{
lean_object* x_1005; lean_object* x_1006; uint8_t x_1007; 
x_1005 = lean_unsigned_to_nat(0u);
x_1006 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_5, x_1005);
x_1007 = lean_nat_dec_eq(x_1006, x_4);
lean_dec(x_1006);
if (x_1007 == 0)
{
uint8_t x_1008; 
x_1008 = 1;
x_13 = x_1008;
goto block_1000;
}
else
{
uint8_t x_1009; 
x_1009 = 0;
x_13 = x_1009;
goto block_1000;
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_1010; 
x_1010 = !lean_is_exclusive(x_5);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_5, 0);
x_1012 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1011);
lean_inc(x_1);
x_1013 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1011, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_1013, 1);
lean_inc(x_1015);
lean_dec(x_1013);
lean_inc(x_1012);
x_1016 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1012, x_6, x_7, x_8, x_9, x_10, x_11, x_1015);
if (lean_obj_tag(x_1016) == 0)
{
uint8_t x_1017; 
x_1017 = !lean_is_exclusive(x_1016);
if (x_1017 == 0)
{
lean_object* x_1018; lean_object* x_1019; 
x_1018 = lean_ctor_get(x_1016, 0);
x_1019 = lean_expr_update_app(x_5, x_1014, x_1018);
lean_ctor_set(x_1016, 0, x_1019);
return x_1016;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1020 = lean_ctor_get(x_1016, 0);
x_1021 = lean_ctor_get(x_1016, 1);
lean_inc(x_1021);
lean_inc(x_1020);
lean_dec(x_1016);
x_1022 = lean_expr_update_app(x_5, x_1014, x_1020);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
}
else
{
uint8_t x_1024; 
lean_dec(x_1014);
lean_free_object(x_5);
lean_dec(x_1012);
lean_dec(x_1011);
x_1024 = !lean_is_exclusive(x_1016);
if (x_1024 == 0)
{
return x_1016;
}
else
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
x_1025 = lean_ctor_get(x_1016, 0);
x_1026 = lean_ctor_get(x_1016, 1);
lean_inc(x_1026);
lean_inc(x_1025);
lean_dec(x_1016);
x_1027 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1027, 0, x_1025);
lean_ctor_set(x_1027, 1, x_1026);
return x_1027;
}
}
}
else
{
uint8_t x_1028; 
lean_free_object(x_5);
lean_dec(x_1012);
lean_dec(x_1011);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1028 = !lean_is_exclusive(x_1013);
if (x_1028 == 0)
{
return x_1013;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_1013, 0);
x_1030 = lean_ctor_get(x_1013, 1);
lean_inc(x_1030);
lean_inc(x_1029);
lean_dec(x_1013);
x_1031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1031, 0, x_1029);
lean_ctor_set(x_1031, 1, x_1030);
return x_1031;
}
}
}
else
{
lean_object* x_1032; lean_object* x_1033; uint64_t x_1034; lean_object* x_1035; 
x_1032 = lean_ctor_get(x_5, 0);
x_1033 = lean_ctor_get(x_5, 1);
x_1034 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_1033);
lean_inc(x_1032);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1032);
lean_inc(x_1);
x_1035 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1032, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1035, 1);
lean_inc(x_1037);
lean_dec(x_1035);
lean_inc(x_1033);
x_1038 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1033, x_6, x_7, x_8, x_9, x_10, x_11, x_1037);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1041 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1041 = lean_box(0);
}
x_1042 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_1042, 0, x_1032);
lean_ctor_set(x_1042, 1, x_1033);
lean_ctor_set_uint64(x_1042, sizeof(void*)*2, x_1034);
x_1043 = lean_expr_update_app(x_1042, x_1036, x_1039);
if (lean_is_scalar(x_1041)) {
 x_1044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1044 = x_1041;
}
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_1040);
return x_1044;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_1036);
lean_dec(x_1033);
lean_dec(x_1032);
x_1045 = lean_ctor_get(x_1038, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1038, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1047 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1045);
lean_ctor_set(x_1048, 1, x_1046);
return x_1048;
}
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1049 = lean_ctor_get(x_1035, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1035, 1);
lean_inc(x_1050);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1051 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1051 = lean_box(0);
}
if (lean_is_scalar(x_1051)) {
 x_1052 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1052 = x_1051;
}
lean_ctor_set(x_1052, 0, x_1049);
lean_ctor_set(x_1052, 1, x_1050);
return x_1052;
}
}
}
case 6:
{
uint8_t x_1053; 
x_1053 = !lean_is_exclusive(x_5);
if (x_1053 == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; uint64_t x_1057; lean_object* x_1058; 
x_1054 = lean_ctor_get(x_5, 0);
x_1055 = lean_ctor_get(x_5, 1);
x_1056 = lean_ctor_get(x_5, 2);
x_1057 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1055);
lean_inc(x_1);
x_1058 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1055, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1058) == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1059 = lean_ctor_get(x_1058, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1058, 1);
lean_inc(x_1060);
lean_dec(x_1058);
x_1061 = lean_unsigned_to_nat(1u);
x_1062 = lean_nat_add(x_6, x_1061);
lean_dec(x_6);
lean_inc(x_1056);
x_1063 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1056, x_1062, x_7, x_8, x_9, x_10, x_11, x_1060);
if (lean_obj_tag(x_1063) == 0)
{
uint8_t x_1064; 
x_1064 = !lean_is_exclusive(x_1063);
if (x_1064 == 0)
{
lean_object* x_1065; uint8_t x_1066; lean_object* x_1067; 
x_1065 = lean_ctor_get(x_1063, 0);
x_1066 = (uint8_t)((x_1057 << 24) >> 61);
x_1067 = lean_expr_update_lambda(x_5, x_1066, x_1059, x_1065);
lean_ctor_set(x_1063, 0, x_1067);
return x_1063;
}
else
{
lean_object* x_1068; lean_object* x_1069; uint8_t x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1068 = lean_ctor_get(x_1063, 0);
x_1069 = lean_ctor_get(x_1063, 1);
lean_inc(x_1069);
lean_inc(x_1068);
lean_dec(x_1063);
x_1070 = (uint8_t)((x_1057 << 24) >> 61);
x_1071 = lean_expr_update_lambda(x_5, x_1070, x_1059, x_1068);
x_1072 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1072, 0, x_1071);
lean_ctor_set(x_1072, 1, x_1069);
return x_1072;
}
}
else
{
uint8_t x_1073; 
lean_dec(x_1059);
lean_free_object(x_5);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_1054);
x_1073 = !lean_is_exclusive(x_1063);
if (x_1073 == 0)
{
return x_1063;
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1074 = lean_ctor_get(x_1063, 0);
x_1075 = lean_ctor_get(x_1063, 1);
lean_inc(x_1075);
lean_inc(x_1074);
lean_dec(x_1063);
x_1076 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1076, 0, x_1074);
lean_ctor_set(x_1076, 1, x_1075);
return x_1076;
}
}
}
else
{
uint8_t x_1077; 
lean_free_object(x_5);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_1054);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1077 = !lean_is_exclusive(x_1058);
if (x_1077 == 0)
{
return x_1058;
}
else
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1058, 0);
x_1079 = lean_ctor_get(x_1058, 1);
lean_inc(x_1079);
lean_inc(x_1078);
lean_dec(x_1058);
x_1080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1080, 0, x_1078);
lean_ctor_set(x_1080, 1, x_1079);
return x_1080;
}
}
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; uint64_t x_1084; lean_object* x_1085; 
x_1081 = lean_ctor_get(x_5, 0);
x_1082 = lean_ctor_get(x_5, 1);
x_1083 = lean_ctor_get(x_5, 2);
x_1084 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1083);
lean_inc(x_1082);
lean_inc(x_1081);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1082);
lean_inc(x_1);
x_1085 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1082, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1085) == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
x_1086 = lean_ctor_get(x_1085, 0);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1085, 1);
lean_inc(x_1087);
lean_dec(x_1085);
x_1088 = lean_unsigned_to_nat(1u);
x_1089 = lean_nat_add(x_6, x_1088);
lean_dec(x_6);
lean_inc(x_1083);
x_1090 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1083, x_1089, x_7, x_8, x_9, x_10, x_11, x_1087);
if (lean_obj_tag(x_1090) == 0)
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1091 = lean_ctor_get(x_1090, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1090, 1);
lean_inc(x_1092);
if (lean_is_exclusive(x_1090)) {
 lean_ctor_release(x_1090, 0);
 lean_ctor_release(x_1090, 1);
 x_1093 = x_1090;
} else {
 lean_dec_ref(x_1090);
 x_1093 = lean_box(0);
}
x_1094 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_1094, 0, x_1081);
lean_ctor_set(x_1094, 1, x_1082);
lean_ctor_set(x_1094, 2, x_1083);
lean_ctor_set_uint64(x_1094, sizeof(void*)*3, x_1084);
x_1095 = (uint8_t)((x_1084 << 24) >> 61);
x_1096 = lean_expr_update_lambda(x_1094, x_1095, x_1086, x_1091);
if (lean_is_scalar(x_1093)) {
 x_1097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1097 = x_1093;
}
lean_ctor_set(x_1097, 0, x_1096);
lean_ctor_set(x_1097, 1, x_1092);
return x_1097;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_1086);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
x_1098 = lean_ctor_get(x_1090, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1090, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1090)) {
 lean_ctor_release(x_1090, 0);
 lean_ctor_release(x_1090, 1);
 x_1100 = x_1090;
} else {
 lean_dec_ref(x_1090);
 x_1100 = lean_box(0);
}
if (lean_is_scalar(x_1100)) {
 x_1101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1101 = x_1100;
}
lean_ctor_set(x_1101, 0, x_1098);
lean_ctor_set(x_1101, 1, x_1099);
return x_1101;
}
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1102 = lean_ctor_get(x_1085, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1085, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 lean_ctor_release(x_1085, 1);
 x_1104 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1102);
lean_ctor_set(x_1105, 1, x_1103);
return x_1105;
}
}
}
case 7:
{
uint8_t x_1106; 
x_1106 = !lean_is_exclusive(x_5);
if (x_1106 == 0)
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; uint64_t x_1110; lean_object* x_1111; 
x_1107 = lean_ctor_get(x_5, 0);
x_1108 = lean_ctor_get(x_5, 1);
x_1109 = lean_ctor_get(x_5, 2);
x_1110 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1108);
lean_inc(x_1);
x_1111 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1108, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1111) == 0)
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
lean_dec(x_1111);
x_1114 = lean_unsigned_to_nat(1u);
x_1115 = lean_nat_add(x_6, x_1114);
lean_dec(x_6);
lean_inc(x_1109);
x_1116 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1109, x_1115, x_7, x_8, x_9, x_10, x_11, x_1113);
if (lean_obj_tag(x_1116) == 0)
{
uint8_t x_1117; 
x_1117 = !lean_is_exclusive(x_1116);
if (x_1117 == 0)
{
lean_object* x_1118; uint8_t x_1119; lean_object* x_1120; 
x_1118 = lean_ctor_get(x_1116, 0);
x_1119 = (uint8_t)((x_1110 << 24) >> 61);
x_1120 = lean_expr_update_forall(x_5, x_1119, x_1112, x_1118);
lean_ctor_set(x_1116, 0, x_1120);
return x_1116;
}
else
{
lean_object* x_1121; lean_object* x_1122; uint8_t x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1121 = lean_ctor_get(x_1116, 0);
x_1122 = lean_ctor_get(x_1116, 1);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_1116);
x_1123 = (uint8_t)((x_1110 << 24) >> 61);
x_1124 = lean_expr_update_forall(x_5, x_1123, x_1112, x_1121);
x_1125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1125, 0, x_1124);
lean_ctor_set(x_1125, 1, x_1122);
return x_1125;
}
}
else
{
uint8_t x_1126; 
lean_dec(x_1112);
lean_free_object(x_5);
lean_dec(x_1109);
lean_dec(x_1108);
lean_dec(x_1107);
x_1126 = !lean_is_exclusive(x_1116);
if (x_1126 == 0)
{
return x_1116;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1127 = lean_ctor_get(x_1116, 0);
x_1128 = lean_ctor_get(x_1116, 1);
lean_inc(x_1128);
lean_inc(x_1127);
lean_dec(x_1116);
x_1129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1129, 0, x_1127);
lean_ctor_set(x_1129, 1, x_1128);
return x_1129;
}
}
}
else
{
uint8_t x_1130; 
lean_free_object(x_5);
lean_dec(x_1109);
lean_dec(x_1108);
lean_dec(x_1107);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1130 = !lean_is_exclusive(x_1111);
if (x_1130 == 0)
{
return x_1111;
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1131 = lean_ctor_get(x_1111, 0);
x_1132 = lean_ctor_get(x_1111, 1);
lean_inc(x_1132);
lean_inc(x_1131);
lean_dec(x_1111);
x_1133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1133, 0, x_1131);
lean_ctor_set(x_1133, 1, x_1132);
return x_1133;
}
}
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; uint64_t x_1137; lean_object* x_1138; 
x_1134 = lean_ctor_get(x_5, 0);
x_1135 = lean_ctor_get(x_5, 1);
x_1136 = lean_ctor_get(x_5, 2);
x_1137 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1136);
lean_inc(x_1135);
lean_inc(x_1134);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1135);
lean_inc(x_1);
x_1138 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1135, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1138) == 0)
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1139 = lean_ctor_get(x_1138, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1138, 1);
lean_inc(x_1140);
lean_dec(x_1138);
x_1141 = lean_unsigned_to_nat(1u);
x_1142 = lean_nat_add(x_6, x_1141);
lean_dec(x_6);
lean_inc(x_1136);
x_1143 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1136, x_1142, x_7, x_8, x_9, x_10, x_11, x_1140);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; uint8_t x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1143, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 lean_ctor_release(x_1143, 1);
 x_1146 = x_1143;
} else {
 lean_dec_ref(x_1143);
 x_1146 = lean_box(0);
}
x_1147 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_1147, 0, x_1134);
lean_ctor_set(x_1147, 1, x_1135);
lean_ctor_set(x_1147, 2, x_1136);
lean_ctor_set_uint64(x_1147, sizeof(void*)*3, x_1137);
x_1148 = (uint8_t)((x_1137 << 24) >> 61);
x_1149 = lean_expr_update_forall(x_1147, x_1148, x_1139, x_1144);
if (lean_is_scalar(x_1146)) {
 x_1150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1150 = x_1146;
}
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_1145);
return x_1150;
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
lean_dec(x_1139);
lean_dec(x_1136);
lean_dec(x_1135);
lean_dec(x_1134);
x_1151 = lean_ctor_get(x_1143, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1143, 1);
lean_inc(x_1152);
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 lean_ctor_release(x_1143, 1);
 x_1153 = x_1143;
} else {
 lean_dec_ref(x_1143);
 x_1153 = lean_box(0);
}
if (lean_is_scalar(x_1153)) {
 x_1154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1154 = x_1153;
}
lean_ctor_set(x_1154, 0, x_1151);
lean_ctor_set(x_1154, 1, x_1152);
return x_1154;
}
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1136);
lean_dec(x_1135);
lean_dec(x_1134);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1155 = lean_ctor_get(x_1138, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1138, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1138)) {
 lean_ctor_release(x_1138, 0);
 lean_ctor_release(x_1138, 1);
 x_1157 = x_1138;
} else {
 lean_dec_ref(x_1138);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1155);
lean_ctor_set(x_1158, 1, x_1156);
return x_1158;
}
}
}
case 8:
{
uint8_t x_1159; 
x_1159 = !lean_is_exclusive(x_5);
if (x_1159 == 0)
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1160 = lean_ctor_get(x_5, 0);
x_1161 = lean_ctor_get(x_5, 1);
x_1162 = lean_ctor_get(x_5, 2);
x_1163 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1161);
lean_inc(x_1);
x_1164 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1161, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1164) == 0)
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1165 = lean_ctor_get(x_1164, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1164, 1);
lean_inc(x_1166);
lean_dec(x_1164);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1162);
lean_inc(x_1);
x_1167 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1162, x_6, x_7, x_8, x_9, x_10, x_11, x_1166);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1167, 1);
lean_inc(x_1169);
lean_dec(x_1167);
x_1170 = lean_unsigned_to_nat(1u);
x_1171 = lean_nat_add(x_6, x_1170);
lean_dec(x_6);
lean_inc(x_1163);
x_1172 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1163, x_1171, x_7, x_8, x_9, x_10, x_11, x_1169);
if (lean_obj_tag(x_1172) == 0)
{
uint8_t x_1173; 
x_1173 = !lean_is_exclusive(x_1172);
if (x_1173 == 0)
{
lean_object* x_1174; lean_object* x_1175; 
x_1174 = lean_ctor_get(x_1172, 0);
x_1175 = lean_expr_update_let(x_5, x_1165, x_1168, x_1174);
lean_ctor_set(x_1172, 0, x_1175);
return x_1172;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1176 = lean_ctor_get(x_1172, 0);
x_1177 = lean_ctor_get(x_1172, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1172);
x_1178 = lean_expr_update_let(x_5, x_1165, x_1168, x_1176);
x_1179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1179, 0, x_1178);
lean_ctor_set(x_1179, 1, x_1177);
return x_1179;
}
}
else
{
uint8_t x_1180; 
lean_dec(x_1168);
lean_dec(x_1165);
lean_free_object(x_5);
lean_dec(x_1163);
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
x_1180 = !lean_is_exclusive(x_1172);
if (x_1180 == 0)
{
return x_1172;
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = lean_ctor_get(x_1172, 0);
x_1182 = lean_ctor_get(x_1172, 1);
lean_inc(x_1182);
lean_inc(x_1181);
lean_dec(x_1172);
x_1183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1183, 0, x_1181);
lean_ctor_set(x_1183, 1, x_1182);
return x_1183;
}
}
}
else
{
uint8_t x_1184; 
lean_dec(x_1165);
lean_free_object(x_5);
lean_dec(x_1163);
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1184 = !lean_is_exclusive(x_1167);
if (x_1184 == 0)
{
return x_1167;
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1185 = lean_ctor_get(x_1167, 0);
x_1186 = lean_ctor_get(x_1167, 1);
lean_inc(x_1186);
lean_inc(x_1185);
lean_dec(x_1167);
x_1187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1187, 0, x_1185);
lean_ctor_set(x_1187, 1, x_1186);
return x_1187;
}
}
}
else
{
uint8_t x_1188; 
lean_free_object(x_5);
lean_dec(x_1163);
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1188 = !lean_is_exclusive(x_1164);
if (x_1188 == 0)
{
return x_1164;
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1189 = lean_ctor_get(x_1164, 0);
x_1190 = lean_ctor_get(x_1164, 1);
lean_inc(x_1190);
lean_inc(x_1189);
lean_dec(x_1164);
x_1191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1191, 0, x_1189);
lean_ctor_set(x_1191, 1, x_1190);
return x_1191;
}
}
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; uint64_t x_1196; lean_object* x_1197; 
x_1192 = lean_ctor_get(x_5, 0);
x_1193 = lean_ctor_get(x_5, 1);
x_1194 = lean_ctor_get(x_5, 2);
x_1195 = lean_ctor_get(x_5, 3);
x_1196 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_1195);
lean_inc(x_1194);
lean_inc(x_1193);
lean_inc(x_1192);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1193);
lean_inc(x_1);
x_1197 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1193, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1197) == 0)
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
x_1198 = lean_ctor_get(x_1197, 0);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_1197, 1);
lean_inc(x_1199);
lean_dec(x_1197);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1194);
lean_inc(x_1);
x_1200 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1194, x_6, x_7, x_8, x_9, x_10, x_11, x_1199);
if (lean_obj_tag(x_1200) == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
lean_dec(x_1200);
x_1203 = lean_unsigned_to_nat(1u);
x_1204 = lean_nat_add(x_6, x_1203);
lean_dec(x_6);
lean_inc(x_1195);
x_1205 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1195, x_1204, x_7, x_8, x_9, x_10, x_11, x_1202);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1206 = lean_ctor_get(x_1205, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1205, 1);
lean_inc(x_1207);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 lean_ctor_release(x_1205, 1);
 x_1208 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1208 = lean_box(0);
}
x_1209 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_1209, 0, x_1192);
lean_ctor_set(x_1209, 1, x_1193);
lean_ctor_set(x_1209, 2, x_1194);
lean_ctor_set(x_1209, 3, x_1195);
lean_ctor_set_uint64(x_1209, sizeof(void*)*4, x_1196);
x_1210 = lean_expr_update_let(x_1209, x_1198, x_1201, x_1206);
if (lean_is_scalar(x_1208)) {
 x_1211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1211 = x_1208;
}
lean_ctor_set(x_1211, 0, x_1210);
lean_ctor_set(x_1211, 1, x_1207);
return x_1211;
}
else
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
x_1212 = lean_ctor_get(x_1205, 0);
lean_inc(x_1212);
x_1213 = lean_ctor_get(x_1205, 1);
lean_inc(x_1213);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 lean_ctor_release(x_1205, 1);
 x_1214 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1214 = lean_box(0);
}
if (lean_is_scalar(x_1214)) {
 x_1215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1215 = x_1214;
}
lean_ctor_set(x_1215, 0, x_1212);
lean_ctor_set(x_1215, 1, x_1213);
return x_1215;
}
}
else
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
lean_dec(x_1198);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1216 = lean_ctor_get(x_1200, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1200, 1);
lean_inc(x_1217);
if (lean_is_exclusive(x_1200)) {
 lean_ctor_release(x_1200, 0);
 lean_ctor_release(x_1200, 1);
 x_1218 = x_1200;
} else {
 lean_dec_ref(x_1200);
 x_1218 = lean_box(0);
}
if (lean_is_scalar(x_1218)) {
 x_1219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1219 = x_1218;
}
lean_ctor_set(x_1219, 0, x_1216);
lean_ctor_set(x_1219, 1, x_1217);
return x_1219;
}
}
else
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1220 = lean_ctor_get(x_1197, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1197, 1);
lean_inc(x_1221);
if (lean_is_exclusive(x_1197)) {
 lean_ctor_release(x_1197, 0);
 lean_ctor_release(x_1197, 1);
 x_1222 = x_1197;
} else {
 lean_dec_ref(x_1197);
 x_1222 = lean_box(0);
}
if (lean_is_scalar(x_1222)) {
 x_1223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1223 = x_1222;
}
lean_ctor_set(x_1223, 0, x_1220);
lean_ctor_set(x_1223, 1, x_1221);
return x_1223;
}
}
}
case 10:
{
uint8_t x_1224; 
x_1224 = !lean_is_exclusive(x_5);
if (x_1224 == 0)
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1225 = lean_ctor_get(x_5, 0);
x_1226 = lean_ctor_get(x_5, 1);
lean_inc(x_1226);
x_1227 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1226, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1227) == 0)
{
uint8_t x_1228; 
x_1228 = !lean_is_exclusive(x_1227);
if (x_1228 == 0)
{
lean_object* x_1229; lean_object* x_1230; 
x_1229 = lean_ctor_get(x_1227, 0);
x_1230 = lean_expr_update_mdata(x_5, x_1229);
lean_ctor_set(x_1227, 0, x_1230);
return x_1227;
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
x_1231 = lean_ctor_get(x_1227, 0);
x_1232 = lean_ctor_get(x_1227, 1);
lean_inc(x_1232);
lean_inc(x_1231);
lean_dec(x_1227);
x_1233 = lean_expr_update_mdata(x_5, x_1231);
x_1234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1234, 0, x_1233);
lean_ctor_set(x_1234, 1, x_1232);
return x_1234;
}
}
else
{
uint8_t x_1235; 
lean_free_object(x_5);
lean_dec(x_1226);
lean_dec(x_1225);
x_1235 = !lean_is_exclusive(x_1227);
if (x_1235 == 0)
{
return x_1227;
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
x_1236 = lean_ctor_get(x_1227, 0);
x_1237 = lean_ctor_get(x_1227, 1);
lean_inc(x_1237);
lean_inc(x_1236);
lean_dec(x_1227);
x_1238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1238, 0, x_1236);
lean_ctor_set(x_1238, 1, x_1237);
return x_1238;
}
}
}
else
{
lean_object* x_1239; lean_object* x_1240; uint64_t x_1241; lean_object* x_1242; 
x_1239 = lean_ctor_get(x_5, 0);
x_1240 = lean_ctor_get(x_5, 1);
x_1241 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_1240);
lean_inc(x_1239);
lean_dec(x_5);
lean_inc(x_1240);
x_1242 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1240, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1242) == 0)
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1243 = lean_ctor_get(x_1242, 0);
lean_inc(x_1243);
x_1244 = lean_ctor_get(x_1242, 1);
lean_inc(x_1244);
if (lean_is_exclusive(x_1242)) {
 lean_ctor_release(x_1242, 0);
 lean_ctor_release(x_1242, 1);
 x_1245 = x_1242;
} else {
 lean_dec_ref(x_1242);
 x_1245 = lean_box(0);
}
x_1246 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_1246, 0, x_1239);
lean_ctor_set(x_1246, 1, x_1240);
lean_ctor_set_uint64(x_1246, sizeof(void*)*2, x_1241);
x_1247 = lean_expr_update_mdata(x_1246, x_1243);
if (lean_is_scalar(x_1245)) {
 x_1248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1248 = x_1245;
}
lean_ctor_set(x_1248, 0, x_1247);
lean_ctor_set(x_1248, 1, x_1244);
return x_1248;
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
lean_dec(x_1240);
lean_dec(x_1239);
x_1249 = lean_ctor_get(x_1242, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1242, 1);
lean_inc(x_1250);
if (lean_is_exclusive(x_1242)) {
 lean_ctor_release(x_1242, 0);
 lean_ctor_release(x_1242, 1);
 x_1251 = x_1242;
} else {
 lean_dec_ref(x_1242);
 x_1251 = lean_box(0);
}
if (lean_is_scalar(x_1251)) {
 x_1252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1252 = x_1251;
}
lean_ctor_set(x_1252, 0, x_1249);
lean_ctor_set(x_1252, 1, x_1250);
return x_1252;
}
}
}
case 11:
{
uint8_t x_1253; 
x_1253 = !lean_is_exclusive(x_5);
if (x_1253 == 0)
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
x_1254 = lean_ctor_get(x_5, 0);
x_1255 = lean_ctor_get(x_5, 1);
x_1256 = lean_ctor_get(x_5, 2);
lean_inc(x_1256);
x_1257 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1256, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1257) == 0)
{
uint8_t x_1258; 
x_1258 = !lean_is_exclusive(x_1257);
if (x_1258 == 0)
{
lean_object* x_1259; lean_object* x_1260; 
x_1259 = lean_ctor_get(x_1257, 0);
x_1260 = lean_expr_update_proj(x_5, x_1259);
lean_ctor_set(x_1257, 0, x_1260);
return x_1257;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1261 = lean_ctor_get(x_1257, 0);
x_1262 = lean_ctor_get(x_1257, 1);
lean_inc(x_1262);
lean_inc(x_1261);
lean_dec(x_1257);
x_1263 = lean_expr_update_proj(x_5, x_1261);
x_1264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1264, 0, x_1263);
lean_ctor_set(x_1264, 1, x_1262);
return x_1264;
}
}
else
{
uint8_t x_1265; 
lean_free_object(x_5);
lean_dec(x_1256);
lean_dec(x_1255);
lean_dec(x_1254);
x_1265 = !lean_is_exclusive(x_1257);
if (x_1265 == 0)
{
return x_1257;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1266 = lean_ctor_get(x_1257, 0);
x_1267 = lean_ctor_get(x_1257, 1);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1257);
x_1268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set(x_1268, 1, x_1267);
return x_1268;
}
}
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; uint64_t x_1272; lean_object* x_1273; 
x_1269 = lean_ctor_get(x_5, 0);
x_1270 = lean_ctor_get(x_5, 1);
x_1271 = lean_ctor_get(x_5, 2);
x_1272 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1271);
lean_inc(x_1270);
lean_inc(x_1269);
lean_dec(x_5);
lean_inc(x_1271);
x_1273 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1271, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1273) == 0)
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1274 = lean_ctor_get(x_1273, 0);
lean_inc(x_1274);
x_1275 = lean_ctor_get(x_1273, 1);
lean_inc(x_1275);
if (lean_is_exclusive(x_1273)) {
 lean_ctor_release(x_1273, 0);
 lean_ctor_release(x_1273, 1);
 x_1276 = x_1273;
} else {
 lean_dec_ref(x_1273);
 x_1276 = lean_box(0);
}
x_1277 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_1277, 0, x_1269);
lean_ctor_set(x_1277, 1, x_1270);
lean_ctor_set(x_1277, 2, x_1271);
lean_ctor_set_uint64(x_1277, sizeof(void*)*3, x_1272);
x_1278 = lean_expr_update_proj(x_1277, x_1274);
if (lean_is_scalar(x_1276)) {
 x_1279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1279 = x_1276;
}
lean_ctor_set(x_1279, 0, x_1278);
lean_ctor_set(x_1279, 1, x_1275);
return x_1279;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1271);
lean_dec(x_1270);
lean_dec(x_1269);
x_1280 = lean_ctor_get(x_1273, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1273, 1);
lean_inc(x_1281);
if (lean_is_exclusive(x_1273)) {
 lean_ctor_release(x_1273, 0);
 lean_ctor_release(x_1273, 1);
 x_1282 = x_1273;
} else {
 lean_dec_ref(x_1273);
 x_1282 = lean_box(0);
}
if (lean_is_scalar(x_1282)) {
 x_1283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1283 = x_1282;
}
lean_ctor_set(x_1283, 0, x_1280);
lean_ctor_set(x_1283, 1, x_1281);
return x_1283;
}
}
}
default: 
{
lean_object* x_1284; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1284, 0, x_5);
lean_ctor_set(x_1284, 1, x_12);
return x_1284;
}
}
}
block_1000:
{
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_14 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_19);
lean_inc(x_1);
x_21 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_20);
x_24 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_expr_update_app(x_5, x_22, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_expr_update_app(x_5, x_22, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_20);
lean_dec(x_19);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_5);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
x_42 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_40);
lean_inc(x_1);
x_43 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_41);
x_46 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set_uint64(x_50, sizeof(void*)*2, x_42);
x_51 = lean_expr_update_app(x_50, x_44, x_47);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_55 = x_46;
} else {
 lean_dec_ref(x_46);
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
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_57 = lean_ctor_get(x_43, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_59 = x_43;
} else {
 lean_dec_ref(x_43);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
case 6:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_dec(x_14);
x_62 = !lean_is_exclusive(x_5);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_5, 0);
x_64 = lean_ctor_get(x_5, 1);
x_65 = lean_ctor_get(x_5, 2);
x_66 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_64);
lean_inc(x_1);
x_67 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_64, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_6, x_70);
lean_dec(x_6);
lean_inc(x_65);
x_72 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_65, x_71, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = (uint8_t)((x_66 << 24) >> 61);
x_76 = lean_expr_update_lambda(x_5, x_75, x_68, x_74);
lean_ctor_set(x_72, 0, x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
x_79 = (uint8_t)((x_66 << 24) >> 61);
x_80 = lean_expr_update_lambda(x_5, x_79, x_68, x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_68);
lean_free_object(x_5);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
x_82 = !lean_is_exclusive(x_72);
if (x_82 == 0)
{
return x_72;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_72, 0);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_72);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_5);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_67);
if (x_86 == 0)
{
return x_67;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_67, 0);
x_88 = lean_ctor_get(x_67, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_67);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint64_t x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_ctor_get(x_5, 1);
x_92 = lean_ctor_get(x_5, 2);
x_93 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_91);
lean_inc(x_1);
x_94 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_91, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_6, x_97);
lean_dec(x_6);
lean_inc(x_92);
x_99 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_92, x_98, x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_91);
lean_ctor_set(x_103, 2, x_92);
lean_ctor_set_uint64(x_103, sizeof(void*)*3, x_93);
x_104 = (uint8_t)((x_93 << 24) >> 61);
x_105 = lean_expr_update_lambda(x_103, x_104, x_95, x_100);
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_102;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
x_107 = lean_ctor_get(x_99, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_109 = x_99;
} else {
 lean_dec_ref(x_99);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_111 = lean_ctor_get(x_94, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_94, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_113 = x_94;
} else {
 lean_dec_ref(x_94);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
case 7:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_14, 1);
lean_inc(x_115);
lean_dec(x_14);
x_116 = !lean_is_exclusive(x_5);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_5, 0);
x_118 = lean_ctor_get(x_5, 1);
x_119 = lean_ctor_get(x_5, 2);
x_120 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_118);
lean_inc(x_1);
x_121 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_118, x_6, x_7, x_8, x_9, x_10, x_11, x_115);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_add(x_6, x_124);
lean_dec(x_6);
lean_inc(x_119);
x_126 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_119, x_125, x_7, x_8, x_9, x_10, x_11, x_123);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = (uint8_t)((x_120 << 24) >> 61);
x_130 = lean_expr_update_forall(x_5, x_129, x_122, x_128);
lean_ctor_set(x_126, 0, x_130);
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_126, 0);
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_126);
x_133 = (uint8_t)((x_120 << 24) >> 61);
x_134 = lean_expr_update_forall(x_5, x_133, x_122, x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_122);
lean_free_object(x_5);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
x_136 = !lean_is_exclusive(x_126);
if (x_136 == 0)
{
return x_126;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_126, 0);
x_138 = lean_ctor_get(x_126, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_126);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_free_object(x_5);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_121);
if (x_140 == 0)
{
return x_121;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_121, 0);
x_142 = lean_ctor_get(x_121, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_121);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint64_t x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_5, 0);
x_145 = lean_ctor_get(x_5, 1);
x_146 = lean_ctor_get(x_5, 2);
x_147 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_145);
lean_inc(x_1);
x_148 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_145, x_6, x_7, x_8, x_9, x_10, x_11, x_115);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_add(x_6, x_151);
lean_dec(x_6);
lean_inc(x_146);
x_153 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_146, x_152, x_7, x_8, x_9, x_10, x_11, x_150);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_157, 0, x_144);
lean_ctor_set(x_157, 1, x_145);
lean_ctor_set(x_157, 2, x_146);
lean_ctor_set_uint64(x_157, sizeof(void*)*3, x_147);
x_158 = (uint8_t)((x_147 << 24) >> 61);
x_159 = lean_expr_update_forall(x_157, x_158, x_149, x_154);
if (lean_is_scalar(x_156)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_156;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_155);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
x_161 = lean_ctor_get(x_153, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_153, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_163 = x_153;
} else {
 lean_dec_ref(x_153);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_165 = lean_ctor_get(x_148, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_148, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_167 = x_148;
} else {
 lean_dec_ref(x_148);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
case 8:
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_14, 1);
lean_inc(x_169);
lean_dec(x_14);
x_170 = !lean_is_exclusive(x_5);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_5, 0);
x_172 = lean_ctor_get(x_5, 1);
x_173 = lean_ctor_get(x_5, 2);
x_174 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_172);
lean_inc(x_1);
x_175 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_172, x_6, x_7, x_8, x_9, x_10, x_11, x_169);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_173);
lean_inc(x_1);
x_178 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_173, x_6, x_7, x_8, x_9, x_10, x_11, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_6, x_181);
lean_dec(x_6);
lean_inc(x_174);
x_183 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_174, x_182, x_7, x_8, x_9, x_10, x_11, x_180);
if (lean_obj_tag(x_183) == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = lean_expr_update_let(x_5, x_176, x_179, x_185);
lean_ctor_set(x_183, 0, x_186);
return x_183;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_183, 0);
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_183);
x_189 = lean_expr_update_let(x_5, x_176, x_179, x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
uint8_t x_191; 
lean_dec(x_179);
lean_dec(x_176);
lean_free_object(x_5);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
x_191 = !lean_is_exclusive(x_183);
if (x_191 == 0)
{
return x_183;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_183, 0);
x_193 = lean_ctor_get(x_183, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_183);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_176);
lean_free_object(x_5);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_178);
if (x_195 == 0)
{
return x_178;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = lean_ctor_get(x_178, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_178);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_free_object(x_5);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_175);
if (x_199 == 0)
{
return x_175;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_175, 0);
x_201 = lean_ctor_get(x_175, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_175);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint64_t x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_5, 0);
x_204 = lean_ctor_get(x_5, 1);
x_205 = lean_ctor_get(x_5, 2);
x_206 = lean_ctor_get(x_5, 3);
x_207 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_204);
lean_inc(x_1);
x_208 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_204, x_6, x_7, x_8, x_9, x_10, x_11, x_169);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_205);
lean_inc(x_1);
x_211 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_205, x_6, x_7, x_8, x_9, x_10, x_11, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_add(x_6, x_214);
lean_dec(x_6);
lean_inc(x_206);
x_216 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_206, x_215, x_7, x_8, x_9, x_10, x_11, x_213);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_219 = x_216;
} else {
 lean_dec_ref(x_216);
 x_219 = lean_box(0);
}
x_220 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_220, 0, x_203);
lean_ctor_set(x_220, 1, x_204);
lean_ctor_set(x_220, 2, x_205);
lean_ctor_set(x_220, 3, x_206);
lean_ctor_set_uint64(x_220, sizeof(void*)*4, x_207);
x_221 = lean_expr_update_let(x_220, x_209, x_212, x_217);
if (lean_is_scalar(x_219)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_219;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_212);
lean_dec(x_209);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
x_223 = lean_ctor_get(x_216, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_216, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_225 = x_216;
} else {
 lean_dec_ref(x_216);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_209);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_227 = lean_ctor_get(x_211, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_211, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_229 = x_211;
} else {
 lean_dec_ref(x_211);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_231 = lean_ctor_get(x_208, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_208, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_233 = x_208;
} else {
 lean_dec_ref(x_208);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
case 10:
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_14, 1);
lean_inc(x_235);
lean_dec(x_14);
x_236 = !lean_is_exclusive(x_5);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_5, 0);
x_238 = lean_ctor_get(x_5, 1);
lean_inc(x_238);
x_239 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_238, x_6, x_7, x_8, x_9, x_10, x_11, x_235);
if (lean_obj_tag(x_239) == 0)
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_239, 0);
x_242 = lean_expr_update_mdata(x_5, x_241);
lean_ctor_set(x_239, 0, x_242);
return x_239;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_239, 0);
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_239);
x_245 = lean_expr_update_mdata(x_5, x_243);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_free_object(x_5);
lean_dec(x_238);
lean_dec(x_237);
x_247 = !lean_is_exclusive(x_239);
if (x_247 == 0)
{
return x_239;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_239, 0);
x_249 = lean_ctor_get(x_239, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_239);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; uint64_t x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_5, 0);
x_252 = lean_ctor_get(x_5, 1);
x_253 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_5);
lean_inc(x_252);
x_254 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_252, x_6, x_7, x_8, x_9, x_10, x_11, x_235);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_258, 0, x_251);
lean_ctor_set(x_258, 1, x_252);
lean_ctor_set_uint64(x_258, sizeof(void*)*2, x_253);
x_259 = lean_expr_update_mdata(x_258, x_255);
if (lean_is_scalar(x_257)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_257;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_256);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_252);
lean_dec(x_251);
x_261 = lean_ctor_get(x_254, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_254, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_263 = x_254;
} else {
 lean_dec_ref(x_254);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
}
case 11:
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_14, 1);
lean_inc(x_265);
lean_dec(x_14);
x_266 = !lean_is_exclusive(x_5);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_5, 0);
x_268 = lean_ctor_get(x_5, 1);
x_269 = lean_ctor_get(x_5, 2);
lean_inc(x_269);
x_270 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_269, x_6, x_7, x_8, x_9, x_10, x_11, x_265);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_270, 0);
x_273 = lean_expr_update_proj(x_5, x_272);
lean_ctor_set(x_270, 0, x_273);
return x_270;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_270, 0);
x_275 = lean_ctor_get(x_270, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_270);
x_276 = lean_expr_update_proj(x_5, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
uint8_t x_278; 
lean_free_object(x_5);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
x_278 = !lean_is_exclusive(x_270);
if (x_278 == 0)
{
return x_270;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_270, 0);
x_280 = lean_ctor_get(x_270, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_270);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint64_t x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_5, 0);
x_283 = lean_ctor_get(x_5, 1);
x_284 = lean_ctor_get(x_5, 2);
x_285 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_5);
lean_inc(x_284);
x_286 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_284, x_6, x_7, x_8, x_9, x_10, x_11, x_265);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
x_290 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_290, 0, x_282);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set_uint64(x_290, sizeof(void*)*3, x_285);
x_291 = lean_expr_update_proj(x_290, x_287);
if (lean_is_scalar(x_289)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_289;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_288);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
x_293 = lean_ctor_get(x_286, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_286, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_295 = x_286;
} else {
 lean_dec_ref(x_286);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
}
default: 
{
uint8_t x_297; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_14);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_14, 0);
lean_dec(x_298);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_14, 1);
lean_inc(x_299);
lean_dec(x_14);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_5);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_301 = lean_ctor_get(x_14, 1);
lean_inc(x_301);
lean_dec(x_14);
x_302 = lean_st_ref_get(x_7, x_301);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_unsigned_to_nat(1u);
x_306 = lean_nat_add(x_303, x_305);
x_307 = lean_st_ref_set(x_7, x_306, x_304);
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_309 = lean_ctor_get(x_307, 1);
x_310 = lean_ctor_get(x_307, 0);
lean_dec(x_310);
x_311 = l_Lean_Occurrences_contains(x_2, x_303);
lean_dec(x_303);
if (x_311 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_312; 
lean_free_object(x_307);
x_312 = !lean_is_exclusive(x_5);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_5, 0);
x_314 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_313);
lean_inc(x_1);
x_315 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_313, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
lean_inc(x_314);
x_318 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_314, x_6, x_7, x_8, x_9, x_10, x_11, x_317);
if (lean_obj_tag(x_318) == 0)
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_318, 0);
x_321 = lean_expr_update_app(x_5, x_316, x_320);
lean_ctor_set(x_318, 0, x_321);
return x_318;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_318, 0);
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_318);
x_324 = lean_expr_update_app(x_5, x_316, x_322);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
uint8_t x_326; 
lean_dec(x_316);
lean_free_object(x_5);
lean_dec(x_314);
lean_dec(x_313);
x_326 = !lean_is_exclusive(x_318);
if (x_326 == 0)
{
return x_318;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_318, 0);
x_328 = lean_ctor_get(x_318, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_318);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
uint8_t x_330; 
lean_free_object(x_5);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_330 = !lean_is_exclusive(x_315);
if (x_330 == 0)
{
return x_315;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_315, 0);
x_332 = lean_ctor_get(x_315, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_315);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; uint64_t x_336; lean_object* x_337; 
x_334 = lean_ctor_get(x_5, 0);
x_335 = lean_ctor_get(x_5, 1);
x_336 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_334);
lean_inc(x_1);
x_337 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_334, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
lean_inc(x_335);
x_340 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_335, x_6, x_7, x_8, x_9, x_10, x_11, x_339);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
x_344 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_344, 0, x_334);
lean_ctor_set(x_344, 1, x_335);
lean_ctor_set_uint64(x_344, sizeof(void*)*2, x_336);
x_345 = lean_expr_update_app(x_344, x_338, x_341);
if (lean_is_scalar(x_343)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_343;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_342);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_338);
lean_dec(x_335);
lean_dec(x_334);
x_347 = lean_ctor_get(x_340, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_340, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_349 = x_340;
} else {
 lean_dec_ref(x_340);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_351 = lean_ctor_get(x_337, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_337, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_353 = x_337;
} else {
 lean_dec_ref(x_337);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
}
case 6:
{
uint8_t x_355; 
lean_free_object(x_307);
x_355 = !lean_is_exclusive(x_5);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint64_t x_359; lean_object* x_360; 
x_356 = lean_ctor_get(x_5, 0);
x_357 = lean_ctor_get(x_5, 1);
x_358 = lean_ctor_get(x_5, 2);
x_359 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_357);
lean_inc(x_1);
x_360 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_357, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_358);
x_364 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_358, x_363, x_7, x_8, x_9, x_10, x_11, x_362);
if (lean_obj_tag(x_364) == 0)
{
uint8_t x_365; 
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; uint8_t x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_364, 0);
x_367 = (uint8_t)((x_359 << 24) >> 61);
x_368 = lean_expr_update_lambda(x_5, x_367, x_361, x_366);
lean_ctor_set(x_364, 0, x_368);
return x_364;
}
else
{
lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; 
x_369 = lean_ctor_get(x_364, 0);
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_364);
x_371 = (uint8_t)((x_359 << 24) >> 61);
x_372 = lean_expr_update_lambda(x_5, x_371, x_361, x_369);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_370);
return x_373;
}
}
else
{
uint8_t x_374; 
lean_dec(x_361);
lean_free_object(x_5);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
x_374 = !lean_is_exclusive(x_364);
if (x_374 == 0)
{
return x_364;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_364, 0);
x_376 = lean_ctor_get(x_364, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_364);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
lean_free_object(x_5);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_378 = !lean_is_exclusive(x_360);
if (x_378 == 0)
{
return x_360;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_360, 0);
x_380 = lean_ctor_get(x_360, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_360);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint64_t x_385; lean_object* x_386; 
x_382 = lean_ctor_get(x_5, 0);
x_383 = lean_ctor_get(x_5, 1);
x_384 = lean_ctor_get(x_5, 2);
x_385 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_384);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_383);
lean_inc(x_1);
x_386 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_383, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_384);
x_390 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_384, x_389, x_7, x_8, x_9, x_10, x_11, x_388);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; lean_object* x_397; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_393 = x_390;
} else {
 lean_dec_ref(x_390);
 x_393 = lean_box(0);
}
x_394 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_394, 0, x_382);
lean_ctor_set(x_394, 1, x_383);
lean_ctor_set(x_394, 2, x_384);
lean_ctor_set_uint64(x_394, sizeof(void*)*3, x_385);
x_395 = (uint8_t)((x_385 << 24) >> 61);
x_396 = lean_expr_update_lambda(x_394, x_395, x_387, x_391);
if (lean_is_scalar(x_393)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_393;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_392);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_387);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
x_398 = lean_ctor_get(x_390, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_390, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_400 = x_390;
} else {
 lean_dec_ref(x_390);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_402 = lean_ctor_get(x_386, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_386, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_404 = x_386;
} else {
 lean_dec_ref(x_386);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_403);
return x_405;
}
}
}
case 7:
{
uint8_t x_406; 
lean_free_object(x_307);
x_406 = !lean_is_exclusive(x_5);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; uint64_t x_410; lean_object* x_411; 
x_407 = lean_ctor_get(x_5, 0);
x_408 = lean_ctor_get(x_5, 1);
x_409 = lean_ctor_get(x_5, 2);
x_410 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_408);
lean_inc(x_1);
x_411 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_408, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_409);
x_415 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_409, x_414, x_7, x_8, x_9, x_10, x_11, x_413);
if (lean_obj_tag(x_415) == 0)
{
uint8_t x_416; 
x_416 = !lean_is_exclusive(x_415);
if (x_416 == 0)
{
lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_415, 0);
x_418 = (uint8_t)((x_410 << 24) >> 61);
x_419 = lean_expr_update_forall(x_5, x_418, x_412, x_417);
lean_ctor_set(x_415, 0, x_419);
return x_415;
}
else
{
lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; 
x_420 = lean_ctor_get(x_415, 0);
x_421 = lean_ctor_get(x_415, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_415);
x_422 = (uint8_t)((x_410 << 24) >> 61);
x_423 = lean_expr_update_forall(x_5, x_422, x_412, x_420);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_421);
return x_424;
}
}
else
{
uint8_t x_425; 
lean_dec(x_412);
lean_free_object(x_5);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
x_425 = !lean_is_exclusive(x_415);
if (x_425 == 0)
{
return x_415;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_415, 0);
x_427 = lean_ctor_get(x_415, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_415);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
else
{
uint8_t x_429; 
lean_free_object(x_5);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_429 = !lean_is_exclusive(x_411);
if (x_429 == 0)
{
return x_411;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_411, 0);
x_431 = lean_ctor_get(x_411, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_411);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; uint64_t x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_5, 0);
x_434 = lean_ctor_get(x_5, 1);
x_435 = lean_ctor_get(x_5, 2);
x_436 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_435);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_434);
lean_inc(x_1);
x_437 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_434, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_440 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_435);
x_441 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_435, x_440, x_7, x_8, x_9, x_10, x_11, x_439);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_444 = x_441;
} else {
 lean_dec_ref(x_441);
 x_444 = lean_box(0);
}
x_445 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_445, 0, x_433);
lean_ctor_set(x_445, 1, x_434);
lean_ctor_set(x_445, 2, x_435);
lean_ctor_set_uint64(x_445, sizeof(void*)*3, x_436);
x_446 = (uint8_t)((x_436 << 24) >> 61);
x_447 = lean_expr_update_forall(x_445, x_446, x_438, x_442);
if (lean_is_scalar(x_444)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_444;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_443);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_438);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_433);
x_449 = lean_ctor_get(x_441, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_441, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_451 = x_441;
} else {
 lean_dec_ref(x_441);
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
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_453 = lean_ctor_get(x_437, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_437, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_455 = x_437;
} else {
 lean_dec_ref(x_437);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 2, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
}
}
case 8:
{
uint8_t x_457; 
lean_free_object(x_307);
x_457 = !lean_is_exclusive(x_5);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_458 = lean_ctor_get(x_5, 0);
x_459 = lean_ctor_get(x_5, 1);
x_460 = lean_ctor_get(x_5, 2);
x_461 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_459);
lean_inc(x_1);
x_462 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_459, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_460);
lean_inc(x_1);
x_465 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_460, x_6, x_7, x_8, x_9, x_10, x_11, x_464);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_461);
x_469 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_461, x_468, x_7, x_8, x_9, x_10, x_11, x_467);
if (lean_obj_tag(x_469) == 0)
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_469);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_ctor_get(x_469, 0);
x_472 = lean_expr_update_let(x_5, x_463, x_466, x_471);
lean_ctor_set(x_469, 0, x_472);
return x_469;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_469, 0);
x_474 = lean_ctor_get(x_469, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_469);
x_475 = lean_expr_update_let(x_5, x_463, x_466, x_473);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_474);
return x_476;
}
}
else
{
uint8_t x_477; 
lean_dec(x_466);
lean_dec(x_463);
lean_free_object(x_5);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
x_477 = !lean_is_exclusive(x_469);
if (x_477 == 0)
{
return x_469;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_469, 0);
x_479 = lean_ctor_get(x_469, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_469);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
else
{
uint8_t x_481; 
lean_dec(x_463);
lean_free_object(x_5);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_481 = !lean_is_exclusive(x_465);
if (x_481 == 0)
{
return x_465;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_465, 0);
x_483 = lean_ctor_get(x_465, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_465);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
uint8_t x_485; 
lean_free_object(x_5);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_485 = !lean_is_exclusive(x_462);
if (x_485 == 0)
{
return x_462;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_462, 0);
x_487 = lean_ctor_get(x_462, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_462);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint64_t x_493; lean_object* x_494; 
x_489 = lean_ctor_get(x_5, 0);
x_490 = lean_ctor_get(x_5, 1);
x_491 = lean_ctor_get(x_5, 2);
x_492 = lean_ctor_get(x_5, 3);
x_493 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_490);
lean_inc(x_1);
x_494 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_490, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_491);
lean_inc(x_1);
x_497 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_491, x_6, x_7, x_8, x_9, x_10, x_11, x_496);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_492);
x_501 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_492, x_500, x_7, x_8, x_9, x_10, x_11, x_499);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_504 = x_501;
} else {
 lean_dec_ref(x_501);
 x_504 = lean_box(0);
}
x_505 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_505, 0, x_489);
lean_ctor_set(x_505, 1, x_490);
lean_ctor_set(x_505, 2, x_491);
lean_ctor_set(x_505, 3, x_492);
lean_ctor_set_uint64(x_505, sizeof(void*)*4, x_493);
x_506 = lean_expr_update_let(x_505, x_495, x_498, x_502);
if (lean_is_scalar(x_504)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_504;
}
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_503);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_498);
lean_dec(x_495);
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
x_508 = lean_ctor_get(x_501, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_501, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_510 = x_501;
} else {
 lean_dec_ref(x_501);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_495);
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_512 = lean_ctor_get(x_497, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_497, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_514 = x_497;
} else {
 lean_dec_ref(x_497);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_516 = lean_ctor_get(x_494, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_494, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_518 = x_494;
} else {
 lean_dec_ref(x_494);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
}
case 10:
{
uint8_t x_520; 
lean_free_object(x_307);
x_520 = !lean_is_exclusive(x_5);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_5, 0);
x_522 = lean_ctor_get(x_5, 1);
lean_inc(x_522);
x_523 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_522, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
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
x_538 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_536, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
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
uint8_t x_549; 
lean_free_object(x_307);
x_549 = !lean_is_exclusive(x_5);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_550 = lean_ctor_get(x_5, 0);
x_551 = lean_ctor_get(x_5, 1);
x_552 = lean_ctor_get(x_5, 2);
lean_inc(x_552);
x_553 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_552, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_553) == 0)
{
uint8_t x_554; 
x_554 = !lean_is_exclusive(x_553);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_553, 0);
x_556 = lean_expr_update_proj(x_5, x_555);
lean_ctor_set(x_553, 0, x_556);
return x_553;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_553, 0);
x_558 = lean_ctor_get(x_553, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_553);
x_559 = lean_expr_update_proj(x_5, x_557);
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_558);
return x_560;
}
}
else
{
uint8_t x_561; 
lean_free_object(x_5);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
x_561 = !lean_is_exclusive(x_553);
if (x_561 == 0)
{
return x_553;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_553, 0);
x_563 = lean_ctor_get(x_553, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_553);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; uint64_t x_568; lean_object* x_569; 
x_565 = lean_ctor_get(x_5, 0);
x_566 = lean_ctor_get(x_5, 1);
x_567 = lean_ctor_get(x_5, 2);
x_568 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_567);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_5);
lean_inc(x_567);
x_569 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_567, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_572 = x_569;
} else {
 lean_dec_ref(x_569);
 x_572 = lean_box(0);
}
x_573 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_573, 0, x_565);
lean_ctor_set(x_573, 1, x_566);
lean_ctor_set(x_573, 2, x_567);
lean_ctor_set_uint64(x_573, sizeof(void*)*3, x_568);
x_574 = lean_expr_update_proj(x_573, x_570);
if (lean_is_scalar(x_572)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_572;
}
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_571);
return x_575;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_567);
lean_dec(x_566);
lean_dec(x_565);
x_576 = lean_ctor_get(x_569, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_569, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_578 = x_569;
} else {
 lean_dec_ref(x_569);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
return x_579;
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
lean_ctor_set(x_307, 0, x_5);
return x_307;
}
}
}
else
{
lean_object* x_580; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_580 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_307, 0, x_580);
return x_307;
}
}
else
{
lean_object* x_581; uint8_t x_582; 
x_581 = lean_ctor_get(x_307, 1);
lean_inc(x_581);
lean_dec(x_307);
x_582 = l_Lean_Occurrences_contains(x_2, x_303);
lean_dec(x_303);
if (x_582 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_583; lean_object* x_584; uint64_t x_585; lean_object* x_586; lean_object* x_587; 
x_583 = lean_ctor_get(x_5, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_5, 1);
lean_inc(x_584);
x_585 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_586 = x_5;
} else {
 lean_dec_ref(x_5);
 x_586 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_583);
lean_inc(x_1);
x_587 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_583, x_6, x_7, x_8, x_9, x_10, x_11, x_581);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
lean_inc(x_584);
x_590 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_584, x_6, x_7, x_8, x_9, x_10, x_11, x_589);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_593 = x_590;
} else {
 lean_dec_ref(x_590);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_594 = lean_alloc_ctor(5, 2, 8);
} else {
 x_594 = x_586;
}
lean_ctor_set(x_594, 0, x_583);
lean_ctor_set(x_594, 1, x_584);
lean_ctor_set_uint64(x_594, sizeof(void*)*2, x_585);
x_595 = lean_expr_update_app(x_594, x_588, x_591);
if (lean_is_scalar(x_593)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_593;
}
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_592);
return x_596;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_588);
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_583);
x_597 = lean_ctor_get(x_590, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_590, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_599 = x_590;
} else {
 lean_dec_ref(x_590);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_583);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_601 = lean_ctor_get(x_587, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_587, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_603 = x_587;
} else {
 lean_dec_ref(x_587);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
return x_604;
}
}
case 6:
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; uint64_t x_608; lean_object* x_609; lean_object* x_610; 
x_605 = lean_ctor_get(x_5, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_5, 1);
lean_inc(x_606);
x_607 = lean_ctor_get(x_5, 2);
lean_inc(x_607);
x_608 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_609 = x_5;
} else {
 lean_dec_ref(x_5);
 x_609 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_606);
lean_inc(x_1);
x_610 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_606, x_6, x_7, x_8, x_9, x_10, x_11, x_581);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_607);
x_614 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_607, x_613, x_7, x_8, x_9, x_10, x_11, x_612);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; lean_object* x_621; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_617 = x_614;
} else {
 lean_dec_ref(x_614);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_618 = lean_alloc_ctor(6, 3, 8);
} else {
 x_618 = x_609;
}
lean_ctor_set(x_618, 0, x_605);
lean_ctor_set(x_618, 1, x_606);
lean_ctor_set(x_618, 2, x_607);
lean_ctor_set_uint64(x_618, sizeof(void*)*3, x_608);
x_619 = (uint8_t)((x_608 << 24) >> 61);
x_620 = lean_expr_update_lambda(x_618, x_619, x_611, x_615);
if (lean_is_scalar(x_617)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_617;
}
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_616);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_611);
lean_dec(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
x_622 = lean_ctor_get(x_614, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_614, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_624 = x_614;
} else {
 lean_dec_ref(x_614);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_623);
return x_625;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_609);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_626 = lean_ctor_get(x_610, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_610, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_628 = x_610;
} else {
 lean_dec_ref(x_610);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
}
case 7:
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; uint64_t x_633; lean_object* x_634; lean_object* x_635; 
x_630 = lean_ctor_get(x_5, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_5, 1);
lean_inc(x_631);
x_632 = lean_ctor_get(x_5, 2);
lean_inc(x_632);
x_633 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_634 = x_5;
} else {
 lean_dec_ref(x_5);
 x_634 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_631);
lean_inc(x_1);
x_635 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_631, x_6, x_7, x_8, x_9, x_10, x_11, x_581);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_632);
x_639 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_632, x_638, x_7, x_8, x_9, x_10, x_11, x_637);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; lean_object* x_646; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_642 = x_639;
} else {
 lean_dec_ref(x_639);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_643 = lean_alloc_ctor(7, 3, 8);
} else {
 x_643 = x_634;
}
lean_ctor_set(x_643, 0, x_630);
lean_ctor_set(x_643, 1, x_631);
lean_ctor_set(x_643, 2, x_632);
lean_ctor_set_uint64(x_643, sizeof(void*)*3, x_633);
x_644 = (uint8_t)((x_633 << 24) >> 61);
x_645 = lean_expr_update_forall(x_643, x_644, x_636, x_640);
if (lean_is_scalar(x_642)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_642;
}
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_641);
return x_646;
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_636);
lean_dec(x_634);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_630);
x_647 = lean_ctor_get(x_639, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_639, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_649 = x_639;
} else {
 lean_dec_ref(x_639);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_650 = x_649;
}
lean_ctor_set(x_650, 0, x_647);
lean_ctor_set(x_650, 1, x_648);
return x_650;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_dec(x_634);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_630);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_651 = lean_ctor_get(x_635, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_635, 1);
lean_inc(x_652);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_653 = x_635;
} else {
 lean_dec_ref(x_635);
 x_653 = lean_box(0);
}
if (lean_is_scalar(x_653)) {
 x_654 = lean_alloc_ctor(1, 2, 0);
} else {
 x_654 = x_653;
}
lean_ctor_set(x_654, 0, x_651);
lean_ctor_set(x_654, 1, x_652);
return x_654;
}
}
case 8:
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint64_t x_659; lean_object* x_660; lean_object* x_661; 
x_655 = lean_ctor_get(x_5, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_5, 1);
lean_inc(x_656);
x_657 = lean_ctor_get(x_5, 2);
lean_inc(x_657);
x_658 = lean_ctor_get(x_5, 3);
lean_inc(x_658);
x_659 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_660 = x_5;
} else {
 lean_dec_ref(x_5);
 x_660 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_656);
lean_inc(x_1);
x_661 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_656, x_6, x_7, x_8, x_9, x_10, x_11, x_581);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_657);
lean_inc(x_1);
x_664 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_657, x_6, x_7, x_8, x_9, x_10, x_11, x_663);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_nat_add(x_6, x_305);
lean_dec(x_6);
lean_inc(x_658);
x_668 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_658, x_667, x_7, x_8, x_9, x_10, x_11, x_666);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_671 = x_668;
} else {
 lean_dec_ref(x_668);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_672 = lean_alloc_ctor(8, 4, 8);
} else {
 x_672 = x_660;
}
lean_ctor_set(x_672, 0, x_655);
lean_ctor_set(x_672, 1, x_656);
lean_ctor_set(x_672, 2, x_657);
lean_ctor_set(x_672, 3, x_658);
lean_ctor_set_uint64(x_672, sizeof(void*)*4, x_659);
x_673 = lean_expr_update_let(x_672, x_662, x_665, x_669);
if (lean_is_scalar(x_671)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_671;
}
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_670);
return x_674;
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_665);
lean_dec(x_662);
lean_dec(x_660);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_655);
x_675 = lean_ctor_get(x_668, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_668, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_677 = x_668;
} else {
 lean_dec_ref(x_668);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(1, 2, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_675);
lean_ctor_set(x_678, 1, x_676);
return x_678;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_662);
lean_dec(x_660);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_679 = lean_ctor_get(x_664, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_664, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_681 = x_664;
} else {
 lean_dec_ref(x_664);
 x_681 = lean_box(0);
}
if (lean_is_scalar(x_681)) {
 x_682 = lean_alloc_ctor(1, 2, 0);
} else {
 x_682 = x_681;
}
lean_ctor_set(x_682, 0, x_679);
lean_ctor_set(x_682, 1, x_680);
return x_682;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_660);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_683 = lean_ctor_get(x_661, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_661, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_685 = x_661;
} else {
 lean_dec_ref(x_661);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_686 = x_685;
}
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set(x_686, 1, x_684);
return x_686;
}
}
case 10:
{
lean_object* x_687; lean_object* x_688; uint64_t x_689; lean_object* x_690; lean_object* x_691; 
x_687 = lean_ctor_get(x_5, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_5, 1);
lean_inc(x_688);
x_689 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_690 = x_5;
} else {
 lean_dec_ref(x_5);
 x_690 = lean_box(0);
}
lean_inc(x_688);
x_691 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_688, x_6, x_7, x_8, x_9, x_10, x_11, x_581);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_694 = x_691;
} else {
 lean_dec_ref(x_691);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_695 = lean_alloc_ctor(10, 2, 8);
} else {
 x_695 = x_690;
}
lean_ctor_set(x_695, 0, x_687);
lean_ctor_set(x_695, 1, x_688);
lean_ctor_set_uint64(x_695, sizeof(void*)*2, x_689);
x_696 = lean_expr_update_mdata(x_695, x_692);
if (lean_is_scalar(x_694)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_694;
}
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_693);
return x_697;
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_690);
lean_dec(x_688);
lean_dec(x_687);
x_698 = lean_ctor_get(x_691, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_691, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_700 = x_691;
} else {
 lean_dec_ref(x_691);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_699);
return x_701;
}
}
case 11:
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; uint64_t x_705; lean_object* x_706; lean_object* x_707; 
x_702 = lean_ctor_get(x_5, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_5, 1);
lean_inc(x_703);
x_704 = lean_ctor_get(x_5, 2);
lean_inc(x_704);
x_705 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_706 = x_5;
} else {
 lean_dec_ref(x_5);
 x_706 = lean_box(0);
}
lean_inc(x_704);
x_707 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_704, x_6, x_7, x_8, x_9, x_10, x_11, x_581);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_710 = x_707;
} else {
 lean_dec_ref(x_707);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_706)) {
 x_711 = lean_alloc_ctor(11, 3, 8);
} else {
 x_711 = x_706;
}
lean_ctor_set(x_711, 0, x_702);
lean_ctor_set(x_711, 1, x_703);
lean_ctor_set(x_711, 2, x_704);
lean_ctor_set_uint64(x_711, sizeof(void*)*3, x_705);
x_712 = lean_expr_update_proj(x_711, x_708);
if (lean_is_scalar(x_710)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_710;
}
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_709);
return x_713;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_706);
lean_dec(x_704);
lean_dec(x_703);
lean_dec(x_702);
x_714 = lean_ctor_get(x_707, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_707, 1);
lean_inc(x_715);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_716 = x_707;
} else {
 lean_dec_ref(x_707);
 x_716 = lean_box(0);
}
if (lean_is_scalar(x_716)) {
 x_717 = lean_alloc_ctor(1, 2, 0);
} else {
 x_717 = x_716;
}
lean_ctor_set(x_717, 0, x_714);
lean_ctor_set(x_717, 1, x_715);
return x_717;
}
}
default: 
{
lean_object* x_718; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_5);
lean_ctor_set(x_718, 1, x_581);
return x_718;
}
}
}
else
{
lean_object* x_719; lean_object* x_720; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_719 = l_Lean_mkBVar(x_6);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_581);
return x_720;
}
}
}
}
else
{
uint8_t x_721; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_721 = !lean_is_exclusive(x_14);
if (x_721 == 0)
{
return x_14;
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_14, 0);
x_723 = lean_ctor_get(x_14, 1);
lean_inc(x_723);
lean_inc(x_722);
lean_dec(x_14);
x_724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
return x_724;
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_725; 
x_725 = !lean_is_exclusive(x_5);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_5, 0);
x_727 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_726);
lean_inc(x_1);
x_728 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_726, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec(x_728);
lean_inc(x_727);
x_731 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_727, x_6, x_7, x_8, x_9, x_10, x_11, x_730);
if (lean_obj_tag(x_731) == 0)
{
uint8_t x_732; 
x_732 = !lean_is_exclusive(x_731);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; 
x_733 = lean_ctor_get(x_731, 0);
x_734 = lean_expr_update_app(x_5, x_729, x_733);
lean_ctor_set(x_731, 0, x_734);
return x_731;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_735 = lean_ctor_get(x_731, 0);
x_736 = lean_ctor_get(x_731, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_731);
x_737 = lean_expr_update_app(x_5, x_729, x_735);
x_738 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_736);
return x_738;
}
}
else
{
uint8_t x_739; 
lean_dec(x_729);
lean_free_object(x_5);
lean_dec(x_727);
lean_dec(x_726);
x_739 = !lean_is_exclusive(x_731);
if (x_739 == 0)
{
return x_731;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_731, 0);
x_741 = lean_ctor_get(x_731, 1);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_731);
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set(x_742, 1, x_741);
return x_742;
}
}
}
else
{
uint8_t x_743; 
lean_free_object(x_5);
lean_dec(x_727);
lean_dec(x_726);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_743 = !lean_is_exclusive(x_728);
if (x_743 == 0)
{
return x_728;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_728, 0);
x_745 = lean_ctor_get(x_728, 1);
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_728);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
return x_746;
}
}
}
else
{
lean_object* x_747; lean_object* x_748; uint64_t x_749; lean_object* x_750; 
x_747 = lean_ctor_get(x_5, 0);
x_748 = lean_ctor_get(x_5, 1);
x_749 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_748);
lean_inc(x_747);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_747);
lean_inc(x_1);
x_750 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_747, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
lean_inc(x_748);
x_753 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_748, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_756 = x_753;
} else {
 lean_dec_ref(x_753);
 x_756 = lean_box(0);
}
x_757 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_757, 0, x_747);
lean_ctor_set(x_757, 1, x_748);
lean_ctor_set_uint64(x_757, sizeof(void*)*2, x_749);
x_758 = lean_expr_update_app(x_757, x_751, x_754);
if (lean_is_scalar(x_756)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_756;
}
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_755);
return x_759;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_751);
lean_dec(x_748);
lean_dec(x_747);
x_760 = lean_ctor_get(x_753, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_753, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_762 = x_753;
} else {
 lean_dec_ref(x_753);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 2, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_760);
lean_ctor_set(x_763, 1, x_761);
return x_763;
}
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_764 = lean_ctor_get(x_750, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_750, 1);
lean_inc(x_765);
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 lean_ctor_release(x_750, 1);
 x_766 = x_750;
} else {
 lean_dec_ref(x_750);
 x_766 = lean_box(0);
}
if (lean_is_scalar(x_766)) {
 x_767 = lean_alloc_ctor(1, 2, 0);
} else {
 x_767 = x_766;
}
lean_ctor_set(x_767, 0, x_764);
lean_ctor_set(x_767, 1, x_765);
return x_767;
}
}
}
case 6:
{
uint8_t x_768; 
x_768 = !lean_is_exclusive(x_5);
if (x_768 == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; uint64_t x_772; lean_object* x_773; 
x_769 = lean_ctor_get(x_5, 0);
x_770 = lean_ctor_get(x_5, 1);
x_771 = lean_ctor_get(x_5, 2);
x_772 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_770);
lean_inc(x_1);
x_773 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_770, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
lean_dec(x_773);
x_776 = lean_unsigned_to_nat(1u);
x_777 = lean_nat_add(x_6, x_776);
lean_dec(x_6);
lean_inc(x_771);
x_778 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_771, x_777, x_7, x_8, x_9, x_10, x_11, x_775);
if (lean_obj_tag(x_778) == 0)
{
uint8_t x_779; 
x_779 = !lean_is_exclusive(x_778);
if (x_779 == 0)
{
lean_object* x_780; uint8_t x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_778, 0);
x_781 = (uint8_t)((x_772 << 24) >> 61);
x_782 = lean_expr_update_lambda(x_5, x_781, x_774, x_780);
lean_ctor_set(x_778, 0, x_782);
return x_778;
}
else
{
lean_object* x_783; lean_object* x_784; uint8_t x_785; lean_object* x_786; lean_object* x_787; 
x_783 = lean_ctor_get(x_778, 0);
x_784 = lean_ctor_get(x_778, 1);
lean_inc(x_784);
lean_inc(x_783);
lean_dec(x_778);
x_785 = (uint8_t)((x_772 << 24) >> 61);
x_786 = lean_expr_update_lambda(x_5, x_785, x_774, x_783);
x_787 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set(x_787, 1, x_784);
return x_787;
}
}
else
{
uint8_t x_788; 
lean_dec(x_774);
lean_free_object(x_5);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_769);
x_788 = !lean_is_exclusive(x_778);
if (x_788 == 0)
{
return x_778;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_ctor_get(x_778, 0);
x_790 = lean_ctor_get(x_778, 1);
lean_inc(x_790);
lean_inc(x_789);
lean_dec(x_778);
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_789);
lean_ctor_set(x_791, 1, x_790);
return x_791;
}
}
}
else
{
uint8_t x_792; 
lean_free_object(x_5);
lean_dec(x_771);
lean_dec(x_770);
lean_dec(x_769);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_792 = !lean_is_exclusive(x_773);
if (x_792 == 0)
{
return x_773;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_793 = lean_ctor_get(x_773, 0);
x_794 = lean_ctor_get(x_773, 1);
lean_inc(x_794);
lean_inc(x_793);
lean_dec(x_773);
x_795 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_795, 0, x_793);
lean_ctor_set(x_795, 1, x_794);
return x_795;
}
}
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; uint64_t x_799; lean_object* x_800; 
x_796 = lean_ctor_get(x_5, 0);
x_797 = lean_ctor_get(x_5, 1);
x_798 = lean_ctor_get(x_5, 2);
x_799 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_798);
lean_inc(x_797);
lean_inc(x_796);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_797);
lean_inc(x_1);
x_800 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_797, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_800, 1);
lean_inc(x_802);
lean_dec(x_800);
x_803 = lean_unsigned_to_nat(1u);
x_804 = lean_nat_add(x_6, x_803);
lean_dec(x_6);
lean_inc(x_798);
x_805 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_798, x_804, x_7, x_8, x_9, x_10, x_11, x_802);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; uint8_t x_810; lean_object* x_811; lean_object* x_812; 
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_808 = x_805;
} else {
 lean_dec_ref(x_805);
 x_808 = lean_box(0);
}
x_809 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_809, 0, x_796);
lean_ctor_set(x_809, 1, x_797);
lean_ctor_set(x_809, 2, x_798);
lean_ctor_set_uint64(x_809, sizeof(void*)*3, x_799);
x_810 = (uint8_t)((x_799 << 24) >> 61);
x_811 = lean_expr_update_lambda(x_809, x_810, x_801, x_806);
if (lean_is_scalar(x_808)) {
 x_812 = lean_alloc_ctor(0, 2, 0);
} else {
 x_812 = x_808;
}
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_807);
return x_812;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_801);
lean_dec(x_798);
lean_dec(x_797);
lean_dec(x_796);
x_813 = lean_ctor_get(x_805, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_805, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_815 = x_805;
} else {
 lean_dec_ref(x_805);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_798);
lean_dec(x_797);
lean_dec(x_796);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_817 = lean_ctor_get(x_800, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_800, 1);
lean_inc(x_818);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 lean_ctor_release(x_800, 1);
 x_819 = x_800;
} else {
 lean_dec_ref(x_800);
 x_819 = lean_box(0);
}
if (lean_is_scalar(x_819)) {
 x_820 = lean_alloc_ctor(1, 2, 0);
} else {
 x_820 = x_819;
}
lean_ctor_set(x_820, 0, x_817);
lean_ctor_set(x_820, 1, x_818);
return x_820;
}
}
}
case 7:
{
uint8_t x_821; 
x_821 = !lean_is_exclusive(x_5);
if (x_821 == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; uint64_t x_825; lean_object* x_826; 
x_822 = lean_ctor_get(x_5, 0);
x_823 = lean_ctor_get(x_5, 1);
x_824 = lean_ctor_get(x_5, 2);
x_825 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_823);
lean_inc(x_1);
x_826 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_823, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_unsigned_to_nat(1u);
x_830 = lean_nat_add(x_6, x_829);
lean_dec(x_6);
lean_inc(x_824);
x_831 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_824, x_830, x_7, x_8, x_9, x_10, x_11, x_828);
if (lean_obj_tag(x_831) == 0)
{
uint8_t x_832; 
x_832 = !lean_is_exclusive(x_831);
if (x_832 == 0)
{
lean_object* x_833; uint8_t x_834; lean_object* x_835; 
x_833 = lean_ctor_get(x_831, 0);
x_834 = (uint8_t)((x_825 << 24) >> 61);
x_835 = lean_expr_update_forall(x_5, x_834, x_827, x_833);
lean_ctor_set(x_831, 0, x_835);
return x_831;
}
else
{
lean_object* x_836; lean_object* x_837; uint8_t x_838; lean_object* x_839; lean_object* x_840; 
x_836 = lean_ctor_get(x_831, 0);
x_837 = lean_ctor_get(x_831, 1);
lean_inc(x_837);
lean_inc(x_836);
lean_dec(x_831);
x_838 = (uint8_t)((x_825 << 24) >> 61);
x_839 = lean_expr_update_forall(x_5, x_838, x_827, x_836);
x_840 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_840, 0, x_839);
lean_ctor_set(x_840, 1, x_837);
return x_840;
}
}
else
{
uint8_t x_841; 
lean_dec(x_827);
lean_free_object(x_5);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
x_841 = !lean_is_exclusive(x_831);
if (x_841 == 0)
{
return x_831;
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_842 = lean_ctor_get(x_831, 0);
x_843 = lean_ctor_get(x_831, 1);
lean_inc(x_843);
lean_inc(x_842);
lean_dec(x_831);
x_844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_844, 0, x_842);
lean_ctor_set(x_844, 1, x_843);
return x_844;
}
}
}
else
{
uint8_t x_845; 
lean_free_object(x_5);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_845 = !lean_is_exclusive(x_826);
if (x_845 == 0)
{
return x_826;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_826, 0);
x_847 = lean_ctor_get(x_826, 1);
lean_inc(x_847);
lean_inc(x_846);
lean_dec(x_826);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_850);
lean_inc(x_1);
x_853 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_850, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
x_856 = lean_unsigned_to_nat(1u);
x_857 = lean_nat_add(x_6, x_856);
lean_dec(x_6);
lean_inc(x_851);
x_858 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_851, x_857, x_7, x_8, x_9, x_10, x_11, x_855);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; uint8_t x_863; lean_object* x_864; lean_object* x_865; 
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_861 = x_858;
} else {
 lean_dec_ref(x_858);
 x_861 = lean_box(0);
}
x_862 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_862, 0, x_849);
lean_ctor_set(x_862, 1, x_850);
lean_ctor_set(x_862, 2, x_851);
lean_ctor_set_uint64(x_862, sizeof(void*)*3, x_852);
x_863 = (uint8_t)((x_852 << 24) >> 61);
x_864 = lean_expr_update_forall(x_862, x_863, x_854, x_859);
if (lean_is_scalar(x_861)) {
 x_865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_865 = x_861;
}
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_860);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_854);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
x_866 = lean_ctor_get(x_858, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_858, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_868 = x_858;
} else {
 lean_dec_ref(x_858);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_866);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_870 = lean_ctor_get(x_853, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_853, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_872 = x_853;
} else {
 lean_dec_ref(x_853);
 x_872 = lean_box(0);
}
if (lean_is_scalar(x_872)) {
 x_873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_873 = x_872;
}
lean_ctor_set(x_873, 0, x_870);
lean_ctor_set(x_873, 1, x_871);
return x_873;
}
}
}
case 8:
{
uint8_t x_874; 
x_874 = !lean_is_exclusive(x_5);
if (x_874 == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_875 = lean_ctor_get(x_5, 0);
x_876 = lean_ctor_get(x_5, 1);
x_877 = lean_ctor_get(x_5, 2);
x_878 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_876);
lean_inc(x_1);
x_879 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_876, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_879, 1);
lean_inc(x_881);
lean_dec(x_879);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_877);
lean_inc(x_1);
x_882 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_877, x_6, x_7, x_8, x_9, x_10, x_11, x_881);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_882, 1);
lean_inc(x_884);
lean_dec(x_882);
x_885 = lean_unsigned_to_nat(1u);
x_886 = lean_nat_add(x_6, x_885);
lean_dec(x_6);
lean_inc(x_878);
x_887 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_878, x_886, x_7, x_8, x_9, x_10, x_11, x_884);
if (lean_obj_tag(x_887) == 0)
{
uint8_t x_888; 
x_888 = !lean_is_exclusive(x_887);
if (x_888 == 0)
{
lean_object* x_889; lean_object* x_890; 
x_889 = lean_ctor_get(x_887, 0);
x_890 = lean_expr_update_let(x_5, x_880, x_883, x_889);
lean_ctor_set(x_887, 0, x_890);
return x_887;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_891 = lean_ctor_get(x_887, 0);
x_892 = lean_ctor_get(x_887, 1);
lean_inc(x_892);
lean_inc(x_891);
lean_dec(x_887);
x_893 = lean_expr_update_let(x_5, x_880, x_883, x_891);
x_894 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_892);
return x_894;
}
}
else
{
uint8_t x_895; 
lean_dec(x_883);
lean_dec(x_880);
lean_free_object(x_5);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_875);
x_895 = !lean_is_exclusive(x_887);
if (x_895 == 0)
{
return x_887;
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_896 = lean_ctor_get(x_887, 0);
x_897 = lean_ctor_get(x_887, 1);
lean_inc(x_897);
lean_inc(x_896);
lean_dec(x_887);
x_898 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_898, 0, x_896);
lean_ctor_set(x_898, 1, x_897);
return x_898;
}
}
}
else
{
uint8_t x_899; 
lean_dec(x_880);
lean_free_object(x_5);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_875);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_899 = !lean_is_exclusive(x_882);
if (x_899 == 0)
{
return x_882;
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_900 = lean_ctor_get(x_882, 0);
x_901 = lean_ctor_get(x_882, 1);
lean_inc(x_901);
lean_inc(x_900);
lean_dec(x_882);
x_902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_902, 0, x_900);
lean_ctor_set(x_902, 1, x_901);
return x_902;
}
}
}
else
{
uint8_t x_903; 
lean_free_object(x_5);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_875);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_903 = !lean_is_exclusive(x_879);
if (x_903 == 0)
{
return x_879;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_904 = lean_ctor_get(x_879, 0);
x_905 = lean_ctor_get(x_879, 1);
lean_inc(x_905);
lean_inc(x_904);
lean_dec(x_879);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_905);
return x_906;
}
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint64_t x_911; lean_object* x_912; 
x_907 = lean_ctor_get(x_5, 0);
x_908 = lean_ctor_get(x_5, 1);
x_909 = lean_ctor_get(x_5, 2);
x_910 = lean_ctor_get(x_5, 3);
x_911 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_910);
lean_inc(x_909);
lean_inc(x_908);
lean_inc(x_907);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_908);
lean_inc(x_1);
x_912 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_908, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_912) == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_909);
lean_inc(x_1);
x_915 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_909, x_6, x_7, x_8, x_9, x_10, x_11, x_914);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
x_918 = lean_unsigned_to_nat(1u);
x_919 = lean_nat_add(x_6, x_918);
lean_dec(x_6);
lean_inc(x_910);
x_920 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_910, x_919, x_7, x_8, x_9, x_10, x_11, x_917);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_923 = x_920;
} else {
 lean_dec_ref(x_920);
 x_923 = lean_box(0);
}
x_924 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_924, 0, x_907);
lean_ctor_set(x_924, 1, x_908);
lean_ctor_set(x_924, 2, x_909);
lean_ctor_set(x_924, 3, x_910);
lean_ctor_set_uint64(x_924, sizeof(void*)*4, x_911);
x_925 = lean_expr_update_let(x_924, x_913, x_916, x_921);
if (lean_is_scalar(x_923)) {
 x_926 = lean_alloc_ctor(0, 2, 0);
} else {
 x_926 = x_923;
}
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_926, 1, x_922);
return x_926;
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_916);
lean_dec(x_913);
lean_dec(x_910);
lean_dec(x_909);
lean_dec(x_908);
lean_dec(x_907);
x_927 = lean_ctor_get(x_920, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_920, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_929 = x_920;
} else {
 lean_dec_ref(x_920);
 x_929 = lean_box(0);
}
if (lean_is_scalar(x_929)) {
 x_930 = lean_alloc_ctor(1, 2, 0);
} else {
 x_930 = x_929;
}
lean_ctor_set(x_930, 0, x_927);
lean_ctor_set(x_930, 1, x_928);
return x_930;
}
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_913);
lean_dec(x_910);
lean_dec(x_909);
lean_dec(x_908);
lean_dec(x_907);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_931 = lean_ctor_get(x_915, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_915, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_933 = x_915;
} else {
 lean_dec_ref(x_915);
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
lean_dec(x_910);
lean_dec(x_909);
lean_dec(x_908);
lean_dec(x_907);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_935 = lean_ctor_get(x_912, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_912, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_912)) {
 lean_ctor_release(x_912, 0);
 lean_ctor_release(x_912, 1);
 x_937 = x_912;
} else {
 lean_dec_ref(x_912);
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
}
case 10:
{
uint8_t x_939; 
x_939 = !lean_is_exclusive(x_5);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_940 = lean_ctor_get(x_5, 0);
x_941 = lean_ctor_get(x_5, 1);
lean_inc(x_941);
x_942 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_941, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_942) == 0)
{
uint8_t x_943; 
x_943 = !lean_is_exclusive(x_942);
if (x_943 == 0)
{
lean_object* x_944; lean_object* x_945; 
x_944 = lean_ctor_get(x_942, 0);
x_945 = lean_expr_update_mdata(x_5, x_944);
lean_ctor_set(x_942, 0, x_945);
return x_942;
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_946 = lean_ctor_get(x_942, 0);
x_947 = lean_ctor_get(x_942, 1);
lean_inc(x_947);
lean_inc(x_946);
lean_dec(x_942);
x_948 = lean_expr_update_mdata(x_5, x_946);
x_949 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_949, 0, x_948);
lean_ctor_set(x_949, 1, x_947);
return x_949;
}
}
else
{
uint8_t x_950; 
lean_free_object(x_5);
lean_dec(x_941);
lean_dec(x_940);
x_950 = !lean_is_exclusive(x_942);
if (x_950 == 0)
{
return x_942;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_942, 0);
x_952 = lean_ctor_get(x_942, 1);
lean_inc(x_952);
lean_inc(x_951);
lean_dec(x_942);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
return x_953;
}
}
}
else
{
lean_object* x_954; lean_object* x_955; uint64_t x_956; lean_object* x_957; 
x_954 = lean_ctor_get(x_5, 0);
x_955 = lean_ctor_get(x_5, 1);
x_956 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_955);
lean_inc(x_954);
lean_dec(x_5);
lean_inc(x_955);
x_957 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_955, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_960 = x_957;
} else {
 lean_dec_ref(x_957);
 x_960 = lean_box(0);
}
x_961 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_961, 0, x_954);
lean_ctor_set(x_961, 1, x_955);
lean_ctor_set_uint64(x_961, sizeof(void*)*2, x_956);
x_962 = lean_expr_update_mdata(x_961, x_958);
if (lean_is_scalar(x_960)) {
 x_963 = lean_alloc_ctor(0, 2, 0);
} else {
 x_963 = x_960;
}
lean_ctor_set(x_963, 0, x_962);
lean_ctor_set(x_963, 1, x_959);
return x_963;
}
else
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
lean_dec(x_955);
lean_dec(x_954);
x_964 = lean_ctor_get(x_957, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_957, 1);
lean_inc(x_965);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_966 = x_957;
} else {
 lean_dec_ref(x_957);
 x_966 = lean_box(0);
}
if (lean_is_scalar(x_966)) {
 x_967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_967 = x_966;
}
lean_ctor_set(x_967, 0, x_964);
lean_ctor_set(x_967, 1, x_965);
return x_967;
}
}
}
case 11:
{
uint8_t x_968; 
x_968 = !lean_is_exclusive(x_5);
if (x_968 == 0)
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_969 = lean_ctor_get(x_5, 0);
x_970 = lean_ctor_get(x_5, 1);
x_971 = lean_ctor_get(x_5, 2);
lean_inc(x_971);
x_972 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_971, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_972) == 0)
{
uint8_t x_973; 
x_973 = !lean_is_exclusive(x_972);
if (x_973 == 0)
{
lean_object* x_974; lean_object* x_975; 
x_974 = lean_ctor_get(x_972, 0);
x_975 = lean_expr_update_proj(x_5, x_974);
lean_ctor_set(x_972, 0, x_975);
return x_972;
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_976 = lean_ctor_get(x_972, 0);
x_977 = lean_ctor_get(x_972, 1);
lean_inc(x_977);
lean_inc(x_976);
lean_dec(x_972);
x_978 = lean_expr_update_proj(x_5, x_976);
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_978);
lean_ctor_set(x_979, 1, x_977);
return x_979;
}
}
else
{
uint8_t x_980; 
lean_free_object(x_5);
lean_dec(x_971);
lean_dec(x_970);
lean_dec(x_969);
x_980 = !lean_is_exclusive(x_972);
if (x_980 == 0)
{
return x_972;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_972, 0);
x_982 = lean_ctor_get(x_972, 1);
lean_inc(x_982);
lean_inc(x_981);
lean_dec(x_972);
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_981);
lean_ctor_set(x_983, 1, x_982);
return x_983;
}
}
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; uint64_t x_987; lean_object* x_988; 
x_984 = lean_ctor_get(x_5, 0);
x_985 = lean_ctor_get(x_5, 1);
x_986 = lean_ctor_get(x_5, 2);
x_987 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_986);
lean_inc(x_985);
lean_inc(x_984);
lean_dec(x_5);
lean_inc(x_986);
x_988 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_986, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_988, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_991 = x_988;
} else {
 lean_dec_ref(x_988);
 x_991 = lean_box(0);
}
x_992 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_992, 0, x_984);
lean_ctor_set(x_992, 1, x_985);
lean_ctor_set(x_992, 2, x_986);
lean_ctor_set_uint64(x_992, sizeof(void*)*3, x_987);
x_993 = lean_expr_update_proj(x_992, x_989);
if (lean_is_scalar(x_991)) {
 x_994 = lean_alloc_ctor(0, 2, 0);
} else {
 x_994 = x_991;
}
lean_ctor_set(x_994, 0, x_993);
lean_ctor_set(x_994, 1, x_990);
return x_994;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_986);
lean_dec(x_985);
lean_dec(x_984);
x_995 = lean_ctor_get(x_988, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_988, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_997 = x_988;
} else {
 lean_dec_ref(x_988);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_998 = x_997;
}
lean_ctor_set(x_998, 0, x_995);
lean_ctor_set(x_998, 1, x_996);
return x_998;
}
}
}
default: 
{
lean_object* x_999; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_999, 0, x_5);
lean_ctor_set(x_999, 1, x_12);
return x_999;
}
}
}
}
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
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1___boxed), 6, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg___lambda__1___boxed), 8, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__6___spec__2___rarg), 7, 2);
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
