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
lean_object* l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_kabstract_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___closed__3;
lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_15__runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___closed__2;
lean_object* l_Lean_Meta_kabstract___rarg___closed__1;
lean_object* l_Lean_Meta_kabstract___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit_match__1(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_237 = lean_st_ref_get(x_7, x_8);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 3);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_ctor_get_uint8(x_239, sizeof(void*)*1);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = 0;
x_10 = x_242;
x_11 = x_241;
goto block_236;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_dec(x_237);
x_244 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_245 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_244, x_4, x_5, x_6, x_7, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_unbox(x_246);
lean_dec(x_246);
x_10 = x_248;
x_11 = x_247;
goto block_236;
}
block_236:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 3);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_61; 
x_24 = 0;
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_24);
x_25 = lean_st_ref_set(x_7, x_18, x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_62);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_64, 0, x_1);
lean_closure_set(x_64, 1, x_2);
lean_closure_set(x_64, 2, x_62);
x_65 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_66 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_65, x_64, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_get(x_7, x_67);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_take(x_7, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 3);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_16);
x_77 = lean_st_ref_set(x_7, x_71, x_73);
lean_dec(x_7);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_62);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_62);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_72, 0);
lean_inc(x_82);
lean_dec(x_72);
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_16);
lean_ctor_set(x_71, 3, x_83);
x_84 = lean_st_ref_set(x_7, x_71, x_73);
lean_dec(x_7);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_62);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_71, 0);
x_89 = lean_ctor_get(x_71, 1);
x_90 = lean_ctor_get(x_71, 2);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_71);
x_91 = lean_ctor_get(x_72, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_92 = x_72;
} else {
 lean_dec_ref(x_72);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 1, 1);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_16);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_89);
lean_ctor_set(x_94, 2, x_90);
lean_ctor_set(x_94, 3, x_93);
x_95 = lean_st_ref_set(x_7, x_94, x_73);
lean_dec(x_7);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_62);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_61, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_61, 1);
lean_inc(x_100);
lean_dec(x_61);
x_27 = x_99;
x_28 = x_100;
goto block_60;
}
block_60:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_st_ref_get(x_7, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 3);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_16);
x_38 = lean_st_ref_set(x_7, x_32, x_34);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_27);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_16);
lean_ctor_set(x_32, 3, x_44);
x_45 = lean_st_ref_set(x_7, x_32, x_34);
lean_dec(x_7);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_27);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
x_51 = lean_ctor_get(x_32, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_52 = lean_ctor_get(x_33, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_53 = x_33;
} else {
 lean_dec_ref(x_33);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_16);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_st_ref_set(x_7, x_55, x_34);
lean_dec(x_7);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_27);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_127; 
x_101 = lean_ctor_get(x_19, 0);
lean_inc(x_101);
lean_dec(x_19);
x_102 = 0;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
lean_ctor_set(x_18, 3, x_103);
x_104 = lean_st_ref_set(x_7, x_18, x_20);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_127 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_128);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_130, 0, x_1);
lean_closure_set(x_130, 1, x_2);
lean_closure_set(x_130, 2, x_128);
x_131 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_132 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_131, x_130, x_4, x_5, x_6, x_7, x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_get(x_7, x_133);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_st_ref_take(x_7, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 2);
lean_inc(x_142);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 x_143 = x_137;
} else {
 lean_dec_ref(x_137);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_145 = x_138;
} else {
 lean_dec_ref(x_138);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 1, 1);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 4, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_141);
lean_ctor_set(x_147, 2, x_142);
lean_ctor_set(x_147, 3, x_146);
x_148 = lean_st_ref_set(x_7, x_147, x_139);
lean_dec(x_7);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_128);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_ctor_get(x_127, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_127, 1);
lean_inc(x_153);
lean_dec(x_127);
x_106 = x_152;
x_107 = x_153;
goto block_126;
}
block_126:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_108 = lean_st_ref_get(x_7, x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_st_ref_take(x_7, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 2);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 1, 1);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 4, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_115);
lean_ctor_set(x_121, 2, x_116);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_7, x_121, x_113);
lean_dec(x_7);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
 lean_ctor_set_tag(x_125, 1);
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_185; 
x_154 = lean_ctor_get(x_18, 0);
x_155 = lean_ctor_get(x_18, 1);
x_156 = lean_ctor_get(x_18, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_18);
x_157 = lean_ctor_get(x_19, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_158 = x_19;
} else {
 lean_dec_ref(x_19);
 x_158 = lean_box(0);
}
x_159 = 0;
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 1, 1);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_159);
x_161 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_160);
x_162 = lean_st_ref_set(x_7, x_161, x_20);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_185 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_163);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_186);
x_188 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_188, 0, x_1);
lean_closure_set(x_188, 1, x_2);
lean_closure_set(x_188, 2, x_186);
x_189 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_190 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_189, x_188, x_4, x_5, x_6, x_7, x_187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_st_ref_get(x_7, x_191);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_st_ref_take(x_7, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 3);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 2);
lean_inc(x_200);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_201 = x_195;
} else {
 lean_dec_ref(x_195);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_196, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_203 = x_196;
} else {
 lean_dec_ref(x_196);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 1, 1);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(0, 4, 0);
} else {
 x_205 = x_201;
}
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_199);
lean_ctor_set(x_205, 2, x_200);
lean_ctor_set(x_205, 3, x_204);
x_206 = lean_st_ref_set(x_7, x_205, x_197);
lean_dec(x_7);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_186);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_185, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_185, 1);
lean_inc(x_211);
lean_dec(x_185);
x_164 = x_210;
x_165 = x_211;
goto block_184;
}
block_184:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_166 = lean_st_ref_get(x_7, x_165);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_st_ref_take(x_7, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 2);
lean_inc(x_174);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 x_175 = x_169;
} else {
 lean_dec_ref(x_169);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_177 = x_170;
} else {
 lean_dec_ref(x_170);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 1, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_175)) {
 x_179 = lean_alloc_ctor(0, 4, 0);
} else {
 x_179 = x_175;
}
lean_ctor_set(x_179, 0, x_172);
lean_ctor_set(x_179, 1, x_173);
lean_ctor_set(x_179, 2, x_174);
lean_ctor_set(x_179, 3, x_178);
x_180 = lean_st_ref_set(x_7, x_179, x_171);
lean_dec(x_7);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
 lean_ctor_set_tag(x_183, 1);
}
lean_ctor_set(x_183, 0, x_164);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_6, 3);
lean_inc(x_212);
x_213 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_7, x_11);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_216 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_217);
x_219 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_219, 0, x_1);
lean_closure_set(x_219, 1, x_2);
lean_closure_set(x_219, 2, x_217);
x_220 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_221 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_220, x_219, x_4, x_5, x_6, x_7, x_218);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_214, x_220, x_212, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_223, 0);
lean_dec(x_225);
lean_ctor_set(x_223, 0, x_217);
return x_223;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_217);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec(x_2);
lean_dec(x_1);
x_228 = lean_ctor_get(x_216, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_216, 1);
lean_inc(x_229);
lean_dec(x_216);
x_230 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_231 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_214, x_230, x_212, x_4, x_5, x_6, x_7, x_229);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_231, 0);
lean_dec(x_233);
lean_ctor_set_tag(x_231, 1);
lean_ctor_set(x_231, 0, x_228);
return x_231;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_228);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
}
}
}
lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_550; 
x_550 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_550 == 0)
{
lean_object* x_551; uint8_t x_552; 
x_551 = l_Lean_Expr_toHeadIndex___main(x_5);
x_552 = l_Lean_HeadIndex_HeadIndex_beq(x_551, x_3);
lean_dec(x_551);
if (x_552 == 0)
{
uint8_t x_553; 
x_553 = 1;
x_13 = x_553;
goto block_549;
}
else
{
lean_object* x_554; lean_object* x_555; uint8_t x_556; 
x_554 = lean_unsigned_to_nat(0u);
x_555 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_5, x_554);
x_556 = lean_nat_dec_eq(x_555, x_4);
lean_dec(x_555);
if (x_556 == 0)
{
uint8_t x_557; 
x_557 = 1;
x_13 = x_557;
goto block_549;
}
else
{
uint8_t x_558; 
x_558 = 0;
x_13 = x_558;
goto block_549;
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_5, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_5, 1);
lean_inc(x_560);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_561 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_559, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_560, x_6, x_7, x_8, x_9, x_10, x_11, x_563);
if (lean_obj_tag(x_564) == 0)
{
uint8_t x_565; 
x_565 = !lean_is_exclusive(x_564);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; 
x_566 = lean_ctor_get(x_564, 0);
x_567 = lean_expr_update_app(x_5, x_562, x_566);
lean_ctor_set(x_564, 0, x_567);
return x_564;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_568 = lean_ctor_get(x_564, 0);
x_569 = lean_ctor_get(x_564, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_564);
x_570 = lean_expr_update_app(x_5, x_562, x_568);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
return x_571;
}
}
else
{
uint8_t x_572; 
lean_dec(x_562);
lean_dec(x_5);
x_572 = !lean_is_exclusive(x_564);
if (x_572 == 0)
{
return x_564;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_564, 0);
x_574 = lean_ctor_get(x_564, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_564);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
}
else
{
uint8_t x_576; 
lean_dec(x_560);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_576 = !lean_is_exclusive(x_561);
if (x_576 == 0)
{
return x_561;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_561, 0);
x_578 = lean_ctor_get(x_561, 1);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_561);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
return x_579;
}
}
}
case 6:
{
lean_object* x_580; lean_object* x_581; uint64_t x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_5, 1);
lean_inc(x_580);
x_581 = lean_ctor_get(x_5, 2);
lean_inc(x_581);
x_582 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_583 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_580, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
x_586 = lean_unsigned_to_nat(1u);
x_587 = lean_nat_add(x_6, x_586);
lean_dec(x_6);
x_588 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_581, x_587, x_7, x_8, x_9, x_10, x_11, x_585);
if (lean_obj_tag(x_588) == 0)
{
uint8_t x_589; 
x_589 = !lean_is_exclusive(x_588);
if (x_589 == 0)
{
lean_object* x_590; uint8_t x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_588, 0);
x_591 = (uint8_t)((x_582 << 24) >> 61);
x_592 = lean_expr_update_lambda(x_5, x_591, x_584, x_590);
lean_ctor_set(x_588, 0, x_592);
return x_588;
}
else
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; 
x_593 = lean_ctor_get(x_588, 0);
x_594 = lean_ctor_get(x_588, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_588);
x_595 = (uint8_t)((x_582 << 24) >> 61);
x_596 = lean_expr_update_lambda(x_5, x_595, x_584, x_593);
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_594);
return x_597;
}
}
else
{
uint8_t x_598; 
lean_dec(x_584);
lean_dec(x_5);
x_598 = !lean_is_exclusive(x_588);
if (x_598 == 0)
{
return x_588;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_588, 0);
x_600 = lean_ctor_get(x_588, 1);
lean_inc(x_600);
lean_inc(x_599);
lean_dec(x_588);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_600);
return x_601;
}
}
}
else
{
uint8_t x_602; 
lean_dec(x_581);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_602 = !lean_is_exclusive(x_583);
if (x_602 == 0)
{
return x_583;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_583, 0);
x_604 = lean_ctor_get(x_583, 1);
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_583);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
return x_605;
}
}
}
case 7:
{
lean_object* x_606; lean_object* x_607; uint64_t x_608; lean_object* x_609; 
x_606 = lean_ctor_get(x_5, 1);
lean_inc(x_606);
x_607 = lean_ctor_get(x_5, 2);
lean_inc(x_607);
x_608 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_609 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_606, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_unsigned_to_nat(1u);
x_613 = lean_nat_add(x_6, x_612);
lean_dec(x_6);
x_614 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_607, x_613, x_7, x_8, x_9, x_10, x_11, x_611);
if (lean_obj_tag(x_614) == 0)
{
uint8_t x_615; 
x_615 = !lean_is_exclusive(x_614);
if (x_615 == 0)
{
lean_object* x_616; uint8_t x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_614, 0);
x_617 = (uint8_t)((x_608 << 24) >> 61);
x_618 = lean_expr_update_forall(x_5, x_617, x_610, x_616);
lean_ctor_set(x_614, 0, x_618);
return x_614;
}
else
{
lean_object* x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; lean_object* x_623; 
x_619 = lean_ctor_get(x_614, 0);
x_620 = lean_ctor_get(x_614, 1);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_614);
x_621 = (uint8_t)((x_608 << 24) >> 61);
x_622 = lean_expr_update_forall(x_5, x_621, x_610, x_619);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_620);
return x_623;
}
}
else
{
uint8_t x_624; 
lean_dec(x_610);
lean_dec(x_5);
x_624 = !lean_is_exclusive(x_614);
if (x_624 == 0)
{
return x_614;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_614, 0);
x_626 = lean_ctor_get(x_614, 1);
lean_inc(x_626);
lean_inc(x_625);
lean_dec(x_614);
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_625);
lean_ctor_set(x_627, 1, x_626);
return x_627;
}
}
}
else
{
uint8_t x_628; 
lean_dec(x_607);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_628 = !lean_is_exclusive(x_609);
if (x_628 == 0)
{
return x_609;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_609, 0);
x_630 = lean_ctor_get(x_609, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_609);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
case 8:
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_632 = lean_ctor_get(x_5, 1);
lean_inc(x_632);
x_633 = lean_ctor_get(x_5, 2);
lean_inc(x_633);
x_634 = lean_ctor_get(x_5, 3);
lean_inc(x_634);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_635 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_632, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_638 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_633, x_6, x_7, x_8, x_9, x_10, x_11, x_637);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = lean_unsigned_to_nat(1u);
x_642 = lean_nat_add(x_6, x_641);
lean_dec(x_6);
x_643 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_634, x_642, x_7, x_8, x_9, x_10, x_11, x_640);
if (lean_obj_tag(x_643) == 0)
{
uint8_t x_644; 
x_644 = !lean_is_exclusive(x_643);
if (x_644 == 0)
{
lean_object* x_645; lean_object* x_646; 
x_645 = lean_ctor_get(x_643, 0);
x_646 = lean_expr_update_let(x_5, x_636, x_639, x_645);
lean_ctor_set(x_643, 0, x_646);
return x_643;
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_647 = lean_ctor_get(x_643, 0);
x_648 = lean_ctor_get(x_643, 1);
lean_inc(x_648);
lean_inc(x_647);
lean_dec(x_643);
x_649 = lean_expr_update_let(x_5, x_636, x_639, x_647);
x_650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_650, 0, x_649);
lean_ctor_set(x_650, 1, x_648);
return x_650;
}
}
else
{
uint8_t x_651; 
lean_dec(x_639);
lean_dec(x_636);
lean_dec(x_5);
x_651 = !lean_is_exclusive(x_643);
if (x_651 == 0)
{
return x_643;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_643, 0);
x_653 = lean_ctor_get(x_643, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_643);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
else
{
uint8_t x_655; 
lean_dec(x_636);
lean_dec(x_634);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_655 = !lean_is_exclusive(x_638);
if (x_655 == 0)
{
return x_638;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_638, 0);
x_657 = lean_ctor_get(x_638, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_638);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_656);
lean_ctor_set(x_658, 1, x_657);
return x_658;
}
}
}
else
{
uint8_t x_659; 
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_659 = !lean_is_exclusive(x_635);
if (x_659 == 0)
{
return x_635;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; 
x_660 = lean_ctor_get(x_635, 0);
x_661 = lean_ctor_get(x_635, 1);
lean_inc(x_661);
lean_inc(x_660);
lean_dec(x_635);
x_662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_662, 0, x_660);
lean_ctor_set(x_662, 1, x_661);
return x_662;
}
}
}
case 10:
{
lean_object* x_663; lean_object* x_664; 
x_663 = lean_ctor_get(x_5, 1);
lean_inc(x_663);
x_664 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_663, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_664) == 0)
{
uint8_t x_665; 
x_665 = !lean_is_exclusive(x_664);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; 
x_666 = lean_ctor_get(x_664, 0);
x_667 = lean_expr_update_mdata(x_5, x_666);
lean_ctor_set(x_664, 0, x_667);
return x_664;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_668 = lean_ctor_get(x_664, 0);
x_669 = lean_ctor_get(x_664, 1);
lean_inc(x_669);
lean_inc(x_668);
lean_dec(x_664);
x_670 = lean_expr_update_mdata(x_5, x_668);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_669);
return x_671;
}
}
else
{
uint8_t x_672; 
lean_dec(x_5);
x_672 = !lean_is_exclusive(x_664);
if (x_672 == 0)
{
return x_664;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_664, 0);
x_674 = lean_ctor_get(x_664, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_664);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
case 11:
{
lean_object* x_676; lean_object* x_677; 
x_676 = lean_ctor_get(x_5, 2);
lean_inc(x_676);
x_677 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_676, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_677) == 0)
{
uint8_t x_678; 
x_678 = !lean_is_exclusive(x_677);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_677, 0);
x_680 = lean_expr_update_proj(x_5, x_679);
lean_ctor_set(x_677, 0, x_680);
return x_677;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_681 = lean_ctor_get(x_677, 0);
x_682 = lean_ctor_get(x_677, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_677);
x_683 = lean_expr_update_proj(x_5, x_681);
x_684 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_682);
return x_684;
}
}
else
{
uint8_t x_685; 
lean_dec(x_5);
x_685 = !lean_is_exclusive(x_677);
if (x_685 == 0)
{
return x_677;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_677, 0);
x_687 = lean_ctor_get(x_677, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_677);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
return x_688;
}
}
}
default: 
{
lean_object* x_689; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_5);
lean_ctor_set(x_689, 1, x_12);
return x_689;
}
}
}
block_549:
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_expr_update_app(x_5, x_21, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_expr_update_app(x_5, x_21, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_43 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_6, x_46);
lean_dec(x_6);
x_48 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_41, x_47, x_7, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = (uint8_t)((x_42 << 24) >> 61);
x_52 = lean_expr_update_lambda(x_5, x_51, x_44, x_50);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = (uint8_t)((x_42 << 24) >> 61);
x_56 = lean_expr_update_lambda(x_5, x_55, x_44, x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_44);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_43);
if (x_62 == 0)
{
return x_43;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
case 7:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_14, 1);
lean_inc(x_66);
lean_dec(x_14);
x_67 = lean_ctor_get(x_5, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_70 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_67, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_6, x_73);
lean_dec(x_6);
x_75 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_68, x_74, x_7, x_8, x_9, x_10, x_11, x_72);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = (uint8_t)((x_69 << 24) >> 61);
x_79 = lean_expr_update_forall(x_5, x_78, x_71, x_77);
lean_ctor_set(x_75, 0, x_79);
return x_75;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_75, 0);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_75);
x_82 = (uint8_t)((x_69 << 24) >> 61);
x_83 = lean_expr_update_forall(x_5, x_82, x_71, x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_75);
if (x_85 == 0)
{
return x_75;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_75, 0);
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_75);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_70);
if (x_89 == 0)
{
return x_70;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_70, 0);
x_91 = lean_ctor_get(x_70, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_70);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
case 8:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_14, 1);
lean_inc(x_93);
lean_dec(x_14);
x_94 = lean_ctor_get(x_5, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_5, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_5, 3);
lean_inc(x_96);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_97 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_94, x_6, x_7, x_8, x_9, x_10, x_11, x_93);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_100 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_95, x_6, x_7, x_8, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_6, x_103);
lean_dec(x_6);
x_105 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_96, x_104, x_7, x_8, x_9, x_10, x_11, x_102);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_expr_update_let(x_5, x_98, x_101, x_107);
lean_ctor_set(x_105, 0, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_105);
x_111 = lean_expr_update_let(x_5, x_98, x_101, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_5);
x_113 = !lean_is_exclusive(x_105);
if (x_113 == 0)
{
return x_105;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_105, 0);
x_115 = lean_ctor_get(x_105, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_105);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_100);
if (x_117 == 0)
{
return x_100;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_100, 0);
x_119 = lean_ctor_get(x_100, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_100);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_97);
if (x_121 == 0)
{
return x_97;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_97, 0);
x_123 = lean_ctor_get(x_97, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_97);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
case 10:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_14, 1);
lean_inc(x_125);
lean_dec(x_14);
x_126 = lean_ctor_get(x_5, 1);
lean_inc(x_126);
x_127 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_126, x_6, x_7, x_8, x_9, x_10, x_11, x_125);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_expr_update_mdata(x_5, x_129);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_127, 0);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_127);
x_133 = lean_expr_update_mdata(x_5, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_5);
x_135 = !lean_is_exclusive(x_127);
if (x_135 == 0)
{
return x_127;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_127, 0);
x_137 = lean_ctor_get(x_127, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_127);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
case 11:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_14, 1);
lean_inc(x_139);
lean_dec(x_14);
x_140 = lean_ctor_get(x_5, 2);
lean_inc(x_140);
x_141 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_140, x_6, x_7, x_8, x_9, x_10, x_11, x_139);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_expr_update_proj(x_5, x_143);
lean_ctor_set(x_141, 0, x_144);
return x_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_141, 0);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_141);
x_147 = lean_expr_update_proj(x_5, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
uint8_t x_149; 
lean_dec(x_5);
x_149 = !lean_is_exclusive(x_141);
if (x_149 == 0)
{
return x_141;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_141, 0);
x_151 = lean_ctor_get(x_141, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_141);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
default: 
{
uint8_t x_153; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_14);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_14, 0);
lean_dec(x_154);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_14, 1);
lean_inc(x_155);
lean_dec(x_14);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_5);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_157 = lean_ctor_get(x_14, 1);
lean_inc(x_157);
lean_dec(x_14);
x_158 = lean_st_ref_get(x_7, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_add(x_159, x_161);
x_163 = lean_st_ref_set(x_7, x_162, x_160);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = lean_ctor_get(x_163, 1);
x_166 = lean_ctor_get(x_163, 0);
lean_dec(x_166);
x_167 = l_Lean_Occurrences_contains(x_2, x_159);
lean_dec(x_159);
if (x_167 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_free_object(x_163);
x_168 = lean_ctor_get(x_5, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_5, 1);
lean_inc(x_169);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_170 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_168, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_169, x_6, x_7, x_8, x_9, x_10, x_11, x_172);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_expr_update_app(x_5, x_171, x_175);
lean_ctor_set(x_173, 0, x_176);
return x_173;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_173, 0);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_173);
x_179 = lean_expr_update_app(x_5, x_171, x_177);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
uint8_t x_181; 
lean_dec(x_171);
lean_dec(x_5);
x_181 = !lean_is_exclusive(x_173);
if (x_181 == 0)
{
return x_173;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_173, 0);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_173);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_169);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_170);
if (x_185 == 0)
{
return x_170;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_170, 0);
x_187 = lean_ctor_get(x_170, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_170);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
case 6:
{
lean_object* x_189; lean_object* x_190; uint64_t x_191; lean_object* x_192; 
lean_free_object(x_163);
x_189 = lean_ctor_get(x_5, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_5, 2);
lean_inc(x_190);
x_191 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_192 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_189, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_nat_add(x_6, x_161);
lean_dec(x_6);
x_196 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_190, x_195, x_7, x_8, x_9, x_10, x_11, x_194);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_196, 0);
x_199 = (uint8_t)((x_191 << 24) >> 61);
x_200 = lean_expr_update_lambda(x_5, x_199, x_193, x_198);
lean_ctor_set(x_196, 0, x_200);
return x_196;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_196, 0);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_196);
x_203 = (uint8_t)((x_191 << 24) >> 61);
x_204 = lean_expr_update_lambda(x_5, x_203, x_193, x_201);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_dec(x_193);
lean_dec(x_5);
x_206 = !lean_is_exclusive(x_196);
if (x_206 == 0)
{
return x_196;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_196, 0);
x_208 = lean_ctor_get(x_196, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_196);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_190);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_192);
if (x_210 == 0)
{
return x_192;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_192, 0);
x_212 = lean_ctor_get(x_192, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_192);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
case 7:
{
lean_object* x_214; lean_object* x_215; uint64_t x_216; lean_object* x_217; 
lean_free_object(x_163);
x_214 = lean_ctor_get(x_5, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_5, 2);
lean_inc(x_215);
x_216 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_217 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_214, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_nat_add(x_6, x_161);
lean_dec(x_6);
x_221 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_215, x_220, x_7, x_8, x_9, x_10, x_11, x_219);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = (uint8_t)((x_216 << 24) >> 61);
x_225 = lean_expr_update_forall(x_5, x_224, x_218, x_223);
lean_ctor_set(x_221, 0, x_225);
return x_221;
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_221, 0);
x_227 = lean_ctor_get(x_221, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_221);
x_228 = (uint8_t)((x_216 << 24) >> 61);
x_229 = lean_expr_update_forall(x_5, x_228, x_218, x_226);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
return x_230;
}
}
else
{
uint8_t x_231; 
lean_dec(x_218);
lean_dec(x_5);
x_231 = !lean_is_exclusive(x_221);
if (x_231 == 0)
{
return x_221;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_221, 0);
x_233 = lean_ctor_get(x_221, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_221);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_215);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_217);
if (x_235 == 0)
{
return x_217;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_217, 0);
x_237 = lean_ctor_get(x_217, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_217);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
case 8:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_free_object(x_163);
x_239 = lean_ctor_get(x_5, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_5, 2);
lean_inc(x_240);
x_241 = lean_ctor_get(x_5, 3);
lean_inc(x_241);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_242 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_239, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_245 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_240, x_6, x_7, x_8, x_9, x_10, x_11, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_nat_add(x_6, x_161);
lean_dec(x_6);
x_249 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_241, x_248, x_7, x_8, x_9, x_10, x_11, x_247);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_249, 0);
x_252 = lean_expr_update_let(x_5, x_243, x_246, x_251);
lean_ctor_set(x_249, 0, x_252);
return x_249;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_249, 0);
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_249);
x_255 = lean_expr_update_let(x_5, x_243, x_246, x_253);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
uint8_t x_257; 
lean_dec(x_246);
lean_dec(x_243);
lean_dec(x_5);
x_257 = !lean_is_exclusive(x_249);
if (x_257 == 0)
{
return x_249;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_249, 0);
x_259 = lean_ctor_get(x_249, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_249);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_243);
lean_dec(x_241);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_245);
if (x_261 == 0)
{
return x_245;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_245, 0);
x_263 = lean_ctor_get(x_245, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_245);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_242);
if (x_265 == 0)
{
return x_242;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_242, 0);
x_267 = lean_ctor_get(x_242, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_242);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
case 10:
{
lean_object* x_269; lean_object* x_270; 
lean_free_object(x_163);
x_269 = lean_ctor_get(x_5, 1);
lean_inc(x_269);
x_270 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_269, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_270, 0);
x_273 = lean_expr_update_mdata(x_5, x_272);
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
x_276 = lean_expr_update_mdata(x_5, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
uint8_t x_278; 
lean_dec(x_5);
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
case 11:
{
lean_object* x_282; lean_object* x_283; 
lean_free_object(x_163);
x_282 = lean_ctor_get(x_5, 2);
lean_inc(x_282);
x_283 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_282, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
if (lean_obj_tag(x_283) == 0)
{
uint8_t x_284; 
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_283, 0);
x_286 = lean_expr_update_proj(x_5, x_285);
lean_ctor_set(x_283, 0, x_286);
return x_283;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_287 = lean_ctor_get(x_283, 0);
x_288 = lean_ctor_get(x_283, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_283);
x_289 = lean_expr_update_proj(x_5, x_287);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
else
{
uint8_t x_291; 
lean_dec(x_5);
x_291 = !lean_is_exclusive(x_283);
if (x_291 == 0)
{
return x_283;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_283, 0);
x_293 = lean_ctor_get(x_283, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_283);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
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
lean_ctor_set(x_163, 0, x_5);
return x_163;
}
}
}
else
{
lean_object* x_295; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_295 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_163, 0, x_295);
return x_163;
}
}
else
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_ctor_get(x_163, 1);
lean_inc(x_296);
lean_dec(x_163);
x_297 = l_Lean_Occurrences_contains(x_2, x_159);
lean_dec(x_159);
if (x_297 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_5, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_5, 1);
lean_inc(x_299);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_300 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_298, x_6, x_7, x_8, x_9, x_10, x_11, x_296);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_299, x_6, x_7, x_8, x_9, x_10, x_11, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
x_307 = lean_expr_update_app(x_5, x_301, x_304);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_301);
lean_dec(x_5);
x_309 = lean_ctor_get(x_303, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_303, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_311 = x_303;
} else {
 lean_dec_ref(x_303);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_299);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_313 = lean_ctor_get(x_300, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_300, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_315 = x_300;
} else {
 lean_dec_ref(x_300);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
case 6:
{
lean_object* x_317; lean_object* x_318; uint64_t x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_5, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_5, 2);
lean_inc(x_318);
x_319 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_320 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_317, x_6, x_7, x_8, x_9, x_10, x_11, x_296);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_nat_add(x_6, x_161);
lean_dec(x_6);
x_324 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_318, x_323, x_7, x_8, x_9, x_10, x_11, x_322);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_327 = x_324;
} else {
 lean_dec_ref(x_324);
 x_327 = lean_box(0);
}
x_328 = (uint8_t)((x_319 << 24) >> 61);
x_329 = lean_expr_update_lambda(x_5, x_328, x_321, x_325);
if (lean_is_scalar(x_327)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_327;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_326);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_321);
lean_dec(x_5);
x_331 = lean_ctor_get(x_324, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_324, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_333 = x_324;
} else {
 lean_dec_ref(x_324);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_318);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_335 = lean_ctor_get(x_320, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_320, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_337 = x_320;
} else {
 lean_dec_ref(x_320);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
case 7:
{
lean_object* x_339; lean_object* x_340; uint64_t x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_5, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_5, 2);
lean_inc(x_340);
x_341 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_342 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_339, x_6, x_7, x_8, x_9, x_10, x_11, x_296);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_nat_add(x_6, x_161);
lean_dec(x_6);
x_346 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_340, x_345, x_7, x_8, x_9, x_10, x_11, x_344);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_349 = x_346;
} else {
 lean_dec_ref(x_346);
 x_349 = lean_box(0);
}
x_350 = (uint8_t)((x_341 << 24) >> 61);
x_351 = lean_expr_update_forall(x_5, x_350, x_343, x_347);
if (lean_is_scalar(x_349)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_349;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_348);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_343);
lean_dec(x_5);
x_353 = lean_ctor_get(x_346, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_346, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_355 = x_346;
} else {
 lean_dec_ref(x_346);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_340);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_357 = lean_ctor_get(x_342, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_342, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_359 = x_342;
} else {
 lean_dec_ref(x_342);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
case 8:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_5, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_5, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_5, 3);
lean_inc(x_363);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_364 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_361, x_6, x_7, x_8, x_9, x_10, x_11, x_296);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_367 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_362, x_6, x_7, x_8, x_9, x_10, x_11, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_nat_add(x_6, x_161);
lean_dec(x_6);
x_371 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_363, x_370, x_7, x_8, x_9, x_10, x_11, x_369);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
x_375 = lean_expr_update_let(x_5, x_365, x_368, x_372);
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_373);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_368);
lean_dec(x_365);
lean_dec(x_5);
x_377 = lean_ctor_get(x_371, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_371, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_379 = x_371;
} else {
 lean_dec_ref(x_371);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_381 = lean_ctor_get(x_367, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_367, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_383 = x_367;
} else {
 lean_dec_ref(x_367);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_385 = lean_ctor_get(x_364, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_364, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_387 = x_364;
} else {
 lean_dec_ref(x_364);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
case 10:
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_5, 1);
lean_inc(x_389);
x_390 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_389, x_6, x_7, x_8, x_9, x_10, x_11, x_296);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
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
x_394 = lean_expr_update_mdata(x_5, x_391);
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_392);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_5);
x_396 = lean_ctor_get(x_390, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_390, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_398 = x_390;
} else {
 lean_dec_ref(x_390);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
case 11:
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_5, 2);
lean_inc(x_400);
x_401 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_400, x_6, x_7, x_8, x_9, x_10, x_11, x_296);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
x_405 = lean_expr_update_proj(x_5, x_402);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_403);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_5);
x_407 = lean_ctor_get(x_401, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_409 = x_401;
} else {
 lean_dec_ref(x_401);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
default: 
{
lean_object* x_411; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_5);
lean_ctor_set(x_411, 1, x_296);
return x_411;
}
}
}
else
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_412 = l_Lean_mkBVar(x_6);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_296);
return x_413;
}
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_414 = !lean_is_exclusive(x_14);
if (x_414 == 0)
{
return x_14;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_14, 0);
x_416 = lean_ctor_get(x_14, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_14);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_5, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_5, 1);
lean_inc(x_419);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_420 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_418, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_419, x_6, x_7, x_8, x_9, x_10, x_11, x_422);
if (lean_obj_tag(x_423) == 0)
{
uint8_t x_424; 
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_423, 0);
x_426 = lean_expr_update_app(x_5, x_421, x_425);
lean_ctor_set(x_423, 0, x_426);
return x_423;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_423, 0);
x_428 = lean_ctor_get(x_423, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_423);
x_429 = lean_expr_update_app(x_5, x_421, x_427);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
else
{
uint8_t x_431; 
lean_dec(x_421);
lean_dec(x_5);
x_431 = !lean_is_exclusive(x_423);
if (x_431 == 0)
{
return x_423;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_423, 0);
x_433 = lean_ctor_get(x_423, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_423);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
else
{
uint8_t x_435; 
lean_dec(x_419);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_435 = !lean_is_exclusive(x_420);
if (x_435 == 0)
{
return x_420;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_420, 0);
x_437 = lean_ctor_get(x_420, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_420);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
}
}
}
case 6:
{
lean_object* x_439; lean_object* x_440; uint64_t x_441; lean_object* x_442; 
x_439 = lean_ctor_get(x_5, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_5, 2);
lean_inc(x_440);
x_441 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_442 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_439, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_unsigned_to_nat(1u);
x_446 = lean_nat_add(x_6, x_445);
lean_dec(x_6);
x_447 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_440, x_446, x_7, x_8, x_9, x_10, x_11, x_444);
if (lean_obj_tag(x_447) == 0)
{
uint8_t x_448; 
x_448 = !lean_is_exclusive(x_447);
if (x_448 == 0)
{
lean_object* x_449; uint8_t x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_447, 0);
x_450 = (uint8_t)((x_441 << 24) >> 61);
x_451 = lean_expr_update_lambda(x_5, x_450, x_443, x_449);
lean_ctor_set(x_447, 0, x_451);
return x_447;
}
else
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_447, 0);
x_453 = lean_ctor_get(x_447, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_447);
x_454 = (uint8_t)((x_441 << 24) >> 61);
x_455 = lean_expr_update_lambda(x_5, x_454, x_443, x_452);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_453);
return x_456;
}
}
else
{
uint8_t x_457; 
lean_dec(x_443);
lean_dec(x_5);
x_457 = !lean_is_exclusive(x_447);
if (x_457 == 0)
{
return x_447;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_447, 0);
x_459 = lean_ctor_get(x_447, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_447);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_440);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_461 = !lean_is_exclusive(x_442);
if (x_461 == 0)
{
return x_442;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_442, 0);
x_463 = lean_ctor_get(x_442, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_442);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
case 7:
{
lean_object* x_465; lean_object* x_466; uint64_t x_467; lean_object* x_468; 
x_465 = lean_ctor_get(x_5, 1);
lean_inc(x_465);
x_466 = lean_ctor_get(x_5, 2);
lean_inc(x_466);
x_467 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_468 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_465, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = lean_unsigned_to_nat(1u);
x_472 = lean_nat_add(x_6, x_471);
lean_dec(x_6);
x_473 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_466, x_472, x_7, x_8, x_9, x_10, x_11, x_470);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; 
x_474 = !lean_is_exclusive(x_473);
if (x_474 == 0)
{
lean_object* x_475; uint8_t x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_473, 0);
x_476 = (uint8_t)((x_467 << 24) >> 61);
x_477 = lean_expr_update_forall(x_5, x_476, x_469, x_475);
lean_ctor_set(x_473, 0, x_477);
return x_473;
}
else
{
lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; 
x_478 = lean_ctor_get(x_473, 0);
x_479 = lean_ctor_get(x_473, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_473);
x_480 = (uint8_t)((x_467 << 24) >> 61);
x_481 = lean_expr_update_forall(x_5, x_480, x_469, x_478);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_479);
return x_482;
}
}
else
{
uint8_t x_483; 
lean_dec(x_469);
lean_dec(x_5);
x_483 = !lean_is_exclusive(x_473);
if (x_483 == 0)
{
return x_473;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_473, 0);
x_485 = lean_ctor_get(x_473, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_473);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_466);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_487 = !lean_is_exclusive(x_468);
if (x_487 == 0)
{
return x_468;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_468, 0);
x_489 = lean_ctor_get(x_468, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_468);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
case 8:
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_491 = lean_ctor_get(x_5, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_5, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_5, 3);
lean_inc(x_493);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_494 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_491, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_inc(x_1);
x_497 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_492, x_6, x_7, x_8, x_9, x_10, x_11, x_496);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_unsigned_to_nat(1u);
x_501 = lean_nat_add(x_6, x_500);
lean_dec(x_6);
x_502 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_493, x_501, x_7, x_8, x_9, x_10, x_11, x_499);
if (lean_obj_tag(x_502) == 0)
{
uint8_t x_503; 
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; 
x_504 = lean_ctor_get(x_502, 0);
x_505 = lean_expr_update_let(x_5, x_495, x_498, x_504);
lean_ctor_set(x_502, 0, x_505);
return x_502;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_506 = lean_ctor_get(x_502, 0);
x_507 = lean_ctor_get(x_502, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_502);
x_508 = lean_expr_update_let(x_5, x_495, x_498, x_506);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
else
{
uint8_t x_510; 
lean_dec(x_498);
lean_dec(x_495);
lean_dec(x_5);
x_510 = !lean_is_exclusive(x_502);
if (x_510 == 0)
{
return x_502;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_502, 0);
x_512 = lean_ctor_get(x_502, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_502);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
else
{
uint8_t x_514; 
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_514 = !lean_is_exclusive(x_497);
if (x_514 == 0)
{
return x_497;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_497, 0);
x_516 = lean_ctor_get(x_497, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_497);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
else
{
uint8_t x_518; 
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_518 = !lean_is_exclusive(x_494);
if (x_518 == 0)
{
return x_494;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_494, 0);
x_520 = lean_ctor_get(x_494, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_494);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
}
case 10:
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_ctor_get(x_5, 1);
lean_inc(x_522);
x_523 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_522, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_5);
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
case 11:
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_5, 2);
lean_inc(x_535);
x_536 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_535, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_536) == 0)
{
uint8_t x_537; 
x_537 = !lean_is_exclusive(x_536);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_ctor_get(x_536, 0);
x_539 = lean_expr_update_proj(x_5, x_538);
lean_ctor_set(x_536, 0, x_539);
return x_536;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_540 = lean_ctor_get(x_536, 0);
x_541 = lean_ctor_get(x_536, 1);
lean_inc(x_541);
lean_inc(x_540);
lean_dec(x_536);
x_542 = lean_expr_update_proj(x_5, x_540);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
else
{
uint8_t x_544; 
lean_dec(x_5);
x_544 = !lean_is_exclusive(x_536);
if (x_544 == 0)
{
return x_536;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_536, 0);
x_546 = lean_ctor_get(x_536, 1);
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_536);
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
return x_547;
}
}
}
default: 
{
lean_object* x_548; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_5);
lean_ctor_set(x_548, 1, x_12);
return x_548;
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
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Meta_kabstract___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_5, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_kabstract___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_kabstract___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_kabstract___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_kabstract___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_kabstract___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg___lambda__3___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_kabstract___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_isFVar(x_3);
if (x_5 == 0)
{
uint8_t x_22; 
x_22 = 0;
x_6 = x_22;
goto block_21;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Occurrences_beq(x_4, x_23);
x_6 = x_24;
goto block_21;
}
block_21:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_Expr_toHeadIndex___main(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_3, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg___lambda__2___boxed), 11, 5);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_2);
x_11 = l_Lean_Meta_kabstract___rarg___closed__2;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_kabstract___rarg___closed__3;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_apply_2(x_1, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = l_Lean_mkOptionalNode___closed__2;
x_17 = lean_array_push(x_16, x_3);
x_18 = lean_expr_abstract(x_2, x_17);
lean_dec(x_17);
lean_dec(x_2);
x_19 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_instantiateMVars___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_apply_2(x_1, lean_box(0), x_19);
return x_20;
}
}
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
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_kabstract___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_kabstract___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_kabstract___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Meta_kabstract___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_kabstract___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
l_Lean_Meta_kabstract___rarg___closed__1 = _init_l_Lean_Meta_kabstract___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_kabstract___rarg___closed__1);
l_Lean_Meta_kabstract___rarg___closed__2 = _init_l_Lean_Meta_kabstract___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_kabstract___rarg___closed__2);
l_Lean_Meta_kabstract___rarg___closed__3 = _init_l_Lean_Meta_kabstract___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_kabstract___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
