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
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_KAbstract_1__kabstractAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___closed__3;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_15__runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___closed__2;
lean_object* l_Lean_Meta_kabstract___rarg___closed__1;
lean_object* l_Lean_Meta_kabstract___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_KAbstract_1__kabstractAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_KAbstract_1__kabstractAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_230 = lean_st_ref_get(x_7, x_8);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_231, 2);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_ctor_get_uint8(x_232, sizeof(void*)*1);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_dec(x_230);
x_235 = 0;
x_10 = x_235;
x_11 = x_234;
goto block_229;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
lean_dec(x_230);
x_237 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_238 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_237, x_4, x_5, x_6, x_7, x_236);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_unbox(x_239);
lean_dec(x_239);
x_10 = x_241;
x_11 = x_240;
goto block_229;
}
block_229:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
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
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 2);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_60; 
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
x_60 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_61);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_63, 0, x_1);
lean_closure_set(x_63, 1, x_2);
lean_closure_set(x_63, 2, x_61);
x_64 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_65 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_64, x_63, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_7, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_7, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_70, 2);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_16);
x_76 = lean_st_ref_set(x_7, x_70, x_72);
lean_dec(x_7);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_61);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_16);
lean_ctor_set(x_70, 2, x_82);
x_83 = lean_st_ref_set(x_7, x_70, x_72);
lean_dec(x_7);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_61);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_70, 0);
x_88 = lean_ctor_get(x_70, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_70);
x_89 = lean_ctor_get(x_71, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_90 = x_71;
} else {
 lean_dec_ref(x_71);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 1, 1);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_16);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_st_ref_set(x_7, x_92, x_72);
lean_dec(x_7);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_61);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_60, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_dec(x_60);
x_27 = x_97;
x_28 = x_98;
goto block_59;
}
block_59:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_st_ref_get(x_7, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 2);
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
lean_ctor_set(x_32, 2, x_44);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_51 = lean_ctor_get(x_33, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_52 = x_33;
} else {
 lean_dec_ref(x_33);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 1);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_16);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_st_ref_set(x_7, x_54, x_34);
lean_dec(x_7);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_27);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_124; 
x_99 = lean_ctor_get(x_19, 0);
lean_inc(x_99);
lean_dec(x_19);
x_100 = 0;
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
lean_ctor_set(x_18, 2, x_101);
x_102 = lean_st_ref_set(x_7, x_18, x_20);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_124 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_103);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_125);
x_127 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_127, 0, x_1);
lean_closure_set(x_127, 1, x_2);
lean_closure_set(x_127, 2, x_125);
x_128 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_129 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_128, x_127, x_4, x_5, x_6, x_7, x_126);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_st_ref_get(x_7, x_130);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_7, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_141 = x_135;
} else {
 lean_dec_ref(x_135);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 1, 1);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 3, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_142);
x_144 = lean_st_ref_set(x_7, x_143, x_136);
lean_dec(x_7);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_125);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_124, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_124, 1);
lean_inc(x_149);
lean_dec(x_124);
x_104 = x_148;
x_105 = x_149;
goto block_123;
}
block_123:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_106 = lean_st_ref_get(x_7, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_7, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_116 = x_110;
} else {
 lean_dec_ref(x_110);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 1, 1);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 3, 0);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_113);
lean_ctor_set(x_118, 2, x_117);
x_119 = lean_st_ref_set(x_7, x_118, x_111);
lean_dec(x_7);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_104);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_179; 
x_150 = lean_ctor_get(x_18, 0);
x_151 = lean_ctor_get(x_18, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_18);
x_152 = lean_ctor_get(x_19, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_153 = x_19;
} else {
 lean_dec_ref(x_19);
 x_153 = lean_box(0);
}
x_154 = 0;
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 1, 1);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_150);
lean_ctor_set(x_156, 1, x_151);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_st_ref_set(x_7, x_156, x_20);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_179 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_158);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
lean_inc(x_180);
x_182 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_182, 0, x_1);
lean_closure_set(x_182, 1, x_2);
lean_closure_set(x_182, 2, x_180);
x_183 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_184 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_183, x_182, x_4, x_5, x_6, x_7, x_181);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_st_ref_get(x_7, x_185);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_st_ref_take(x_7, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_ctor_get(x_189, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_194 = x_189;
} else {
 lean_dec_ref(x_189);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_190, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_196 = x_190;
} else {
 lean_dec_ref(x_190);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 1, 1);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_194)) {
 x_198 = lean_alloc_ctor(0, 3, 0);
} else {
 x_198 = x_194;
}
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_193);
lean_ctor_set(x_198, 2, x_197);
x_199 = lean_st_ref_set(x_7, x_198, x_191);
lean_dec(x_7);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_180);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_179, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_179, 1);
lean_inc(x_204);
lean_dec(x_179);
x_159 = x_203;
x_160 = x_204;
goto block_178;
}
block_178:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_161 = lean_st_ref_get(x_7, x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_st_ref_take(x_7, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 1, 1);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 3, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_168);
lean_ctor_set(x_173, 2, x_172);
x_174 = lean_st_ref_set(x_7, x_173, x_166);
lean_dec(x_7);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
 lean_ctor_set_tag(x_177, 1);
}
lean_ctor_set(x_177, 0, x_159);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_6, 3);
lean_inc(x_205);
x_206 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_7, x_11);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_209 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_9, x_4, x_5, x_6, x_7, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
lean_inc(x_210);
x_212 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_212, 0, x_1);
lean_closure_set(x_212, 1, x_2);
lean_closure_set(x_212, 2, x_210);
x_213 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_214 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_213, x_212, x_4, x_5, x_6, x_7, x_211);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_207, x_213, x_205, x_4, x_5, x_6, x_7, x_215);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_216, 0);
lean_dec(x_218);
lean_ctor_set(x_216, 0, x_210);
return x_216;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_210);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_dec(x_2);
lean_dec(x_1);
x_221 = lean_ctor_get(x_209, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_209, 1);
lean_inc(x_222);
lean_dec(x_209);
x_223 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_224 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_207, x_223, x_205, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_224, 0);
lean_dec(x_226);
lean_ctor_set_tag(x_224, 1);
lean_ctor_set(x_224, 0, x_221);
return x_224;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_146; 
x_146 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = l_Lean_Expr_toHeadIndex___main(x_5);
x_148 = l_Lean_HeadIndex_HeadIndex_beq(x_147, x_3);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_13 = x_149;
goto block_145;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_unsigned_to_nat(0u);
x_151 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_5, x_150);
x_152 = lean_nat_dec_eq(x_151, x_4);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_box(0);
x_13 = x_153;
goto block_145;
}
else
{
lean_object* x_154; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_5);
x_154 = l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_KAbstract_1__kabstractAux___main___spec__1(x_5, x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_5, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_5, 1);
lean_inc(x_159);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_160 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_158, x_6, x_7, x_8, x_9, x_10, x_11, x_157);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_159, x_6, x_7, x_8, x_9, x_10, x_11, x_162);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_expr_update_app(x_5, x_161, x_165);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_163);
x_169 = lean_expr_update_app(x_5, x_161, x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
uint8_t x_171; 
lean_dec(x_161);
lean_dec(x_5);
x_171 = !lean_is_exclusive(x_163);
if (x_171 == 0)
{
return x_163;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_163, 0);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_163);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_159);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_160);
if (x_175 == 0)
{
return x_160;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_160, 0);
x_177 = lean_ctor_get(x_160, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_160);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 6:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint64_t x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_154, 1);
lean_inc(x_179);
lean_dec(x_154);
x_180 = lean_ctor_get(x_5, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_5, 2);
lean_inc(x_181);
x_182 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_183 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_180, x_6, x_7, x_8, x_9, x_10, x_11, x_179);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_add(x_6, x_186);
lean_dec(x_6);
x_188 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_181, x_187, x_7, x_8, x_9, x_10, x_11, x_185);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = (uint8_t)((x_182 << 24) >> 61);
x_192 = lean_expr_update_lambda(x_5, x_191, x_184, x_190);
lean_ctor_set(x_188, 0, x_192);
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_188, 0);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_188);
x_195 = (uint8_t)((x_182 << 24) >> 61);
x_196 = lean_expr_update_lambda(x_5, x_195, x_184, x_193);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_194);
return x_197;
}
}
else
{
uint8_t x_198; 
lean_dec(x_184);
lean_dec(x_5);
x_198 = !lean_is_exclusive(x_188);
if (x_198 == 0)
{
return x_188;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_188, 0);
x_200 = lean_ctor_get(x_188, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_188);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_181);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_202 = !lean_is_exclusive(x_183);
if (x_202 == 0)
{
return x_183;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_183, 0);
x_204 = lean_ctor_get(x_183, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_183);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
case 7:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint64_t x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_154, 1);
lean_inc(x_206);
lean_dec(x_154);
x_207 = lean_ctor_get(x_5, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_5, 2);
lean_inc(x_208);
x_209 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_210 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_207, x_6, x_7, x_8, x_9, x_10, x_11, x_206);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_add(x_6, x_213);
lean_dec(x_6);
x_215 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_208, x_214, x_7, x_8, x_9, x_10, x_11, x_212);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = (uint8_t)((x_209 << 24) >> 61);
x_219 = lean_expr_update_forall(x_5, x_218, x_211, x_217);
lean_ctor_set(x_215, 0, x_219);
return x_215;
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_215, 0);
x_221 = lean_ctor_get(x_215, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_215);
x_222 = (uint8_t)((x_209 << 24) >> 61);
x_223 = lean_expr_update_forall(x_5, x_222, x_211, x_220);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
}
else
{
uint8_t x_225; 
lean_dec(x_211);
lean_dec(x_5);
x_225 = !lean_is_exclusive(x_215);
if (x_225 == 0)
{
return x_215;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_215, 0);
x_227 = lean_ctor_get(x_215, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_215);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_208);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_229 = !lean_is_exclusive(x_210);
if (x_229 == 0)
{
return x_210;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_210, 0);
x_231 = lean_ctor_get(x_210, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_210);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
case 8:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_154, 1);
lean_inc(x_233);
lean_dec(x_154);
x_234 = lean_ctor_get(x_5, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_5, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_5, 3);
lean_inc(x_236);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_237 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_234, x_6, x_7, x_8, x_9, x_10, x_11, x_233);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_240 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_235, x_6, x_7, x_8, x_9, x_10, x_11, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_unsigned_to_nat(1u);
x_244 = lean_nat_add(x_6, x_243);
lean_dec(x_6);
x_245 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_236, x_244, x_7, x_8, x_9, x_10, x_11, x_242);
if (lean_obj_tag(x_245) == 0)
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
x_248 = lean_expr_update_let(x_5, x_238, x_241, x_247);
lean_ctor_set(x_245, 0, x_248);
return x_245;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_245, 0);
x_250 = lean_ctor_get(x_245, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_245);
x_251 = lean_expr_update_let(x_5, x_238, x_241, x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
uint8_t x_253; 
lean_dec(x_241);
lean_dec(x_238);
lean_dec(x_5);
x_253 = !lean_is_exclusive(x_245);
if (x_253 == 0)
{
return x_245;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_245, 0);
x_255 = lean_ctor_get(x_245, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_245);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_257 = !lean_is_exclusive(x_240);
if (x_257 == 0)
{
return x_240;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_240, 0);
x_259 = lean_ctor_get(x_240, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_240);
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
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_261 = !lean_is_exclusive(x_237);
if (x_261 == 0)
{
return x_237;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_237, 0);
x_263 = lean_ctor_get(x_237, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_237);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
case 10:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_154, 1);
lean_inc(x_265);
lean_dec(x_154);
x_266 = lean_ctor_get(x_5, 1);
lean_inc(x_266);
x_267 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_266, x_6, x_7, x_8, x_9, x_10, x_11, x_265);
if (lean_obj_tag(x_267) == 0)
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_expr_update_mdata(x_5, x_269);
lean_ctor_set(x_267, 0, x_270);
return x_267;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_267, 0);
x_272 = lean_ctor_get(x_267, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_267);
x_273 = lean_expr_update_mdata(x_5, x_271);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
uint8_t x_275; 
lean_dec(x_5);
x_275 = !lean_is_exclusive(x_267);
if (x_275 == 0)
{
return x_267;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_267, 0);
x_277 = lean_ctor_get(x_267, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_267);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
case 11:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_154, 1);
lean_inc(x_279);
lean_dec(x_154);
x_280 = lean_ctor_get(x_5, 2);
lean_inc(x_280);
x_281 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_280, x_6, x_7, x_8, x_9, x_10, x_11, x_279);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_281, 0);
x_284 = lean_expr_update_proj(x_5, x_283);
lean_ctor_set(x_281, 0, x_284);
return x_281;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_281, 0);
x_286 = lean_ctor_get(x_281, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_281);
x_287 = lean_expr_update_proj(x_5, x_285);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
uint8_t x_289; 
lean_dec(x_5);
x_289 = !lean_is_exclusive(x_281);
if (x_289 == 0)
{
return x_281;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_281, 0);
x_291 = lean_ctor_get(x_281, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_281);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
default: 
{
uint8_t x_293; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_293 = !lean_is_exclusive(x_154);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_154, 0);
lean_dec(x_294);
lean_ctor_set(x_154, 0, x_5);
return x_154;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_154, 1);
lean_inc(x_295);
lean_dec(x_154);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_5);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_297 = lean_ctor_get(x_154, 1);
lean_inc(x_297);
lean_dec(x_154);
x_298 = lean_st_ref_get(x_7, x_297);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_unsigned_to_nat(1u);
x_302 = lean_nat_add(x_299, x_301);
x_303 = lean_st_ref_set(x_7, x_302, x_300);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_303, 1);
x_306 = lean_ctor_get(x_303, 0);
lean_dec(x_306);
x_307 = l_Lean_Occurrences_contains(x_1, x_299);
lean_dec(x_299);
if (x_307 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_free_object(x_303);
x_308 = lean_ctor_get(x_5, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_5, 1);
lean_inc(x_309);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_310 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_308, x_6, x_7, x_8, x_9, x_10, x_11, x_305);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_309, x_6, x_7, x_8, x_9, x_10, x_11, x_312);
if (lean_obj_tag(x_313) == 0)
{
uint8_t x_314; 
x_314 = !lean_is_exclusive(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_313, 0);
x_316 = lean_expr_update_app(x_5, x_311, x_315);
lean_ctor_set(x_313, 0, x_316);
return x_313;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_313, 0);
x_318 = lean_ctor_get(x_313, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_313);
x_319 = lean_expr_update_app(x_5, x_311, x_317);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
else
{
uint8_t x_321; 
lean_dec(x_311);
lean_dec(x_5);
x_321 = !lean_is_exclusive(x_313);
if (x_321 == 0)
{
return x_313;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_313, 0);
x_323 = lean_ctor_get(x_313, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_313);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_309);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_325 = !lean_is_exclusive(x_310);
if (x_325 == 0)
{
return x_310;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_310, 0);
x_327 = lean_ctor_get(x_310, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_310);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
case 6:
{
lean_object* x_329; lean_object* x_330; uint64_t x_331; lean_object* x_332; 
lean_free_object(x_303);
x_329 = lean_ctor_get(x_5, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_5, 2);
lean_inc(x_330);
x_331 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_332 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_329, x_6, x_7, x_8, x_9, x_10, x_11, x_305);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_nat_add(x_6, x_301);
lean_dec(x_6);
x_336 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_330, x_335, x_7, x_8, x_9, x_10, x_11, x_334);
if (lean_obj_tag(x_336) == 0)
{
uint8_t x_337; 
x_337 = !lean_is_exclusive(x_336);
if (x_337 == 0)
{
lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_336, 0);
x_339 = (uint8_t)((x_331 << 24) >> 61);
x_340 = lean_expr_update_lambda(x_5, x_339, x_333, x_338);
lean_ctor_set(x_336, 0, x_340);
return x_336;
}
else
{
lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_336, 0);
x_342 = lean_ctor_get(x_336, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_336);
x_343 = (uint8_t)((x_331 << 24) >> 61);
x_344 = lean_expr_update_lambda(x_5, x_343, x_333, x_341);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_342);
return x_345;
}
}
else
{
uint8_t x_346; 
lean_dec(x_333);
lean_dec(x_5);
x_346 = !lean_is_exclusive(x_336);
if (x_346 == 0)
{
return x_336;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_336, 0);
x_348 = lean_ctor_get(x_336, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_336);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
else
{
uint8_t x_350; 
lean_dec(x_330);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_350 = !lean_is_exclusive(x_332);
if (x_350 == 0)
{
return x_332;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_332, 0);
x_352 = lean_ctor_get(x_332, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_332);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
case 7:
{
lean_object* x_354; lean_object* x_355; uint64_t x_356; lean_object* x_357; 
lean_free_object(x_303);
x_354 = lean_ctor_get(x_5, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_5, 2);
lean_inc(x_355);
x_356 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_357 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_354, x_6, x_7, x_8, x_9, x_10, x_11, x_305);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_nat_add(x_6, x_301);
lean_dec(x_6);
x_361 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_355, x_360, x_7, x_8, x_9, x_10, x_11, x_359);
if (lean_obj_tag(x_361) == 0)
{
uint8_t x_362; 
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_361, 0);
x_364 = (uint8_t)((x_356 << 24) >> 61);
x_365 = lean_expr_update_forall(x_5, x_364, x_358, x_363);
lean_ctor_set(x_361, 0, x_365);
return x_361;
}
else
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_361, 0);
x_367 = lean_ctor_get(x_361, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_361);
x_368 = (uint8_t)((x_356 << 24) >> 61);
x_369 = lean_expr_update_forall(x_5, x_368, x_358, x_366);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_367);
return x_370;
}
}
else
{
uint8_t x_371; 
lean_dec(x_358);
lean_dec(x_5);
x_371 = !lean_is_exclusive(x_361);
if (x_371 == 0)
{
return x_361;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_361, 0);
x_373 = lean_ctor_get(x_361, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_361);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_375 = !lean_is_exclusive(x_357);
if (x_375 == 0)
{
return x_357;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_357, 0);
x_377 = lean_ctor_get(x_357, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_357);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
case 8:
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_free_object(x_303);
x_379 = lean_ctor_get(x_5, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_5, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_5, 3);
lean_inc(x_381);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_382 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_379, x_6, x_7, x_8, x_9, x_10, x_11, x_305);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_385 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_380, x_6, x_7, x_8, x_9, x_10, x_11, x_384);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_nat_add(x_6, x_301);
lean_dec(x_6);
x_389 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_381, x_388, x_7, x_8, x_9, x_10, x_11, x_387);
if (lean_obj_tag(x_389) == 0)
{
uint8_t x_390; 
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_389, 0);
x_392 = lean_expr_update_let(x_5, x_383, x_386, x_391);
lean_ctor_set(x_389, 0, x_392);
return x_389;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = lean_ctor_get(x_389, 0);
x_394 = lean_ctor_get(x_389, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_389);
x_395 = lean_expr_update_let(x_5, x_383, x_386, x_393);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
else
{
uint8_t x_397; 
lean_dec(x_386);
lean_dec(x_383);
lean_dec(x_5);
x_397 = !lean_is_exclusive(x_389);
if (x_397 == 0)
{
return x_389;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_389, 0);
x_399 = lean_ctor_get(x_389, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_389);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
uint8_t x_401; 
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_401 = !lean_is_exclusive(x_385);
if (x_401 == 0)
{
return x_385;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_385, 0);
x_403 = lean_ctor_get(x_385, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_385);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_405 = !lean_is_exclusive(x_382);
if (x_405 == 0)
{
return x_382;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_382, 0);
x_407 = lean_ctor_get(x_382, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_382);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
case 10:
{
lean_object* x_409; lean_object* x_410; 
lean_free_object(x_303);
x_409 = lean_ctor_get(x_5, 1);
lean_inc(x_409);
x_410 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_409, x_6, x_7, x_8, x_9, x_10, x_11, x_305);
if (lean_obj_tag(x_410) == 0)
{
uint8_t x_411; 
x_411 = !lean_is_exclusive(x_410);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_410, 0);
x_413 = lean_expr_update_mdata(x_5, x_412);
lean_ctor_set(x_410, 0, x_413);
return x_410;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = lean_ctor_get(x_410, 0);
x_415 = lean_ctor_get(x_410, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_410);
x_416 = lean_expr_update_mdata(x_5, x_414);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
uint8_t x_418; 
lean_dec(x_5);
x_418 = !lean_is_exclusive(x_410);
if (x_418 == 0)
{
return x_410;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_410, 0);
x_420 = lean_ctor_get(x_410, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_410);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
case 11:
{
lean_object* x_422; lean_object* x_423; 
lean_free_object(x_303);
x_422 = lean_ctor_get(x_5, 2);
lean_inc(x_422);
x_423 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_422, x_6, x_7, x_8, x_9, x_10, x_11, x_305);
if (lean_obj_tag(x_423) == 0)
{
uint8_t x_424; 
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_423, 0);
x_426 = lean_expr_update_proj(x_5, x_425);
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
x_429 = lean_expr_update_proj(x_5, x_427);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
else
{
uint8_t x_431; 
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
default: 
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_ctor_set(x_303, 0, x_5);
return x_303;
}
}
}
else
{
lean_object* x_435; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_435 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_303, 0, x_435);
return x_303;
}
}
else
{
lean_object* x_436; uint8_t x_437; 
x_436 = lean_ctor_get(x_303, 1);
lean_inc(x_436);
lean_dec(x_303);
x_437 = l_Lean_Occurrences_contains(x_1, x_299);
lean_dec(x_299);
if (x_437 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_5, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_5, 1);
lean_inc(x_439);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_440 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_438, x_6, x_7, x_8, x_9, x_10, x_11, x_436);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_439, x_6, x_7, x_8, x_9, x_10, x_11, x_442);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_446 = x_443;
} else {
 lean_dec_ref(x_443);
 x_446 = lean_box(0);
}
x_447 = lean_expr_update_app(x_5, x_441, x_444);
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_441);
lean_dec(x_5);
x_449 = lean_ctor_get(x_443, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_443, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_451 = x_443;
} else {
 lean_dec_ref(x_443);
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
lean_dec(x_439);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_453 = lean_ctor_get(x_440, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_440, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_455 = x_440;
} else {
 lean_dec_ref(x_440);
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
case 6:
{
lean_object* x_457; lean_object* x_458; uint64_t x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_5, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_5, 2);
lean_inc(x_458);
x_459 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_460 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_457, x_6, x_7, x_8, x_9, x_10, x_11, x_436);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = lean_nat_add(x_6, x_301);
lean_dec(x_6);
x_464 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_458, x_463, x_7, x_8, x_9, x_10, x_11, x_462);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; lean_object* x_470; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_467 = x_464;
} else {
 lean_dec_ref(x_464);
 x_467 = lean_box(0);
}
x_468 = (uint8_t)((x_459 << 24) >> 61);
x_469 = lean_expr_update_lambda(x_5, x_468, x_461, x_465);
if (lean_is_scalar(x_467)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_467;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_466);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_461);
lean_dec(x_5);
x_471 = lean_ctor_get(x_464, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_464, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_473 = x_464;
} else {
 lean_dec_ref(x_464);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_458);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_475 = lean_ctor_get(x_460, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_460, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_477 = x_460;
} else {
 lean_dec_ref(x_460);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_476);
return x_478;
}
}
case 7:
{
lean_object* x_479; lean_object* x_480; uint64_t x_481; lean_object* x_482; 
x_479 = lean_ctor_get(x_5, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_5, 2);
lean_inc(x_480);
x_481 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_482 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_479, x_6, x_7, x_8, x_9, x_10, x_11, x_436);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_nat_add(x_6, x_301);
lean_dec(x_6);
x_486 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_480, x_485, x_7, x_8, x_9, x_10, x_11, x_484);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; lean_object* x_492; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_489 = x_486;
} else {
 lean_dec_ref(x_486);
 x_489 = lean_box(0);
}
x_490 = (uint8_t)((x_481 << 24) >> 61);
x_491 = lean_expr_update_forall(x_5, x_490, x_483, x_487);
if (lean_is_scalar(x_489)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_489;
}
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_488);
return x_492;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_483);
lean_dec(x_5);
x_493 = lean_ctor_get(x_486, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_486, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_495 = x_486;
} else {
 lean_dec_ref(x_486);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_480);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_497 = lean_ctor_get(x_482, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_482, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_499 = x_482;
} else {
 lean_dec_ref(x_482);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
case 8:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_501 = lean_ctor_get(x_5, 1);
lean_inc(x_501);
x_502 = lean_ctor_get(x_5, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_5, 3);
lean_inc(x_503);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_504 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_501, x_6, x_7, x_8, x_9, x_10, x_11, x_436);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_507 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_502, x_6, x_7, x_8, x_9, x_10, x_11, x_506);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_nat_add(x_6, x_301);
lean_dec(x_6);
x_511 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_503, x_510, x_7, x_8, x_9, x_10, x_11, x_509);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_514 = x_511;
} else {
 lean_dec_ref(x_511);
 x_514 = lean_box(0);
}
x_515 = lean_expr_update_let(x_5, x_505, x_508, x_512);
if (lean_is_scalar(x_514)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_514;
}
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_513);
return x_516;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_508);
lean_dec(x_505);
lean_dec(x_5);
x_517 = lean_ctor_get(x_511, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_511, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_519 = x_511;
} else {
 lean_dec_ref(x_511);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_505);
lean_dec(x_503);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_521 = lean_ctor_get(x_507, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_507, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_523 = x_507;
} else {
 lean_dec_ref(x_507);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_521);
lean_ctor_set(x_524, 1, x_522);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_525 = lean_ctor_get(x_504, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_504, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_527 = x_504;
} else {
 lean_dec_ref(x_504);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
case 10:
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_ctor_get(x_5, 1);
lean_inc(x_529);
x_530 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_529, x_6, x_7, x_8, x_9, x_10, x_11, x_436);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_533 = x_530;
} else {
 lean_dec_ref(x_530);
 x_533 = lean_box(0);
}
x_534 = lean_expr_update_mdata(x_5, x_531);
if (lean_is_scalar(x_533)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_533;
}
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_532);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_5);
x_536 = lean_ctor_get(x_530, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_530, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_538 = x_530;
} else {
 lean_dec_ref(x_530);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
}
case 11:
{
lean_object* x_540; lean_object* x_541; 
x_540 = lean_ctor_get(x_5, 2);
lean_inc(x_540);
x_541 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_540, x_6, x_7, x_8, x_9, x_10, x_11, x_436);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_544 = x_541;
} else {
 lean_dec_ref(x_541);
 x_544 = lean_box(0);
}
x_545 = lean_expr_update_proj(x_5, x_542);
if (lean_is_scalar(x_544)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_544;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_543);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_5);
x_547 = lean_ctor_get(x_541, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_541, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_549 = x_541;
} else {
 lean_dec_ref(x_541);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
default: 
{
lean_object* x_551; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_5);
lean_ctor_set(x_551, 1, x_436);
return x_551;
}
}
}
else
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_552 = l_Lean_mkBVar(x_6);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_436);
return x_553;
}
}
}
}
else
{
uint8_t x_554; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_554 = !lean_is_exclusive(x_154);
if (x_554 == 0)
{
return x_154;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_154, 0);
x_556 = lean_ctor_get(x_154, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_154);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
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
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_5, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_5, 1);
lean_inc(x_559);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_560 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_558, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_563 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_559, x_6, x_7, x_8, x_9, x_10, x_11, x_562);
if (lean_obj_tag(x_563) == 0)
{
uint8_t x_564; 
x_564 = !lean_is_exclusive(x_563);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_563, 0);
x_566 = lean_expr_update_app(x_5, x_561, x_565);
lean_ctor_set(x_563, 0, x_566);
return x_563;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_563, 0);
x_568 = lean_ctor_get(x_563, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_563);
x_569 = lean_expr_update_app(x_5, x_561, x_567);
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_568);
return x_570;
}
}
else
{
uint8_t x_571; 
lean_dec(x_561);
lean_dec(x_5);
x_571 = !lean_is_exclusive(x_563);
if (x_571 == 0)
{
return x_563;
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_572 = lean_ctor_get(x_563, 0);
x_573 = lean_ctor_get(x_563, 1);
lean_inc(x_573);
lean_inc(x_572);
lean_dec(x_563);
x_574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
return x_574;
}
}
}
else
{
uint8_t x_575; 
lean_dec(x_559);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_575 = !lean_is_exclusive(x_560);
if (x_575 == 0)
{
return x_560;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_560, 0);
x_577 = lean_ctor_get(x_560, 1);
lean_inc(x_577);
lean_inc(x_576);
lean_dec(x_560);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
}
}
case 6:
{
lean_object* x_579; lean_object* x_580; uint64_t x_581; lean_object* x_582; 
x_579 = lean_ctor_get(x_5, 1);
lean_inc(x_579);
x_580 = lean_ctor_get(x_5, 2);
lean_inc(x_580);
x_581 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_582 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_579, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = lean_unsigned_to_nat(1u);
x_586 = lean_nat_add(x_6, x_585);
lean_dec(x_6);
x_587 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_580, x_586, x_7, x_8, x_9, x_10, x_11, x_584);
if (lean_obj_tag(x_587) == 0)
{
uint8_t x_588; 
x_588 = !lean_is_exclusive(x_587);
if (x_588 == 0)
{
lean_object* x_589; uint8_t x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_587, 0);
x_590 = (uint8_t)((x_581 << 24) >> 61);
x_591 = lean_expr_update_lambda(x_5, x_590, x_583, x_589);
lean_ctor_set(x_587, 0, x_591);
return x_587;
}
else
{
lean_object* x_592; lean_object* x_593; uint8_t x_594; lean_object* x_595; lean_object* x_596; 
x_592 = lean_ctor_get(x_587, 0);
x_593 = lean_ctor_get(x_587, 1);
lean_inc(x_593);
lean_inc(x_592);
lean_dec(x_587);
x_594 = (uint8_t)((x_581 << 24) >> 61);
x_595 = lean_expr_update_lambda(x_5, x_594, x_583, x_592);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_593);
return x_596;
}
}
else
{
uint8_t x_597; 
lean_dec(x_583);
lean_dec(x_5);
x_597 = !lean_is_exclusive(x_587);
if (x_597 == 0)
{
return x_587;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_587, 0);
x_599 = lean_ctor_get(x_587, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_587);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
return x_600;
}
}
}
else
{
uint8_t x_601; 
lean_dec(x_580);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_601 = !lean_is_exclusive(x_582);
if (x_601 == 0)
{
return x_582;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_582, 0);
x_603 = lean_ctor_get(x_582, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_582);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
case 7:
{
lean_object* x_605; lean_object* x_606; uint64_t x_607; lean_object* x_608; 
x_605 = lean_ctor_get(x_5, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_5, 2);
lean_inc(x_606);
x_607 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_608 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_605, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_611 = lean_unsigned_to_nat(1u);
x_612 = lean_nat_add(x_6, x_611);
lean_dec(x_6);
x_613 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_606, x_612, x_7, x_8, x_9, x_10, x_11, x_610);
if (lean_obj_tag(x_613) == 0)
{
uint8_t x_614; 
x_614 = !lean_is_exclusive(x_613);
if (x_614 == 0)
{
lean_object* x_615; uint8_t x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_613, 0);
x_616 = (uint8_t)((x_607 << 24) >> 61);
x_617 = lean_expr_update_forall(x_5, x_616, x_609, x_615);
lean_ctor_set(x_613, 0, x_617);
return x_613;
}
else
{
lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; lean_object* x_622; 
x_618 = lean_ctor_get(x_613, 0);
x_619 = lean_ctor_get(x_613, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_613);
x_620 = (uint8_t)((x_607 << 24) >> 61);
x_621 = lean_expr_update_forall(x_5, x_620, x_609, x_618);
x_622 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_619);
return x_622;
}
}
else
{
uint8_t x_623; 
lean_dec(x_609);
lean_dec(x_5);
x_623 = !lean_is_exclusive(x_613);
if (x_623 == 0)
{
return x_613;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_613, 0);
x_625 = lean_ctor_get(x_613, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_613);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_625);
return x_626;
}
}
}
else
{
uint8_t x_627; 
lean_dec(x_606);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_627 = !lean_is_exclusive(x_608);
if (x_627 == 0)
{
return x_608;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_608, 0);
x_629 = lean_ctor_get(x_608, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_608);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
}
case 8:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_631 = lean_ctor_get(x_5, 1);
lean_inc(x_631);
x_632 = lean_ctor_get(x_5, 2);
lean_inc(x_632);
x_633 = lean_ctor_get(x_5, 3);
lean_inc(x_633);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_634 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_631, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_637 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_632, x_6, x_7, x_8, x_9, x_10, x_11, x_636);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_640 = lean_unsigned_to_nat(1u);
x_641 = lean_nat_add(x_6, x_640);
lean_dec(x_6);
x_642 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_633, x_641, x_7, x_8, x_9, x_10, x_11, x_639);
if (lean_obj_tag(x_642) == 0)
{
uint8_t x_643; 
x_643 = !lean_is_exclusive(x_642);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; 
x_644 = lean_ctor_get(x_642, 0);
x_645 = lean_expr_update_let(x_5, x_635, x_638, x_644);
lean_ctor_set(x_642, 0, x_645);
return x_642;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_646 = lean_ctor_get(x_642, 0);
x_647 = lean_ctor_get(x_642, 1);
lean_inc(x_647);
lean_inc(x_646);
lean_dec(x_642);
x_648 = lean_expr_update_let(x_5, x_635, x_638, x_646);
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
uint8_t x_650; 
lean_dec(x_638);
lean_dec(x_635);
lean_dec(x_5);
x_650 = !lean_is_exclusive(x_642);
if (x_650 == 0)
{
return x_642;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_642, 0);
x_652 = lean_ctor_get(x_642, 1);
lean_inc(x_652);
lean_inc(x_651);
lean_dec(x_642);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
return x_653;
}
}
}
else
{
uint8_t x_654; 
lean_dec(x_635);
lean_dec(x_633);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_654 = !lean_is_exclusive(x_637);
if (x_654 == 0)
{
return x_637;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_637, 0);
x_656 = lean_ctor_get(x_637, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_637);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
}
else
{
uint8_t x_658; 
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_658 = !lean_is_exclusive(x_634);
if (x_658 == 0)
{
return x_634;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_634, 0);
x_660 = lean_ctor_get(x_634, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_634);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
case 10:
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_ctor_get(x_5, 1);
lean_inc(x_662);
x_663 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_662, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_663) == 0)
{
uint8_t x_664; 
x_664 = !lean_is_exclusive(x_663);
if (x_664 == 0)
{
lean_object* x_665; lean_object* x_666; 
x_665 = lean_ctor_get(x_663, 0);
x_666 = lean_expr_update_mdata(x_5, x_665);
lean_ctor_set(x_663, 0, x_666);
return x_663;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_667 = lean_ctor_get(x_663, 0);
x_668 = lean_ctor_get(x_663, 1);
lean_inc(x_668);
lean_inc(x_667);
lean_dec(x_663);
x_669 = lean_expr_update_mdata(x_5, x_667);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
else
{
uint8_t x_671; 
lean_dec(x_5);
x_671 = !lean_is_exclusive(x_663);
if (x_671 == 0)
{
return x_663;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = lean_ctor_get(x_663, 0);
x_673 = lean_ctor_get(x_663, 1);
lean_inc(x_673);
lean_inc(x_672);
lean_dec(x_663);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
return x_674;
}
}
}
case 11:
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_5, 2);
lean_inc(x_675);
x_676 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_675, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_676) == 0)
{
uint8_t x_677; 
x_677 = !lean_is_exclusive(x_676);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; 
x_678 = lean_ctor_get(x_676, 0);
x_679 = lean_expr_update_proj(x_5, x_678);
lean_ctor_set(x_676, 0, x_679);
return x_676;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_680 = lean_ctor_get(x_676, 0);
x_681 = lean_ctor_get(x_676, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_676);
x_682 = lean_expr_update_proj(x_5, x_680);
x_683 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_681);
return x_683;
}
}
else
{
uint8_t x_684; 
lean_dec(x_5);
x_684 = !lean_is_exclusive(x_676);
if (x_684 == 0)
{
return x_676;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_676, 0);
x_686 = lean_ctor_get(x_676, 1);
lean_inc(x_686);
lean_inc(x_685);
lean_dec(x_676);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
return x_687;
}
}
}
default: 
{
lean_object* x_688; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_688 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_688, 0, x_5);
lean_ctor_set(x_688, 1, x_12);
return x_688;
}
}
}
block_145:
{
lean_dec(x_13);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_16 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_expr_update_app(x_5, x_17, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_expr_update_app(x_5, x_17, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
case 6:
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_38 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_6, x_41);
lean_dec(x_6);
x_43 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_36, x_42, x_7, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = (uint8_t)((x_37 << 24) >> 61);
x_47 = lean_expr_update_lambda(x_5, x_46, x_39, x_45);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = (uint8_t)((x_37 << 24) >> 61);
x_51 = lean_expr_update_lambda(x_5, x_50, x_39, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_39);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
return x_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 7:
{
lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_64 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_61, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_6, x_67);
lean_dec(x_6);
x_69 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_62, x_68, x_7, x_8, x_9, x_10, x_11, x_66);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = (uint8_t)((x_63 << 24) >> 61);
x_73 = lean_expr_update_forall(x_5, x_72, x_65, x_71);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
x_76 = (uint8_t)((x_63 << 24) >> 61);
x_77 = lean_expr_update_forall(x_5, x_76, x_65, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_69);
if (x_79 == 0)
{
return x_69;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_62);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_64);
if (x_83 == 0)
{
return x_64;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_64, 0);
x_85 = lean_ctor_get(x_64, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_64);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_5, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_5, 3);
lean_inc(x_89);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_90 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_87, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_93 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_88, x_6, x_7, x_8, x_9, x_10, x_11, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_6, x_96);
lean_dec(x_6);
x_98 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_89, x_97, x_7, x_8, x_9, x_10, x_11, x_95);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_expr_update_let(x_5, x_91, x_94, x_100);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = lean_expr_update_let(x_5, x_91, x_94, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_5);
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
return x_98;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_98);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_93);
if (x_110 == 0)
{
return x_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get(x_93, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_93);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_90);
if (x_114 == 0)
{
return x_90;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_90, 0);
x_116 = lean_ctor_get(x_90, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_90);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_5, 1);
lean_inc(x_118);
x_119 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_118, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_expr_update_mdata(x_5, x_121);
lean_ctor_set(x_119, 0, x_122);
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
x_125 = lean_expr_update_mdata(x_5, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_dec(x_5);
x_127 = !lean_is_exclusive(x_119);
if (x_127 == 0)
{
return x_119;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_119, 0);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_119);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
case 11:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_5, 2);
lean_inc(x_131);
x_132 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_131, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_expr_update_proj(x_5, x_134);
lean_ctor_set(x_132, 0, x_135);
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_132, 0);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_132);
x_138 = lean_expr_update_proj(x_5, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_5);
x_140 = !lean_is_exclusive(x_132);
if (x_140 == 0)
{
return x_132;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
default: 
{
lean_object* x_144; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_5);
lean_ctor_set(x_144, 1, x_12);
return x_144;
}
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_KAbstract_1__kabstractAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isExprDefEq___at___private_Lean_Meta_KAbstract_1__kabstractAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* _init_l_Lean_Meta_kabstract___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_kabstract___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_kabstract___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_kabstract___rarg___closed__3() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Expr_toHeadIndex___main(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_3, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_kabstract___rarg___lambda__2___boxed), 11, 5);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_7);
lean_closure_set(x_8, 4, x_2);
x_9 = l_Lean_Meta_kabstract___rarg___closed__2;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_kabstract___rarg___closed__3;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
return x_13;
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
lean_dec(x_1);
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
