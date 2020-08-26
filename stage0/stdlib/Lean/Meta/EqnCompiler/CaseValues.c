// Lean compiler output
// Module: Lean.Meta.EqnCompiler.CaseValues
// Imports: Init Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Clear
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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__5;
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__2;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__3;
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__4;
lean_object* l_Lean_Meta_caseValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2;
extern lean_object* l_Lean_Meta_mkAppM___rarg___closed__2;
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__6;
lean_object* l_Lean_Meta_caseValue___closed__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__9;
lean_object* l_Lean_Meta_CaseValueSubgoal_inhabited;
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_caseValueAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6;
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5;
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__11;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1;
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1;
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7;
lean_object* l_Lean_Meta_caseValue___closed__6;
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__5;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__10;
lean_object* l___private_Lean_Meta_AppBuilder_20__mkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__7;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__2;
lean_object* l_Lean_Meta_caseValue___closed__3;
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM___at_Lean_Meta_caseValueAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__8(lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__5;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseValueSubgoals_inhabited;
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__8;
lean_object* l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__4;
lean_object* l_Lean_Meta_caseValueAux___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4;
lean_object* l_Lean_Meta_mkAppOptM___at_Lean_Meta_caseValueAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__1;
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_CaseValueSubgoal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_mkAppOptM___at_Lean_Meta_caseValueAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_629; 
x_8 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_629 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; uint8_t x_631; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get_uint8(x_630, sizeof(void*)*1);
lean_dec(x_630);
if (x_631 == 0)
{
lean_object* x_632; uint8_t x_633; 
x_632 = lean_ctor_get(x_629, 1);
lean_inc(x_632);
lean_dec(x_629);
x_633 = 0;
x_10 = x_633;
x_11 = x_632;
goto block_628;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; 
x_634 = lean_ctor_get(x_629, 1);
lean_inc(x_634);
lean_dec(x_629);
x_635 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_636 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_635, x_3, x_4, x_5, x_6, x_634);
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
lean_dec(x_636);
x_639 = lean_unbox(x_637);
lean_dec(x_637);
x_10 = x_639;
x_11 = x_638;
goto block_628;
}
}
else
{
uint8_t x_640; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_640 = !lean_is_exclusive(x_629);
if (x_640 == 0)
{
return x_629;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_629, 0);
x_642 = lean_ctor_get(x_629, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_629);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
block_628:
{
if (x_10 == 0)
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 2);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_63; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_23 = 0;
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_23);
x_24 = lean_st_ref_set(x_6, x_17, x_19);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_101 = lean_st_ref_get(x_4, x_25);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_st_ref_take(x_4, x_103);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_106, 0);
x_110 = l_Lean_MetavarContext_incDepth(x_109);
lean_ctor_set(x_106, 0, x_110);
x_111 = lean_st_ref_set(x_4, x_106, x_107);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_116, x_2, x_118, x_119, x_118, x_119, x_117, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_st_ref_take(x_4, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_124, 0);
lean_dec(x_127);
lean_ctor_set(x_124, 0, x_104);
x_128 = lean_st_ref_set(x_4, x_124, x_125);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
lean_dec(x_130);
lean_ctor_set(x_128, 0, x_121);
x_63 = x_128;
goto block_100;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_121);
lean_ctor_set(x_132, 1, x_131);
x_63 = x_132;
goto block_100;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_ctor_get(x_124, 1);
x_134 = lean_ctor_get(x_124, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_124);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_104);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_134);
x_136 = lean_st_ref_set(x_4, x_135, x_125);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_121);
lean_ctor_set(x_139, 1, x_137);
x_63 = x_139;
goto block_100;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_140 = lean_ctor_get(x_120, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_120, 1);
lean_inc(x_141);
lean_dec(x_120);
x_142 = lean_st_ref_take(x_4, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
lean_ctor_set(x_143, 0, x_104);
x_147 = lean_st_ref_set(x_4, x_143, x_144);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_dec(x_149);
lean_ctor_set_tag(x_147, 1);
lean_ctor_set(x_147, 0, x_140);
x_63 = x_147;
goto block_100;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_140);
lean_ctor_set(x_151, 1, x_150);
x_63 = x_151;
goto block_100;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_143, 1);
x_153 = lean_ctor_get(x_143, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_143);
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_104);
lean_ctor_set(x_154, 1, x_152);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_st_ref_set(x_4, x_154, x_144);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_140);
lean_ctor_set(x_158, 1, x_156);
x_63 = x_158;
goto block_100;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_159 = lean_ctor_get(x_113, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_113, 1);
lean_inc(x_160);
lean_dec(x_113);
x_161 = lean_st_ref_take(x_4, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = !lean_is_exclusive(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = lean_ctor_get(x_162, 0);
lean_dec(x_165);
lean_ctor_set(x_162, 0, x_104);
x_166 = lean_st_ref_set(x_4, x_162, x_163);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 0);
lean_dec(x_168);
lean_ctor_set_tag(x_166, 1);
lean_ctor_set(x_166, 0, x_159);
x_63 = x_166;
goto block_100;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_159);
lean_ctor_set(x_170, 1, x_169);
x_63 = x_170;
goto block_100;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_162, 1);
x_172 = lean_ctor_get(x_162, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_162);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_104);
lean_ctor_set(x_173, 1, x_171);
lean_ctor_set(x_173, 2, x_172);
x_174 = lean_st_ref_set(x_4, x_173, x_163);
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
x_63 = x_177;
goto block_100;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_178 = lean_ctor_get(x_106, 0);
x_179 = lean_ctor_get(x_106, 1);
x_180 = lean_ctor_get(x_106, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_106);
x_181 = l_Lean_MetavarContext_incDepth(x_178);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
lean_ctor_set(x_182, 2, x_180);
x_183 = lean_st_ref_set(x_4, x_182, x_107);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_unsigned_to_nat(0u);
x_191 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_192 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_188, x_2, x_190, x_191, x_190, x_191, x_189, x_3, x_4, x_5, x_6, x_187);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_4, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 x_200 = x_196;
} else {
 lean_dec_ref(x_196);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(0, 3, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_104);
lean_ctor_set(x_201, 1, x_198);
lean_ctor_set(x_201, 2, x_199);
x_202 = lean_st_ref_set(x_4, x_201, x_197);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_193);
lean_ctor_set(x_205, 1, x_203);
x_63 = x_205;
goto block_100;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_206 = lean_ctor_get(x_192, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_192, 1);
lean_inc(x_207);
lean_dec(x_192);
x_208 = lean_st_ref_take(x_4, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 2);
lean_inc(x_212);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 x_213 = x_209;
} else {
 lean_dec_ref(x_209);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 3, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_104);
lean_ctor_set(x_214, 1, x_211);
lean_ctor_set(x_214, 2, x_212);
x_215 = lean_st_ref_set(x_4, x_214, x_210);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
 lean_ctor_set_tag(x_218, 1);
}
lean_ctor_set(x_218, 0, x_206);
lean_ctor_set(x_218, 1, x_216);
x_63 = x_218;
goto block_100;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_219 = lean_ctor_get(x_185, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_185, 1);
lean_inc(x_220);
lean_dec(x_185);
x_221 = lean_st_ref_take(x_4, x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 2);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(0, 3, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_104);
lean_ctor_set(x_227, 1, x_224);
lean_ctor_set(x_227, 2, x_225);
x_228 = lean_st_ref_set(x_4, x_227, x_223);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
 lean_ctor_set_tag(x_231, 1);
}
lean_ctor_set(x_231, 0, x_219);
lean_ctor_set(x_231, 1, x_229);
x_63 = x_231;
goto block_100;
}
}
block_62:
{
lean_object* x_28; 
lean_inc(x_6);
x_28 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_6, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 2);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_15);
x_37 = lean_st_ref_set(x_6, x_31, x_33);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_26);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_15);
lean_ctor_set(x_31, 2, x_43);
x_44 = lean_st_ref_set(x_6, x_31, x_33);
lean_dec(x_6);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_15);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_st_ref_set(x_6, x_53, x_33);
lean_dec(x_6);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_26);
lean_dec(x_6);
x_58 = !lean_is_exclusive(x_28);
if (x_58 == 0)
{
return x_28;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_28, 0);
x_60 = lean_ctor_get(x_28, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_28);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_100:
{
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_66 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_take(x_6, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_69, 2);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_15);
x_75 = lean_st_ref_set(x_6, x_69, x_71);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_64);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
lean_dec(x_70);
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_15);
lean_ctor_set(x_69, 2, x_81);
x_82 = lean_st_ref_set(x_6, x_69, x_71);
lean_dec(x_6);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_64);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_69, 0);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_69);
x_88 = lean_ctor_get(x_70, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_89 = x_70;
} else {
 lean_dec_ref(x_70);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 1, 1);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_15);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_91, 2, x_90);
x_92 = lean_st_ref_set(x_6, x_91, x_71);
lean_dec(x_6);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_64);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_64);
x_96 = lean_ctor_get(x_66, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_66, 1);
lean_inc(x_97);
lean_dec(x_66);
x_26 = x_96;
x_27 = x_97;
goto block_62;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_63, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
lean_dec(x_63);
x_26 = x_98;
x_27 = x_99;
goto block_62;
}
}
}
else
{
lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_261; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_232 = lean_ctor_get(x_18, 0);
lean_inc(x_232);
lean_dec(x_18);
x_233 = 0;
x_234 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set_uint8(x_234, sizeof(void*)*1, x_233);
lean_ctor_set(x_17, 2, x_234);
x_235 = lean_st_ref_set(x_6, x_17, x_19);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_286 = lean_st_ref_get(x_4, x_236);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_st_ref_take(x_4, x_288);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_291, 2);
lean_inc(x_295);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 x_296 = x_291;
} else {
 lean_dec_ref(x_291);
 x_296 = lean_box(0);
}
x_297 = l_Lean_MetavarContext_incDepth(x_293);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 3, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_294);
lean_ctor_set(x_298, 2, x_295);
x_299 = lean_st_ref_set(x_4, x_298, x_292);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec(x_299);
x_301 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_300);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_ctor_get(x_302, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
lean_dec(x_302);
x_306 = lean_unsigned_to_nat(0u);
x_307 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_308 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_304, x_2, x_306, x_307, x_306, x_307, x_305, x_3, x_4, x_5, x_6, x_303);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_st_ref_take(x_4, x_310);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_312, 2);
lean_inc(x_315);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 x_316 = x_312;
} else {
 lean_dec_ref(x_312);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(0, 3, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_289);
lean_ctor_set(x_317, 1, x_314);
lean_ctor_set(x_317, 2, x_315);
x_318 = lean_st_ref_set(x_4, x_317, x_313);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_320 = x_318;
} else {
 lean_dec_ref(x_318);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_309);
lean_ctor_set(x_321, 1, x_319);
x_261 = x_321;
goto block_285;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_322 = lean_ctor_get(x_308, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_308, 1);
lean_inc(x_323);
lean_dec(x_308);
x_324 = lean_st_ref_take(x_4, x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_325, 2);
lean_inc(x_328);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 x_329 = x_325;
} else {
 lean_dec_ref(x_325);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 3, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_289);
lean_ctor_set(x_330, 1, x_327);
lean_ctor_set(x_330, 2, x_328);
x_331 = lean_st_ref_set(x_4, x_330, x_326);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
 lean_ctor_set_tag(x_334, 1);
}
lean_ctor_set(x_334, 0, x_322);
lean_ctor_set(x_334, 1, x_332);
x_261 = x_334;
goto block_285;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_335 = lean_ctor_get(x_301, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_301, 1);
lean_inc(x_336);
lean_dec(x_301);
x_337 = lean_st_ref_take(x_4, x_336);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 2);
lean_inc(x_341);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 x_342 = x_338;
} else {
 lean_dec_ref(x_338);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 3, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_289);
lean_ctor_set(x_343, 1, x_340);
lean_ctor_set(x_343, 2, x_341);
x_344 = lean_st_ref_set(x_4, x_343, x_339);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_346 = x_344;
} else {
 lean_dec_ref(x_344);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
 lean_ctor_set_tag(x_347, 1);
}
lean_ctor_set(x_347, 0, x_335);
lean_ctor_set(x_347, 1, x_345);
x_261 = x_347;
goto block_285;
}
block_260:
{
lean_object* x_239; 
lean_inc(x_6);
x_239 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = lean_st_ref_take(x_6, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_242, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
lean_dec(x_241);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 x_247 = x_242;
} else {
 lean_dec_ref(x_242);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_243, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_249 = x_243;
} else {
 lean_dec_ref(x_243);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 1, 1);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set_uint8(x_250, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_247)) {
 x_251 = lean_alloc_ctor(0, 3, 0);
} else {
 x_251 = x_247;
}
lean_ctor_set(x_251, 0, x_245);
lean_ctor_set(x_251, 1, x_246);
lean_ctor_set(x_251, 2, x_250);
x_252 = lean_st_ref_set(x_6, x_251, x_244);
lean_dec(x_6);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
 lean_ctor_set_tag(x_255, 1);
}
lean_ctor_set(x_255, 0, x_237);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_237);
lean_dec(x_6);
x_256 = lean_ctor_get(x_239, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_239, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_258 = x_239;
} else {
 lean_dec_ref(x_239);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
block_285:
{
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_264 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = lean_st_ref_take(x_6, x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_267, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
x_270 = lean_ctor_get(x_267, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 lean_ctor_release(x_267, 2);
 x_272 = x_267;
} else {
 lean_dec_ref(x_267);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_274 = x_268;
} else {
 lean_dec_ref(x_268);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(0, 1, 1);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_272)) {
 x_276 = lean_alloc_ctor(0, 3, 0);
} else {
 x_276 = x_272;
}
lean_ctor_set(x_276, 0, x_270);
lean_ctor_set(x_276, 1, x_271);
lean_ctor_set(x_276, 2, x_275);
x_277 = lean_st_ref_set(x_6, x_276, x_269);
lean_dec(x_6);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_279 = x_277;
} else {
 lean_dec_ref(x_277);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_262);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_262);
x_281 = lean_ctor_get(x_264, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_264, 1);
lean_inc(x_282);
lean_dec(x_264);
x_237 = x_281;
x_238 = x_282;
goto block_260;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_261, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_261, 1);
lean_inc(x_284);
lean_dec(x_261);
x_237 = x_283;
x_238 = x_284;
goto block_260;
}
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_381; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_348 = lean_ctor_get(x_17, 0);
x_349 = lean_ctor_get(x_17, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_17);
x_350 = lean_ctor_get(x_18, 0);
lean_inc(x_350);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_351 = x_18;
} else {
 lean_dec_ref(x_18);
 x_351 = lean_box(0);
}
x_352 = 0;
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(0, 1, 1);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set_uint8(x_353, sizeof(void*)*1, x_352);
x_354 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_354, 0, x_348);
lean_ctor_set(x_354, 1, x_349);
lean_ctor_set(x_354, 2, x_353);
x_355 = lean_st_ref_set(x_6, x_354, x_19);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
x_406 = lean_st_ref_get(x_4, x_356);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_st_ref_take(x_4, x_408);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_411, 2);
lean_inc(x_415);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 lean_ctor_release(x_411, 2);
 x_416 = x_411;
} else {
 lean_dec_ref(x_411);
 x_416 = lean_box(0);
}
x_417 = l_Lean_MetavarContext_incDepth(x_413);
if (lean_is_scalar(x_416)) {
 x_418 = lean_alloc_ctor(0, 3, 0);
} else {
 x_418 = x_416;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_414);
lean_ctor_set(x_418, 2, x_415);
x_419 = lean_st_ref_set(x_4, x_418, x_412);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_420);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_dec(x_422);
x_426 = lean_unsigned_to_nat(0u);
x_427 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_428 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_424, x_2, x_426, x_427, x_426, x_427, x_425, x_3, x_4, x_5, x_6, x_423);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_st_ref_take(x_4, x_430);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 2);
lean_inc(x_435);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 x_436 = x_432;
} else {
 lean_dec_ref(x_432);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(0, 3, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_409);
lean_ctor_set(x_437, 1, x_434);
lean_ctor_set(x_437, 2, x_435);
x_438 = lean_st_ref_set(x_4, x_437, x_433);
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_440 = x_438;
} else {
 lean_dec_ref(x_438);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_429);
lean_ctor_set(x_441, 1, x_439);
x_381 = x_441;
goto block_405;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_442 = lean_ctor_get(x_428, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_428, 1);
lean_inc(x_443);
lean_dec(x_428);
x_444 = lean_st_ref_take(x_4, x_443);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_445, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 lean_ctor_release(x_445, 2);
 x_449 = x_445;
} else {
 lean_dec_ref(x_445);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(0, 3, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_409);
lean_ctor_set(x_450, 1, x_447);
lean_ctor_set(x_450, 2, x_448);
x_451 = lean_st_ref_set(x_4, x_450, x_446);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_453 = x_451;
} else {
 lean_dec_ref(x_451);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
 lean_ctor_set_tag(x_454, 1);
}
lean_ctor_set(x_454, 0, x_442);
lean_ctor_set(x_454, 1, x_452);
x_381 = x_454;
goto block_405;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_455 = lean_ctor_get(x_421, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_421, 1);
lean_inc(x_456);
lean_dec(x_421);
x_457 = lean_st_ref_take(x_4, x_456);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_458, 2);
lean_inc(x_461);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 lean_ctor_release(x_458, 2);
 x_462 = x_458;
} else {
 lean_dec_ref(x_458);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(0, 3, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_409);
lean_ctor_set(x_463, 1, x_460);
lean_ctor_set(x_463, 2, x_461);
x_464 = lean_st_ref_set(x_4, x_463, x_459);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
 lean_ctor_set_tag(x_467, 1);
}
lean_ctor_set(x_467, 0, x_455);
lean_ctor_set(x_467, 1, x_465);
x_381 = x_467;
goto block_405;
}
block_380:
{
lean_object* x_359; 
lean_inc(x_6);
x_359 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_358);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec(x_359);
x_361 = lean_st_ref_take(x_6, x_360);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_362, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_361, 1);
lean_inc(x_364);
lean_dec(x_361);
x_365 = lean_ctor_get(x_362, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 x_367 = x_362;
} else {
 lean_dec_ref(x_362);
 x_367 = lean_box(0);
}
x_368 = lean_ctor_get(x_363, 0);
lean_inc(x_368);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_369 = x_363;
} else {
 lean_dec_ref(x_363);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 1, 1);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_367)) {
 x_371 = lean_alloc_ctor(0, 3, 0);
} else {
 x_371 = x_367;
}
lean_ctor_set(x_371, 0, x_365);
lean_ctor_set(x_371, 1, x_366);
lean_ctor_set(x_371, 2, x_370);
x_372 = lean_st_ref_set(x_6, x_371, x_364);
lean_dec(x_6);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
 lean_ctor_set_tag(x_375, 1);
}
lean_ctor_set(x_375, 0, x_357);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_357);
lean_dec(x_6);
x_376 = lean_ctor_get(x_359, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_359, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_378 = x_359;
} else {
 lean_dec_ref(x_359);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
block_405:
{
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_384 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_383);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
x_386 = lean_st_ref_take(x_6, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_387, 2);
lean_inc(x_388);
x_389 = lean_ctor_get(x_386, 1);
lean_inc(x_389);
lean_dec(x_386);
x_390 = lean_ctor_get(x_387, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_387, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 x_392 = x_387;
} else {
 lean_dec_ref(x_387);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_388, 0);
lean_inc(x_393);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 x_394 = x_388;
} else {
 lean_dec_ref(x_388);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(0, 1, 1);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set_uint8(x_395, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_392)) {
 x_396 = lean_alloc_ctor(0, 3, 0);
} else {
 x_396 = x_392;
}
lean_ctor_set(x_396, 0, x_390);
lean_ctor_set(x_396, 1, x_391);
lean_ctor_set(x_396, 2, x_395);
x_397 = lean_st_ref_set(x_6, x_396, x_389);
lean_dec(x_6);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_382);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_382);
x_401 = lean_ctor_get(x_384, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_384, 1);
lean_inc(x_402);
lean_dec(x_384);
x_357 = x_401;
x_358 = x_402;
goto block_380;
}
}
else
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_381, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_381, 1);
lean_inc(x_404);
lean_dec(x_381);
x_357 = x_403;
x_358 = x_404;
goto block_380;
}
}
}
}
else
{
uint8_t x_468; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_468 = !lean_is_exclusive(x_12);
if (x_468 == 0)
{
return x_12;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_12, 0);
x_470 = lean_ctor_get(x_12, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_12);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
else
{
lean_object* x_472; 
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_472 = l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1(x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_493 = lean_st_ref_get(x_4, x_474);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_st_ref_take(x_4, x_495);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = !lean_is_exclusive(x_498);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_501 = lean_ctor_get(x_498, 0);
x_502 = l_Lean_MetavarContext_incDepth(x_501);
lean_ctor_set(x_498, 0, x_502);
x_503 = lean_st_ref_set(x_4, x_498, x_499);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
lean_dec(x_503);
x_505 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
lean_dec(x_506);
x_510 = lean_unsigned_to_nat(0u);
x_511 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_512 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_508, x_2, x_510, x_511, x_510, x_511, x_509, x_3, x_4, x_5, x_6, x_507);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = lean_st_ref_take(x_4, x_514);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = !lean_is_exclusive(x_516);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_519 = lean_ctor_get(x_516, 0);
lean_dec(x_519);
lean_ctor_set(x_516, 0, x_496);
x_520 = lean_st_ref_set(x_4, x_516, x_517);
x_521 = !lean_is_exclusive(x_520);
if (x_521 == 0)
{
lean_object* x_522; 
x_522 = lean_ctor_get(x_520, 0);
lean_dec(x_522);
lean_ctor_set(x_520, 0, x_513);
x_475 = x_520;
goto block_492;
}
else
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
lean_dec(x_520);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_513);
lean_ctor_set(x_524, 1, x_523);
x_475 = x_524;
goto block_492;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_525 = lean_ctor_get(x_516, 1);
x_526 = lean_ctor_get(x_516, 2);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_516);
x_527 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_527, 0, x_496);
lean_ctor_set(x_527, 1, x_525);
lean_ctor_set(x_527, 2, x_526);
x_528 = lean_st_ref_set(x_4, x_527, x_517);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_530 = x_528;
} else {
 lean_dec_ref(x_528);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_513);
lean_ctor_set(x_531, 1, x_529);
x_475 = x_531;
goto block_492;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; 
x_532 = lean_ctor_get(x_512, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_512, 1);
lean_inc(x_533);
lean_dec(x_512);
x_534 = lean_st_ref_take(x_4, x_533);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = !lean_is_exclusive(x_535);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; uint8_t x_540; 
x_538 = lean_ctor_get(x_535, 0);
lean_dec(x_538);
lean_ctor_set(x_535, 0, x_496);
x_539 = lean_st_ref_set(x_4, x_535, x_536);
x_540 = !lean_is_exclusive(x_539);
if (x_540 == 0)
{
lean_object* x_541; 
x_541 = lean_ctor_get(x_539, 0);
lean_dec(x_541);
lean_ctor_set_tag(x_539, 1);
lean_ctor_set(x_539, 0, x_532);
x_475 = x_539;
goto block_492;
}
else
{
lean_object* x_542; lean_object* x_543; 
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_532);
lean_ctor_set(x_543, 1, x_542);
x_475 = x_543;
goto block_492;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_544 = lean_ctor_get(x_535, 1);
x_545 = lean_ctor_get(x_535, 2);
lean_inc(x_545);
lean_inc(x_544);
lean_dec(x_535);
x_546 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_546, 0, x_496);
lean_ctor_set(x_546, 1, x_544);
lean_ctor_set(x_546, 2, x_545);
x_547 = lean_st_ref_set(x_4, x_546, x_536);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_549 = x_547;
} else {
 lean_dec_ref(x_547);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
 lean_ctor_set_tag(x_550, 1);
}
lean_ctor_set(x_550, 0, x_532);
lean_ctor_set(x_550, 1, x_548);
x_475 = x_550;
goto block_492;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; 
x_551 = lean_ctor_get(x_505, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_505, 1);
lean_inc(x_552);
lean_dec(x_505);
x_553 = lean_st_ref_take(x_4, x_552);
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = !lean_is_exclusive(x_554);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_557 = lean_ctor_get(x_554, 0);
lean_dec(x_557);
lean_ctor_set(x_554, 0, x_496);
x_558 = lean_st_ref_set(x_4, x_554, x_555);
x_559 = !lean_is_exclusive(x_558);
if (x_559 == 0)
{
lean_object* x_560; 
x_560 = lean_ctor_get(x_558, 0);
lean_dec(x_560);
lean_ctor_set_tag(x_558, 1);
lean_ctor_set(x_558, 0, x_551);
x_475 = x_558;
goto block_492;
}
else
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_dec(x_558);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_551);
lean_ctor_set(x_562, 1, x_561);
x_475 = x_562;
goto block_492;
}
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_563 = lean_ctor_get(x_554, 1);
x_564 = lean_ctor_get(x_554, 2);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_554);
x_565 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_565, 0, x_496);
lean_ctor_set(x_565, 1, x_563);
lean_ctor_set(x_565, 2, x_564);
x_566 = lean_st_ref_set(x_4, x_565, x_555);
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_568 = x_566;
} else {
 lean_dec_ref(x_566);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
 lean_ctor_set_tag(x_569, 1);
}
lean_ctor_set(x_569, 0, x_551);
lean_ctor_set(x_569, 1, x_567);
x_475 = x_569;
goto block_492;
}
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_570 = lean_ctor_get(x_498, 0);
x_571 = lean_ctor_get(x_498, 1);
x_572 = lean_ctor_get(x_498, 2);
lean_inc(x_572);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_498);
x_573 = l_Lean_MetavarContext_incDepth(x_570);
x_574 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_571);
lean_ctor_set(x_574, 2, x_572);
x_575 = lean_st_ref_set(x_4, x_574, x_499);
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
lean_dec(x_575);
x_577 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_576);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_580 = lean_ctor_get(x_578, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_578, 1);
lean_inc(x_581);
lean_dec(x_578);
x_582 = lean_unsigned_to_nat(0u);
x_583 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_584 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_580, x_2, x_582, x_583, x_582, x_583, x_581, x_3, x_4, x_5, x_6, x_579);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
x_587 = lean_st_ref_take(x_4, x_586);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
x_591 = lean_ctor_get(x_588, 2);
lean_inc(x_591);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 lean_ctor_release(x_588, 2);
 x_592 = x_588;
} else {
 lean_dec_ref(x_588);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(0, 3, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_496);
lean_ctor_set(x_593, 1, x_590);
lean_ctor_set(x_593, 2, x_591);
x_594 = lean_st_ref_set(x_4, x_593, x_589);
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_596 = x_594;
} else {
 lean_dec_ref(x_594);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_585);
lean_ctor_set(x_597, 1, x_595);
x_475 = x_597;
goto block_492;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_598 = lean_ctor_get(x_584, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_584, 1);
lean_inc(x_599);
lean_dec(x_584);
x_600 = lean_st_ref_take(x_4, x_599);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
x_604 = lean_ctor_get(x_601, 2);
lean_inc(x_604);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 lean_ctor_release(x_601, 2);
 x_605 = x_601;
} else {
 lean_dec_ref(x_601);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(0, 3, 0);
} else {
 x_606 = x_605;
}
lean_ctor_set(x_606, 0, x_496);
lean_ctor_set(x_606, 1, x_603);
lean_ctor_set(x_606, 2, x_604);
x_607 = lean_st_ref_set(x_4, x_606, x_602);
x_608 = lean_ctor_get(x_607, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_609 = x_607;
} else {
 lean_dec_ref(x_607);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_610 = x_609;
 lean_ctor_set_tag(x_610, 1);
}
lean_ctor_set(x_610, 0, x_598);
lean_ctor_set(x_610, 1, x_608);
x_475 = x_610;
goto block_492;
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_611 = lean_ctor_get(x_577, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_577, 1);
lean_inc(x_612);
lean_dec(x_577);
x_613 = lean_st_ref_take(x_4, x_612);
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
x_617 = lean_ctor_get(x_614, 2);
lean_inc(x_617);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 lean_ctor_release(x_614, 2);
 x_618 = x_614;
} else {
 lean_dec_ref(x_614);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 3, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_496);
lean_ctor_set(x_619, 1, x_616);
lean_ctor_set(x_619, 2, x_617);
x_620 = lean_st_ref_set(x_4, x_619, x_615);
x_621 = lean_ctor_get(x_620, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_622 = x_620;
} else {
 lean_dec_ref(x_620);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_623 = x_622;
 lean_ctor_set_tag(x_623, 1);
}
lean_ctor_set(x_623, 0, x_611);
lean_ctor_set(x_623, 1, x_621);
x_475 = x_623;
goto block_492;
}
}
block_492:
{
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_479 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_473, x_478, x_3, x_4, x_5, x_6, x_477);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_480 = !lean_is_exclusive(x_479);
if (x_480 == 0)
{
lean_object* x_481; 
x_481 = lean_ctor_get(x_479, 0);
lean_dec(x_481);
lean_ctor_set(x_479, 0, x_476);
return x_479;
}
else
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_ctor_get(x_479, 1);
lean_inc(x_482);
lean_dec(x_479);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_476);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_484 = lean_ctor_get(x_475, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_475, 1);
lean_inc(x_485);
lean_dec(x_475);
x_486 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_487 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_473, x_486, x_3, x_4, x_5, x_6, x_485);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_488 = !lean_is_exclusive(x_487);
if (x_488 == 0)
{
lean_object* x_489; 
x_489 = lean_ctor_get(x_487, 0);
lean_dec(x_489);
lean_ctor_set_tag(x_487, 1);
lean_ctor_set(x_487, 0, x_484);
return x_487;
}
else
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_dec(x_487);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_484);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
}
}
}
else
{
uint8_t x_624; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_624 = !lean_is_exclusive(x_472);
if (x_624 == 0)
{
return x_472;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_472, 0);
x_626 = lean_ctor_get(x_472, 1);
lean_inc(x_626);
lean_inc(x_625);
lean_dec(x_472);
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_625);
lean_ctor_set(x_627, 1, x_626);
return x_627;
}
}
}
}
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst domain: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Meta_FVarSubst_domain(x_1);
x_12 = l_List_toString___at_Lean_Meta_substCore___spec__8(x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_caseValueAux___lambda__1___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_2, x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("found decl");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("searching for decl");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_47; 
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_2);
x_12 = l_Lean_Expr_fvarId_x21(x_11);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_13 = x_50;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
lean_inc(x_4);
x_52 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_4, x_6, x_7, x_8, x_9, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_13 = x_55;
goto block_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = l_Lean_Meta_caseValueAux___lambda__2___closed__6;
lean_inc(x_4);
x_58 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_4, x_57, x_6, x_7, x_8, x_9, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_13 = x_59;
goto block_46;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
block_46:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
lean_inc(x_4);
x_26 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_4, x_6, x_7, x_8, x_9, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Meta_caseValueAux___lambda__2___closed__3;
x_37 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_4, x_36, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("caseValue");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__3___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dite");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__3___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__3___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = l_Lean_Meta_caseValueAux___lambda__3___closed__10;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_caseValueAux___lambda__3___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_1);
x_15 = l_Lean_Meta_getMVarType(x_1, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_mkFVar(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_18, x_3, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_caseValueAux___lambda__3___closed__5;
lean_inc(x_20);
x_23 = l_Lean_mkApp(x_22, x_20);
x_24 = 0;
lean_inc(x_16);
lean_inc(x_20);
x_25 = l_Lean_mkForall(x_4, x_24, x_20, x_16);
x_26 = l_Lean_mkForall(x_4, x_24, x_23, x_16);
lean_inc(x_6);
x_27 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_25, x_6, x_7, x_8, x_9, x_10, x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_26, x_6, x_7, x_8, x_9, x_10, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_20);
lean_inc(x_28);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_28);
lean_inc(x_31);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_37 = l_Lean_Meta_caseValueAux___lambda__3___closed__9;
x_38 = lean_array_push(x_37, x_34);
x_39 = lean_array_push(x_38, x_33);
x_40 = lean_array_push(x_39, x_35);
x_41 = lean_array_push(x_40, x_36);
x_42 = l_Lean_Meta_caseValueAux___lambda__3___closed__7;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_43 = l_Lean_Meta_mkAppOptM___at_Lean_Meta_caseValueAux___spec__1(x_42, x_41, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_1, x_44, x_7, x_8, x_9, x_10, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Expr_mvarId_x21(x_31);
lean_dec(x_31);
x_49 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_50 = l_Lean_Meta_intro1(x_48, x_49, x_7, x_8, x_9, x_10, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
lean_inc(x_5);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_5);
x_56 = l_Lean_Expr_mvarId_x21(x_28);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = l_Lean_Meta_intro1(x_56, x_49, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_60);
x_62 = l_Lean_Meta_substCore(x_61, x_60, x_49, x_5, x_49, x_7, x_8, x_9, x_10, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
x_68 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
x_70 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_inc(x_66);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__1___boxed), 8, 2);
lean_closure_set(x_71, 0, x_66);
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_caseValueAux___lambda__3___closed__11;
x_73 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_73, 0, x_72);
lean_closure_set(x_73, 1, x_71);
lean_inc(x_60);
lean_inc(x_66);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__2___boxed), 10, 4);
lean_closure_set(x_74, 0, x_66);
lean_closure_set(x_74, 1, x_60);
lean_closure_set(x_74, 2, x_69);
lean_closure_set(x_74, 3, x_70);
x_75 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_75, 0, x_73);
lean_closure_set(x_75, 1, x_74);
lean_inc(x_67);
x_76 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_67, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 4);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_79, x_80, x_75, x_7, x_8, x_9, x_10, x_78);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = l_Lean_Meta_FVarSubst_get(x_66, x_60);
x_85 = l_Lean_Expr_fvarId_x21(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_67);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_66);
lean_ctor_set(x_63, 1, x_55);
lean_ctor_set(x_63, 0, x_86);
lean_ctor_set(x_81, 0, x_63);
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = l_Lean_Meta_FVarSubst_get(x_66, x_60);
x_89 = l_Lean_Expr_fvarId_x21(x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_67);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_66);
lean_ctor_set(x_63, 1, x_55);
lean_ctor_set(x_63, 0, x_90);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_63);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_free_object(x_63);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_55);
x_92 = !lean_is_exclusive(x_81);
if (x_92 == 0)
{
return x_81;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_81, 0);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_81);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_75);
lean_free_object(x_63);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = !lean_is_exclusive(x_76);
if (x_96 == 0)
{
return x_76;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_76, 0);
x_98 = lean_ctor_get(x_76, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_76);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_63, 0);
x_101 = lean_ctor_get(x_63, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_63);
x_102 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
x_104 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_inc(x_100);
x_105 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__1___boxed), 8, 2);
lean_closure_set(x_105, 0, x_100);
lean_closure_set(x_105, 1, x_104);
x_106 = l_Lean_Meta_caseValueAux___lambda__3___closed__11;
x_107 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_107, 0, x_106);
lean_closure_set(x_107, 1, x_105);
lean_inc(x_60);
lean_inc(x_100);
x_108 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__2___boxed), 10, 4);
lean_closure_set(x_108, 0, x_100);
lean_closure_set(x_108, 1, x_60);
lean_closure_set(x_108, 2, x_103);
lean_closure_set(x_108, 3, x_104);
x_109 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_109, 0, x_107);
lean_closure_set(x_109, 1, x_108);
lean_inc(x_101);
x_110 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_101, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 4);
lean_inc(x_114);
lean_dec(x_111);
x_115 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_113, x_114, x_109, x_7, x_8, x_9, x_10, x_112);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = l_Lean_Meta_FVarSubst_get(x_100, x_60);
x_119 = l_Lean_Expr_fvarId_x21(x_118);
lean_dec(x_118);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_101);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_100);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_55);
if (lean_is_scalar(x_117)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_117;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_60);
lean_dec(x_55);
x_123 = lean_ctor_get(x_115, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_125 = x_115;
} else {
 lean_dec_ref(x_115);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_109);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_60);
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_127 = lean_ctor_get(x_110, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_110, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_129 = x_110;
} else {
 lean_dec_ref(x_110);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_60);
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_131 = !lean_is_exclusive(x_62);
if (x_131 == 0)
{
return x_62;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_62, 0);
x_133 = lean_ctor_get(x_62, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_62);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_135 = !lean_is_exclusive(x_57);
if (x_135 == 0)
{
return x_57;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_57, 0);
x_137 = lean_ctor_get(x_57, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_57);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_139 = !lean_is_exclusive(x_50);
if (x_139 == 0)
{
return x_50;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_50, 0);
x_141 = lean_ctor_get(x_50, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_50);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_43);
if (x_143 == 0)
{
return x_43;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_43, 0);
x_145 = lean_ctor_get(x_43, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_43);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_19);
if (x_147 == 0)
{
return x_19;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_19, 0);
x_149 = lean_ctor_get(x_19, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_19);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_15);
if (x_151 == 0)
{
return x_15;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_15, 0);
x_153 = lean_ctor_get(x_15, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_15);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_13);
if (x_155 == 0)
{
return x_13;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_13, 0);
x_157 = lean_ctor_get(x_13, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_13);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
lean_object* l_Lean_Meta_caseValueAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__3___boxed), 11, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 4);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_17, x_18, x_13, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_mkAppOptM___at_Lean_Meta_caseValueAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppOptM___at_Lean_Meta_caseValueAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_caseValueAux___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_caseValueAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_caseValueAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("thenBranch");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elseBranch");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_caseValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_caseValueAux(x_1, x_2, x_3, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_caseValue___closed__4;
x_17 = l_Lean_Meta_appendTagSuffix(x_15, x_16, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Meta_caseValue___closed__6;
x_22 = l_Lean_Meta_appendTagSuffix(x_20, x_21, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
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
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_CaseValueSubgoals_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Meta_FVarSubst_get(x_17, x_14);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_tryClear(x_5, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_16;
x_5 = x_21;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_dec(x_18);
x_4 = x_16;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("caseValues");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("list of values must not be empty");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2;
x_14 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_13, x_4, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l_Lean_Name_appendIndexAfter(x_1, x_3);
x_20 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_21 = l_Lean_Meta_caseValueAux(x_4, x_2, x_17, x_19, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 2);
lean_inc(x_28);
x_29 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7;
lean_inc(x_3);
x_30 = l_Lean_Name_appendIndexAfter(x_29, x_3);
lean_inc(x_26);
x_31 = l_Lean_Meta_appendTagSuffix(x_26, x_30, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_34 = l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(x_6, x_23, x_6, x_33, x_26, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_mkOptionalNode___closed__2;
x_38 = lean_array_push(x_37, x_27);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_28);
x_40 = lean_array_push(x_7, x_39);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_45 = l_Lean_Name_appendIndexAfter(x_29, x_44);
lean_inc(x_41);
x_46 = l_Lean_Meta_appendTagSuffix(x_41, x_45, x_8, x_9, x_10, x_11, x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_array_push(x_6, x_42);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_20);
x_51 = lean_array_push(x_40, x_50);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_array_push(x_6, x_42);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_20);
x_55 = lean_array_push(x_40, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_3, x_61);
lean_dec(x_3);
x_63 = lean_ctor_get(x_25, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_dec(x_25);
x_65 = lean_array_push(x_6, x_64);
x_3 = x_62;
x_4 = x_63;
x_5 = x_18;
x_6 = x_65;
x_7 = x_40;
x_12 = x_36;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
return x_34;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_34, 0);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_34);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_31);
if (x_71 == 0)
{
return x_31;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_31, 0);
x_73 = lean_ctor_get(x_31, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_31);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_caseValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_toList___rarg(x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(x_4, x_2, x_11, x_1, x_10, x_12, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Meta_caseValues___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_caseValues(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_EqnCompiler_CaseValues(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1 = _init_l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1);
l_Lean_Meta_CaseValueSubgoal_inhabited = _init_l_Lean_Meta_CaseValueSubgoal_inhabited();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoal_inhabited);
l_Lean_Meta_caseValueAux___lambda__1___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__1);
l_Lean_Meta_caseValueAux___lambda__1___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__2);
l_Lean_Meta_caseValueAux___lambda__1___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__1___closed__3);
l_Lean_Meta_caseValueAux___lambda__2___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__1);
l_Lean_Meta_caseValueAux___lambda__2___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__2);
l_Lean_Meta_caseValueAux___lambda__2___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__3);
l_Lean_Meta_caseValueAux___lambda__2___closed__4 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__4);
l_Lean_Meta_caseValueAux___lambda__2___closed__5 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__5);
l_Lean_Meta_caseValueAux___lambda__2___closed__6 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__6);
l_Lean_Meta_caseValueAux___lambda__3___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__1);
l_Lean_Meta_caseValueAux___lambda__3___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__2);
l_Lean_Meta_caseValueAux___lambda__3___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__3);
l_Lean_Meta_caseValueAux___lambda__3___closed__4 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__4);
l_Lean_Meta_caseValueAux___lambda__3___closed__5 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__5);
l_Lean_Meta_caseValueAux___lambda__3___closed__6 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__6);
l_Lean_Meta_caseValueAux___lambda__3___closed__7 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__7);
l_Lean_Meta_caseValueAux___lambda__3___closed__8 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__8);
l_Lean_Meta_caseValueAux___lambda__3___closed__9 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__9);
l_Lean_Meta_caseValueAux___lambda__3___closed__10 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__10);
l_Lean_Meta_caseValueAux___lambda__3___closed__11 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__11);
l_Lean_Meta_caseValue___closed__1 = _init_l_Lean_Meta_caseValue___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__1);
l_Lean_Meta_caseValue___closed__2 = _init_l_Lean_Meta_caseValue___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__2);
l_Lean_Meta_caseValue___closed__3 = _init_l_Lean_Meta_caseValue___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__3);
l_Lean_Meta_caseValue___closed__4 = _init_l_Lean_Meta_caseValue___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__4);
l_Lean_Meta_caseValue___closed__5 = _init_l_Lean_Meta_caseValue___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__5);
l_Lean_Meta_caseValue___closed__6 = _init_l_Lean_Meta_caseValue___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__6);
l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1 = _init_l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1);
l_Lean_Meta_CaseValueSubgoals_inhabited = _init_l_Lean_Meta_CaseValueSubgoals_inhabited();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoals_inhabited);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
