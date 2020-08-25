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
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_522; 
x_8 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_522 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; uint8_t x_524; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get_uint8(x_523, sizeof(void*)*1);
lean_dec(x_523);
if (x_524 == 0)
{
lean_object* x_525; uint8_t x_526; 
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_dec(x_522);
x_526 = 0;
x_10 = x_526;
x_11 = x_525;
goto block_521;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; 
x_527 = lean_ctor_get(x_522, 1);
lean_inc(x_527);
lean_dec(x_522);
x_528 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_529 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_528, x_3, x_4, x_5, x_6, x_527);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_unbox(x_530);
lean_dec(x_530);
x_10 = x_532;
x_11 = x_531;
goto block_521;
}
}
else
{
uint8_t x_533; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_533 = !lean_is_exclusive(x_522);
if (x_533 == 0)
{
return x_522;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_522, 0);
x_535 = lean_ctor_get(x_522, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_522);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
return x_536;
}
}
block_521:
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
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_23 = 0;
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_23);
x_24 = lean_st_ref_set(x_6, x_17, x_19);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_63 = lean_st_ref_get(x_4, x_25);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_147 = lean_st_ref_take(x_4, x_65);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = !lean_is_exclusive(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_148, 0);
x_152 = l_Lean_MetavarContext_incDepth(x_151);
lean_ctor_set(x_148, 0, x_152);
x_153 = lean_st_ref_set(x_4, x_148, x_149);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_unsigned_to_nat(0u);
x_161 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_162 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_158, x_2, x_160, x_161, x_160, x_161, x_159, x_3, x_4, x_5, x_6, x_157);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_163);
x_67 = x_165;
x_68 = x_164;
goto block_146;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
lean_dec(x_162);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_166);
x_67 = x_168;
x_68 = x_167;
goto block_146;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_155, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_155, 1);
lean_inc(x_170);
lean_dec(x_155);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_169);
x_67 = x_171;
x_68 = x_170;
goto block_146;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_172 = lean_ctor_get(x_148, 0);
x_173 = lean_ctor_get(x_148, 1);
x_174 = lean_ctor_get(x_148, 2);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_148);
x_175 = l_Lean_MetavarContext_incDepth(x_172);
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
lean_ctor_set(x_176, 2, x_174);
x_177 = lean_st_ref_set(x_4, x_176, x_149);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_unsigned_to_nat(0u);
x_185 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_186 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_182, x_2, x_184, x_185, x_184, x_185, x_183, x_3, x_4, x_5, x_6, x_181);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_187);
x_67 = x_189;
x_68 = x_188;
goto block_146;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_dec(x_186);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_190);
x_67 = x_192;
x_68 = x_191;
goto block_146;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_179, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_179, 1);
lean_inc(x_194);
lean_dec(x_179);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_193);
x_67 = x_195;
x_68 = x_194;
goto block_146;
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
block_146:
{
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_take(x_4, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 0);
lean_dec(x_74);
lean_ctor_set(x_71, 0, x_66);
x_75 = lean_st_ref_set(x_4, x_71, x_72);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_26 = x_69;
x_27 = x_76;
goto block_62;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_71, 1);
x_78 = lean_ctor_get(x_71, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
x_80 = lean_st_ref_set(x_4, x_79, x_72);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_26 = x_69;
x_27 = x_81;
goto block_62;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_67, 0);
lean_inc(x_82);
lean_dec(x_67);
x_83 = lean_st_ref_take(x_4, x_68);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_66);
x_88 = lean_st_ref_set(x_4, x_84, x_85);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_take(x_6, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_93, 2);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_15);
x_99 = lean_st_ref_set(x_6, x_93, x_95);
lean_dec(x_6);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
lean_ctor_set(x_99, 0, x_82);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_82);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_94, 0);
lean_inc(x_104);
lean_dec(x_94);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_15);
lean_ctor_set(x_93, 2, x_105);
x_106 = lean_st_ref_set(x_6, x_93, x_95);
lean_dec(x_6);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_82);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_110 = lean_ctor_get(x_93, 0);
x_111 = lean_ctor_get(x_93, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_93);
x_112 = lean_ctor_get(x_94, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_113 = x_94;
} else {
 lean_dec_ref(x_94);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 1, 1);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_15);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_115, 2, x_114);
x_116 = lean_st_ref_set(x_6, x_115, x_95);
lean_dec(x_6);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_82);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_82);
x_120 = lean_ctor_get(x_90, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_90, 1);
lean_inc(x_121);
lean_dec(x_90);
x_26 = x_120;
x_27 = x_121;
goto block_62;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_84, 1);
x_123 = lean_ctor_get(x_84, 2);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_84);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_66);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_123);
x_125 = lean_st_ref_set(x_4, x_124, x_85);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_127 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_take(x_6, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 3, 0);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_138);
x_140 = lean_st_ref_set(x_6, x_139, x_132);
lean_dec(x_6);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_82);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_82);
x_144 = lean_ctor_get(x_127, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_127, 1);
lean_inc(x_145);
lean_dec(x_127);
x_26 = x_144;
x_27 = x_145;
goto block_62;
}
}
}
}
}
else
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_196 = lean_ctor_get(x_18, 0);
lean_inc(x_196);
lean_dec(x_18);
x_197 = 0;
x_198 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_197);
lean_ctor_set(x_17, 2, x_198);
x_199 = lean_st_ref_set(x_6, x_17, x_19);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_225 = lean_st_ref_get(x_4, x_200);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
lean_dec(x_226);
x_271 = lean_st_ref_take(x_4, x_227);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 2);
lean_inc(x_276);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 x_277 = x_272;
} else {
 lean_dec_ref(x_272);
 x_277 = lean_box(0);
}
x_278 = l_Lean_MetavarContext_incDepth(x_274);
if (lean_is_scalar(x_277)) {
 x_279 = lean_alloc_ctor(0, 3, 0);
} else {
 x_279 = x_277;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_275);
lean_ctor_set(x_279, 2, x_276);
x_280 = lean_st_ref_set(x_4, x_279, x_273);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_282 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_unsigned_to_nat(0u);
x_288 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_289 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_285, x_2, x_287, x_288, x_287, x_288, x_286, x_3, x_4, x_5, x_6, x_284);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_290);
x_229 = x_292;
x_230 = x_291;
goto block_270;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_289, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_289, 1);
lean_inc(x_294);
lean_dec(x_289);
x_295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_295, 0, x_293);
x_229 = x_295;
x_230 = x_294;
goto block_270;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_282, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_282, 1);
lean_inc(x_297);
lean_dec(x_282);
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_296);
x_229 = x_298;
x_230 = x_297;
goto block_270;
}
block_224:
{
lean_object* x_203; 
lean_inc(x_6);
x_203 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_st_ref_take(x_6, x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_206, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_207, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_213 = x_207;
} else {
 lean_dec_ref(x_207);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 1, 1);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_211)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_211;
}
lean_ctor_set(x_215, 0, x_209);
lean_ctor_set(x_215, 1, x_210);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_st_ref_set(x_6, x_215, x_208);
lean_dec(x_6);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_218 = x_216;
} else {
 lean_dec_ref(x_216);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
 lean_ctor_set_tag(x_219, 1);
}
lean_ctor_set(x_219, 0, x_201);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_201);
lean_dec(x_6);
x_220 = lean_ctor_get(x_203, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_203, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_222 = x_203;
} else {
 lean_dec_ref(x_203);
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
block_270:
{
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_st_ref_take(x_4, x_230);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 2);
lean_inc(x_236);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 x_237 = x_233;
} else {
 lean_dec_ref(x_233);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 3, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_228);
lean_ctor_set(x_238, 1, x_235);
lean_ctor_set(x_238, 2, x_236);
x_239 = lean_st_ref_set(x_4, x_238, x_234);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_201 = x_231;
x_202 = x_240;
goto block_224;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_241 = lean_ctor_get(x_229, 0);
lean_inc(x_241);
lean_dec(x_229);
x_242 = lean_st_ref_take(x_4, x_230);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 2);
lean_inc(x_246);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_247 = x_243;
} else {
 lean_dec_ref(x_243);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 3, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_228);
lean_ctor_set(x_248, 1, x_245);
lean_ctor_set(x_248, 2, x_246);
x_249 = lean_st_ref_set(x_4, x_248, x_244);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_251 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_253 = lean_st_ref_take(x_6, x_252);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_254, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_254, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 x_259 = x_254;
} else {
 lean_dec_ref(x_254);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_255, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_261 = x_255;
} else {
 lean_dec_ref(x_255);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(0, 1, 1);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set_uint8(x_262, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_259)) {
 x_263 = lean_alloc_ctor(0, 3, 0);
} else {
 x_263 = x_259;
}
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_258);
lean_ctor_set(x_263, 2, x_262);
x_264 = lean_st_ref_set(x_6, x_263, x_256);
lean_dec(x_6);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_241);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_241);
x_268 = lean_ctor_get(x_251, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_251, 1);
lean_inc(x_269);
lean_dec(x_251);
x_201 = x_268;
x_202 = x_269;
goto block_224;
}
}
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_299 = lean_ctor_get(x_17, 0);
x_300 = lean_ctor_get(x_17, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_17);
x_301 = lean_ctor_get(x_18, 0);
lean_inc(x_301);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_302 = x_18;
} else {
 lean_dec_ref(x_18);
 x_302 = lean_box(0);
}
x_303 = 0;
if (lean_is_scalar(x_302)) {
 x_304 = lean_alloc_ctor(0, 1, 1);
} else {
 x_304 = x_302;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set_uint8(x_304, sizeof(void*)*1, x_303);
x_305 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_305, 0, x_299);
lean_ctor_set(x_305, 1, x_300);
lean_ctor_set(x_305, 2, x_304);
x_306 = lean_st_ref_set(x_6, x_305, x_19);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_332 = lean_st_ref_get(x_4, x_307);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
lean_dec(x_333);
x_378 = lean_st_ref_take(x_4, x_334);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_379, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 x_384 = x_379;
} else {
 lean_dec_ref(x_379);
 x_384 = lean_box(0);
}
x_385 = l_Lean_MetavarContext_incDepth(x_381);
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(0, 3, 0);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set(x_386, 2, x_383);
x_387 = lean_st_ref_set(x_4, x_386, x_380);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_ctor_get(x_390, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_390, 1);
lean_inc(x_393);
lean_dec(x_390);
x_394 = lean_unsigned_to_nat(0u);
x_395 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_396 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_392, x_2, x_394, x_395, x_394, x_395, x_393, x_3, x_4, x_5, x_6, x_391);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_397);
x_336 = x_399;
x_337 = x_398;
goto block_377;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_396, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_396, 1);
lean_inc(x_401);
lean_dec(x_396);
x_402 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_402, 0, x_400);
x_336 = x_402;
x_337 = x_401;
goto block_377;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_389, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_389, 1);
lean_inc(x_404);
lean_dec(x_389);
x_405 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_405, 0, x_403);
x_336 = x_405;
x_337 = x_404;
goto block_377;
}
block_331:
{
lean_object* x_310; 
lean_inc(x_6);
x_310 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_309);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_st_ref_take(x_6, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 2);
lean_inc(x_314);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
lean_dec(x_312);
x_316 = lean_ctor_get(x_313, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_313, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 x_318 = x_313;
} else {
 lean_dec_ref(x_313);
 x_318 = lean_box(0);
}
x_319 = lean_ctor_get(x_314, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 x_320 = x_314;
} else {
 lean_dec_ref(x_314);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 1, 1);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set_uint8(x_321, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_318)) {
 x_322 = lean_alloc_ctor(0, 3, 0);
} else {
 x_322 = x_318;
}
lean_ctor_set(x_322, 0, x_316);
lean_ctor_set(x_322, 1, x_317);
lean_ctor_set(x_322, 2, x_321);
x_323 = lean_st_ref_set(x_6, x_322, x_315);
lean_dec(x_6);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
 lean_ctor_set_tag(x_326, 1);
}
lean_ctor_set(x_326, 0, x_308);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_308);
lean_dec(x_6);
x_327 = lean_ctor_get(x_310, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_310, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_329 = x_310;
} else {
 lean_dec_ref(x_310);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
block_377:
{
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_338 = lean_ctor_get(x_336, 0);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_st_ref_take(x_4, x_337);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 2);
lean_inc(x_343);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 x_344 = x_340;
} else {
 lean_dec_ref(x_340);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(0, 3, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_335);
lean_ctor_set(x_345, 1, x_342);
lean_ctor_set(x_345, 2, x_343);
x_346 = lean_st_ref_set(x_4, x_345, x_341);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
x_308 = x_338;
x_309 = x_347;
goto block_331;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_348 = lean_ctor_get(x_336, 0);
lean_inc(x_348);
lean_dec(x_336);
x_349 = lean_st_ref_take(x_4, x_337);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_350, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 x_354 = x_350;
} else {
 lean_dec_ref(x_350);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 3, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_335);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_353);
x_356 = lean_st_ref_set(x_4, x_355, x_351);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec(x_356);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_358 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec(x_358);
x_360 = lean_st_ref_take(x_6, x_359);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_361, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
lean_dec(x_360);
x_364 = lean_ctor_get(x_361, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_361, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 lean_ctor_release(x_361, 2);
 x_366 = x_361;
} else {
 lean_dec_ref(x_361);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_362, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_368 = x_362;
} else {
 lean_dec_ref(x_362);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(0, 1, 1);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set_uint8(x_369, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_366)) {
 x_370 = lean_alloc_ctor(0, 3, 0);
} else {
 x_370 = x_366;
}
lean_ctor_set(x_370, 0, x_364);
lean_ctor_set(x_370, 1, x_365);
lean_ctor_set(x_370, 2, x_369);
x_371 = lean_st_ref_set(x_6, x_370, x_363);
lean_dec(x_6);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_373 = x_371;
} else {
 lean_dec_ref(x_371);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_348);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_348);
x_375 = lean_ctor_get(x_358, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_358, 1);
lean_inc(x_376);
lean_dec(x_358);
x_308 = x_375;
x_309 = x_376;
goto block_331;
}
}
}
}
}
else
{
uint8_t x_406; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_406 = !lean_is_exclusive(x_12);
if (x_406 == 0)
{
return x_12;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_12, 0);
x_408 = lean_ctor_get(x_12, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_12);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
lean_object* x_410; 
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_410 = l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1(x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_st_ref_get(x_4, x_412);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
lean_dec(x_414);
x_468 = lean_st_ref_take(x_4, x_415);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = !lean_is_exclusive(x_469);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_472 = lean_ctor_get(x_469, 0);
x_473 = l_Lean_MetavarContext_incDepth(x_472);
lean_ctor_set(x_469, 0, x_473);
x_474 = lean_st_ref_set(x_4, x_469, x_470);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
x_476 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_475);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = lean_ctor_get(x_477, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_477, 1);
lean_inc(x_480);
lean_dec(x_477);
x_481 = lean_unsigned_to_nat(0u);
x_482 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_483 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_479, x_2, x_481, x_482, x_481, x_482, x_480, x_3, x_4, x_5, x_6, x_478);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
x_486 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_486, 0, x_484);
x_417 = x_486;
x_418 = x_485;
goto block_467;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_483, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_483, 1);
lean_inc(x_488);
lean_dec(x_483);
x_489 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_489, 0, x_487);
x_417 = x_489;
x_418 = x_488;
goto block_467;
}
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_476, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_476, 1);
lean_inc(x_491);
lean_dec(x_476);
x_492 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_492, 0, x_490);
x_417 = x_492;
x_418 = x_491;
goto block_467;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_493 = lean_ctor_get(x_469, 0);
x_494 = lean_ctor_get(x_469, 1);
x_495 = lean_ctor_get(x_469, 2);
lean_inc(x_495);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_469);
x_496 = l_Lean_MetavarContext_incDepth(x_493);
x_497 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_494);
lean_ctor_set(x_497, 2, x_495);
x_498 = lean_st_ref_set(x_4, x_497, x_470);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
x_500 = l___private_Lean_Meta_AppBuilder_20__mkFun(x_1, x_3, x_4, x_5, x_6, x_499);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
lean_dec(x_501);
x_505 = lean_unsigned_to_nat(0u);
x_506 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_507 = l___private_Lean_Meta_AppBuilder_21__mkAppOptMAux___main(x_503, x_2, x_505, x_506, x_505, x_506, x_504, x_3, x_4, x_5, x_6, x_502);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_508);
x_417 = x_510;
x_418 = x_509;
goto block_467;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_507, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_507, 1);
lean_inc(x_512);
lean_dec(x_507);
x_513 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_513, 0, x_511);
x_417 = x_513;
x_418 = x_512;
goto block_467;
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_500, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_500, 1);
lean_inc(x_515);
lean_dec(x_500);
x_516 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_516, 0, x_514);
x_417 = x_516;
x_418 = x_515;
goto block_467;
}
}
block_467:
{
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_st_ref_take(x_4, x_418);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = !lean_is_exclusive(x_421);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_424 = lean_ctor_get(x_421, 0);
lean_dec(x_424);
lean_ctor_set(x_421, 0, x_416);
x_425 = lean_st_ref_set(x_4, x_421, x_422);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_428 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_411, x_427, x_3, x_4, x_5, x_6, x_426);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_429 = !lean_is_exclusive(x_428);
if (x_429 == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 0);
lean_dec(x_430);
lean_ctor_set_tag(x_428, 1);
lean_ctor_set(x_428, 0, x_419);
return x_428;
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_419);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_433 = lean_ctor_get(x_421, 1);
x_434 = lean_ctor_get(x_421, 2);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_421);
x_435 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_435, 0, x_416);
lean_ctor_set(x_435, 1, x_433);
lean_ctor_set(x_435, 2, x_434);
x_436 = lean_st_ref_set(x_4, x_435, x_422);
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
lean_dec(x_436);
x_438 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_439 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_411, x_438, x_3, x_4, x_5, x_6, x_437);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_441 = x_439;
} else {
 lean_dec_ref(x_439);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
 lean_ctor_set_tag(x_442, 1);
}
lean_ctor_set(x_442, 0, x_419);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_443 = lean_ctor_get(x_417, 0);
lean_inc(x_443);
lean_dec(x_417);
x_444 = lean_st_ref_take(x_4, x_418);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = !lean_is_exclusive(x_445);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_448 = lean_ctor_get(x_445, 0);
lean_dec(x_448);
lean_ctor_set(x_445, 0, x_416);
x_449 = lean_st_ref_set(x_4, x_445, x_446);
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
lean_dec(x_449);
x_451 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_452 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_411, x_451, x_3, x_4, x_5, x_6, x_450);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_453 = !lean_is_exclusive(x_452);
if (x_453 == 0)
{
lean_object* x_454; 
x_454 = lean_ctor_get(x_452, 0);
lean_dec(x_454);
lean_ctor_set(x_452, 0, x_443);
return x_452;
}
else
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
lean_dec(x_452);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_443);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_457 = lean_ctor_get(x_445, 1);
x_458 = lean_ctor_get(x_445, 2);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_445);
x_459 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_459, 0, x_416);
lean_ctor_set(x_459, 1, x_457);
lean_ctor_set(x_459, 2, x_458);
x_460 = lean_st_ref_set(x_4, x_459, x_446);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_463 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_411, x_462, x_3, x_4, x_5, x_6, x_461);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_465 = x_463;
} else {
 lean_dec_ref(x_463);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_443);
lean_ctor_set(x_466, 1, x_464);
return x_466;
}
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_517 = !lean_is_exclusive(x_410);
if (x_517 == 0)
{
return x_410;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_410, 0);
x_519 = lean_ctor_get(x_410, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_410);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
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
