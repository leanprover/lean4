// Lean compiler output
// Module: Lean.Elab.PreDefinition.Basic
// Imports: Init Lean.Util.SCC Lean.Meta.AbstractNestedProofs Lean.Elab.Term Lean.Elab.DefView Lean.Elab.PreDefinition.MkInhabitant
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
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_match__1(lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Declaration_inhabited;
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafeRec_match__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Std_ShareCommon_State_empty;
lean_object* l_Lean_Elab_addAndCompileUnsafeRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_inhabited;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_ShareCommonT_withShareCommon___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon___spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafeRec_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Elab_fixLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr_match__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
lean_object* l_Lean_Elab_addAndCompileUnsafeRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Elab_fixLevelParams_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__1;
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_inhabited___closed__2;
lean_object* l_Lean_Elab_fixLevelParams_match__1(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_addAndCompileUnsafe___spec__1(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_inhabited___closed__1;
extern lean_object* l_Lean_Compiler_mkUnsafeRecName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_fixLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
extern lean_object* l_Lean_Expr_Lean_Expr___instance__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_PreDefinition_inhabited___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PreDefinition_inhabited___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_Elab_PreDefinition_inhabited___closed__1;
x_4 = lean_box(0);
x_5 = l_Lean_Expr_Lean_Expr___instance__1___closed__1;
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_PreDefinition_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_PreDefinition_inhabited___closed__2;
return x_1;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_17, 3);
x_20 = lean_ctor_get(x_17, 4);
x_21 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_17, 4, x_25);
lean_ctor_set(x_17, 3, x_22);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_1, x_27);
x_29 = x_17;
x_30 = lean_array_fset(x_16, x_1, x_29);
lean_dec(x_1);
x_1 = x_28;
x_2 = x_30;
x_9 = x_26;
goto _start;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get_uint8(x_17, sizeof(void*)*5);
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
x_35 = lean_ctor_get(x_17, 2);
x_36 = lean_ctor_get(x_17, 3);
x_37 = lean_ctor_get(x_17, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_38 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*5, x_32);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_1, x_45);
x_47 = x_44;
x_48 = lean_array_fset(x_16, x_1, x_47);
lean_dec(x_1);
x_1 = x_46;
x_2 = x_48;
x_9 = x_43;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed), 9, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = x_11;
x_13 = lean_apply_7(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_levelMVarToParam(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_set(x_2, x_17, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = x_15;
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_18, 3);
x_21 = lean_ctor_get(x_18, 4);
lean_inc(x_4);
x_22 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_4);
x_25 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_18, 4, x_26);
lean_ctor_set(x_18, 3, x_23);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_1, x_28);
x_30 = x_18;
x_31 = lean_array_fset(x_17, x_1, x_30);
lean_dec(x_1);
x_1 = x_29;
x_2 = x_31;
x_10 = x_27;
goto _start;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_33 = lean_ctor_get_uint8(x_18, sizeof(void*)*5);
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
x_36 = lean_ctor_get(x_18, 2);
x_37 = lean_ctor_get(x_18, 3);
x_38 = lean_ctor_get(x_18, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
lean_inc(x_4);
x_39 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_4);
x_42 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamExpr(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_33);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_1, x_46);
x_48 = x_45;
x_49 = lean_array_fset(x_17, x_1, x_48);
lean_dec(x_1);
x_1 = x_47;
x_2 = x_49;
x_10 = x_44;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = x_1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = x_12;
x_14 = lean_apply_8(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = l_Lean_CollectLevelParams_main(x_15, x_4);
x_17 = lean_ctor_get(x_14, 4);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_CollectLevelParams_main(x_17, x_16);
x_19 = 1;
x_20 = x_3 + x_19;
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Lean_CollectLevelParams_State_inhabited___closed__1;
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(x_1, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_ShareCommonT_withShareCommon___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_state_sharecommon(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = x_2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = x_8;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_11, 3);
x_14 = lean_ctor_get(x_11, 4);
x_15 = lean_state_sharecommon(x_3, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_state_sharecommon(x_17, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_11, 4, x_19);
lean_ctor_set(x_11, 3, x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_11;
x_24 = lean_array_fset(x_10, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
x_31 = lean_ctor_get(x_11, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_32 = lean_state_sharecommon(x_3, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_state_sharecommon(x_34, x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*5, x_26);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_1, x_39);
x_41 = x_38;
x_42 = lean_array_fset(x_10, x_1, x_41);
lean_dec(x_1);
x_1 = x_40;
x_2 = x_42;
x_3 = x_37;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = x_1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon___spec__2), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Std_ShareCommon_State_empty;
x_6 = x_4;
x_7 = lean_apply_1(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_fixLevelParams_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Elab_fixLevelParams_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_fixLevelParams_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_238; lean_object* x_239; size_t x_240; uint8_t x_241; 
x_7 = lean_ptr_addr(x_5);
x_8 = x_4 == 0 ? 0 : x_7 % x_4;
x_238 = lean_ctor_get(x_6, 0);
lean_inc(x_238);
x_239 = lean_array_uget(x_238, x_8);
x_240 = lean_ptr_addr(x_239);
lean_dec(x_239);
x_241 = x_240 == x_7;
if (x_241 == 0)
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_5, 0);
lean_inc(x_242);
x_243 = lean_array_get_size(x_2);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(x_1, x_242, x_2, x_243, x_244);
lean_dec(x_243);
if (x_245 == 0)
{
lean_object* x_246; 
lean_dec(x_242);
lean_dec(x_238);
x_246 = lean_box(0);
x_9 = x_246;
goto block_237;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = l_Lean_mkConst(x_242, x_3);
x_248 = lean_array_uset(x_238, x_8, x_5);
x_249 = lean_ctor_get(x_6, 1);
lean_inc(x_249);
lean_dec(x_6);
lean_inc(x_247);
x_250 = lean_array_uset(x_249, x_8, x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_247);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
else
{
lean_object* x_253; 
lean_dec(x_238);
x_253 = lean_box(0);
x_9 = x_253;
goto block_237;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_238);
lean_dec(x_5);
lean_dec(x_3);
x_254 = lean_ctor_get(x_6, 1);
lean_inc(x_254);
x_255 = lean_array_uget(x_254, x_8);
lean_dec(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_6);
return x_256;
}
block_237:
{
lean_dec(x_9);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_10);
lean_inc(x_3);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_10, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_11, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_inc(x_5);
x_21 = lean_array_uset(x_20, x_8, x_5);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_expr_update_app(x_5, x_14, x_18);
lean_inc(x_26);
x_27 = lean_array_uset(x_25, x_8, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_12);
x_31 = lean_expr_update_app(x_30, x_14, x_18);
lean_inc(x_31);
x_32 = lean_array_uset(x_29, x_8, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_16, 1, x_33);
lean_ctor_set(x_16, 0, x_31);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_inc(x_5);
x_37 = lean_array_uset(x_36, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_38 = x_5;
} else {
 lean_dec_ref(x_5);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(5, 2, 8);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set_uint64(x_40, sizeof(void*)*2, x_12);
x_41 = lean_expr_update_app(x_40, x_14, x_34);
lean_inc(x_41);
x_42 = lean_array_uset(x_39, x_8, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_46);
lean_inc(x_3);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_46, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_47);
x_52 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_47, x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_inc(x_5);
x_57 = lean_array_uset(x_56, x_8, x_5);
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_5, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_5, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_5, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = (uint8_t)((x_48 << 24) >> 61);
x_64 = lean_expr_update_lambda(x_5, x_63, x_50, x_54);
lean_inc(x_64);
x_65 = lean_array_uset(x_62, x_8, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_52, 1, x_66);
lean_ctor_set(x_52, 0, x_64);
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_68, 0, x_45);
lean_ctor_set(x_68, 1, x_46);
lean_ctor_set(x_68, 2, x_47);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_48);
x_69 = (uint8_t)((x_48 << 24) >> 61);
x_70 = lean_expr_update_lambda(x_68, x_69, x_50, x_54);
lean_inc(x_70);
x_71 = lean_array_uset(x_67, x_8, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_52, 1, x_72);
lean_ctor_set(x_52, 0, x_70);
return x_52;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_52, 0);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_52);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_inc(x_5);
x_76 = lean_array_uset(x_75, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_77 = x_5;
} else {
 lean_dec_ref(x_5);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(6, 3, 8);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_45);
lean_ctor_set(x_79, 1, x_46);
lean_ctor_set(x_79, 2, x_47);
lean_ctor_set_uint64(x_79, sizeof(void*)*3, x_48);
x_80 = (uint8_t)((x_48 << 24) >> 61);
x_81 = lean_expr_update_lambda(x_79, x_80, x_50, x_73);
lean_inc(x_81);
x_82 = lean_array_uset(x_78, x_8, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_85 = lean_ctor_get(x_5, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_5, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_5, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_86);
lean_inc(x_3);
x_89 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_86, x_6);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_87);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_87, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_inc(x_5);
x_97 = lean_array_uset(x_96, x_8, x_5);
x_98 = !lean_is_exclusive(x_5);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_5, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_5, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_5, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_dec(x_95);
x_103 = (uint8_t)((x_88 << 24) >> 61);
x_104 = lean_expr_update_forall(x_5, x_103, x_90, x_94);
lean_inc(x_104);
x_105 = lean_array_uset(x_102, x_8, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_92, 1, x_106);
lean_ctor_set(x_92, 0, x_104);
return x_92;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_5);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_dec(x_95);
x_108 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_108, 0, x_85);
lean_ctor_set(x_108, 1, x_86);
lean_ctor_set(x_108, 2, x_87);
lean_ctor_set_uint64(x_108, sizeof(void*)*3, x_88);
x_109 = (uint8_t)((x_88 << 24) >> 61);
x_110 = lean_expr_update_forall(x_108, x_109, x_90, x_94);
lean_inc(x_110);
x_111 = lean_array_uset(x_107, x_8, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_97);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_92, 1, x_112);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_92, 0);
x_114 = lean_ctor_get(x_92, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_92);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_inc(x_5);
x_116 = lean_array_uset(x_115, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_117 = x_5;
} else {
 lean_dec_ref(x_5);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(7, 3, 8);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_85);
lean_ctor_set(x_119, 1, x_86);
lean_ctor_set(x_119, 2, x_87);
lean_ctor_set_uint64(x_119, sizeof(void*)*3, x_88);
x_120 = (uint8_t)((x_88 << 24) >> 61);
x_121 = lean_expr_update_forall(x_119, x_120, x_90, x_113);
lean_inc(x_121);
x_122 = lean_array_uset(x_118, x_8, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
case 8:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_125 = lean_ctor_get(x_5, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_5, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_5, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_5, 3);
lean_inc(x_128);
x_129 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_126);
lean_inc(x_3);
x_130 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_126, x_6);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_127);
lean_inc(x_3);
x_133 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_127, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_128);
x_136 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_128, x_135);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_inc(x_5);
x_141 = lean_array_uset(x_140, x_8, x_5);
x_142 = !lean_is_exclusive(x_5);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_5, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_5, 2);
lean_dec(x_144);
x_145 = lean_ctor_get(x_5, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_5, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_139, 1);
lean_inc(x_147);
lean_dec(x_139);
x_148 = lean_expr_update_let(x_5, x_131, x_134, x_138);
lean_inc(x_148);
x_149 = lean_array_uset(x_147, x_8, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_136, 1, x_150);
lean_ctor_set(x_136, 0, x_148);
return x_136;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_5);
x_151 = lean_ctor_get(x_139, 1);
lean_inc(x_151);
lean_dec(x_139);
x_152 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_152, 0, x_125);
lean_ctor_set(x_152, 1, x_126);
lean_ctor_set(x_152, 2, x_127);
lean_ctor_set(x_152, 3, x_128);
lean_ctor_set_uint64(x_152, sizeof(void*)*4, x_129);
x_153 = lean_expr_update_let(x_152, x_131, x_134, x_138);
lean_inc(x_153);
x_154 = lean_array_uset(x_151, x_8, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_141);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_136, 1, x_155);
lean_ctor_set(x_136, 0, x_153);
return x_136;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_136, 0);
x_157 = lean_ctor_get(x_136, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_136);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_inc(x_5);
x_159 = lean_array_uset(x_158, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_160 = x_5;
} else {
 lean_dec_ref(x_5);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(8, 4, 8);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_125);
lean_ctor_set(x_162, 1, x_126);
lean_ctor_set(x_162, 2, x_127);
lean_ctor_set(x_162, 3, x_128);
lean_ctor_set_uint64(x_162, sizeof(void*)*4, x_129);
x_163 = lean_expr_update_let(x_162, x_131, x_134, x_156);
lean_inc(x_163);
x_164 = lean_array_uset(x_161, x_8, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
case 10:
{
lean_object* x_167; lean_object* x_168; uint64_t x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_5, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_5, 1);
lean_inc(x_168);
x_169 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_168);
x_170 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_168, x_6);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = lean_ctor_get(x_170, 1);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_inc(x_5);
x_175 = lean_array_uset(x_174, x_8, x_5);
x_176 = !lean_is_exclusive(x_5);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_5, 1);
lean_dec(x_177);
x_178 = lean_ctor_get(x_5, 0);
lean_dec(x_178);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec(x_173);
x_180 = lean_expr_update_mdata(x_5, x_172);
lean_inc(x_180);
x_181 = lean_array_uset(x_179, x_8, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_170, 1, x_182);
lean_ctor_set(x_170, 0, x_180);
return x_170;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_5);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
lean_dec(x_173);
x_184 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_168);
lean_ctor_set_uint64(x_184, sizeof(void*)*2, x_169);
x_185 = lean_expr_update_mdata(x_184, x_172);
lean_inc(x_185);
x_186 = lean_array_uset(x_183, x_8, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_175);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_170, 1, x_187);
lean_ctor_set(x_170, 0, x_185);
return x_170;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_188 = lean_ctor_get(x_170, 0);
x_189 = lean_ctor_get(x_170, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_170);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_inc(x_5);
x_191 = lean_array_uset(x_190, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_192 = x_5;
} else {
 lean_dec_ref(x_5);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
lean_dec(x_189);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(10, 2, 8);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_167);
lean_ctor_set(x_194, 1, x_168);
lean_ctor_set_uint64(x_194, sizeof(void*)*2, x_169);
x_195 = lean_expr_update_mdata(x_194, x_188);
lean_inc(x_195);
x_196 = lean_array_uset(x_193, x_8, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_191);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
case 11:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint64_t x_202; lean_object* x_203; uint8_t x_204; 
x_199 = lean_ctor_get(x_5, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_5, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_5, 2);
lean_inc(x_201);
x_202 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_201);
x_203 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_201, x_6);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_inc(x_5);
x_208 = lean_array_uset(x_207, x_8, x_5);
x_209 = !lean_is_exclusive(x_5);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_5, 2);
lean_dec(x_210);
x_211 = lean_ctor_get(x_5, 1);
lean_dec(x_211);
x_212 = lean_ctor_get(x_5, 0);
lean_dec(x_212);
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_dec(x_206);
x_214 = lean_expr_update_proj(x_5, x_205);
lean_inc(x_214);
x_215 = lean_array_uset(x_213, x_8, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_203, 1, x_216);
lean_ctor_set(x_203, 0, x_214);
return x_203;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_5);
x_217 = lean_ctor_get(x_206, 1);
lean_inc(x_217);
lean_dec(x_206);
x_218 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_218, 0, x_199);
lean_ctor_set(x_218, 1, x_200);
lean_ctor_set(x_218, 2, x_201);
lean_ctor_set_uint64(x_218, sizeof(void*)*3, x_202);
x_219 = lean_expr_update_proj(x_218, x_205);
lean_inc(x_219);
x_220 = lean_array_uset(x_217, x_8, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_208);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_203, 1, x_221);
lean_ctor_set(x_203, 0, x_219);
return x_203;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_222 = lean_ctor_get(x_203, 0);
x_223 = lean_ctor_get(x_203, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_203);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_inc(x_5);
x_225 = lean_array_uset(x_224, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_226 = x_5;
} else {
 lean_dec_ref(x_5);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(11, 3, 8);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_199);
lean_ctor_set(x_228, 1, x_200);
lean_ctor_set(x_228, 2, x_201);
lean_ctor_set_uint64(x_228, sizeof(void*)*3, x_202);
x_229 = lean_expr_update_proj(x_228, x_222);
lean_inc(x_229);
x_230 = lean_array_uset(x_227, x_8, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_225);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
case 12:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_5);
lean_dec(x_3);
x_233 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
x_234 = l_unreachable_x21___rarg(x_233);
x_235 = lean_apply_1(x_234, x_6);
return x_235;
}
default: 
{
lean_object* x_236; 
lean_dec(x_3);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_5);
lean_ctor_set(x_236, 1, x_6);
return x_236;
}
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_238; lean_object* x_239; size_t x_240; uint8_t x_241; 
x_7 = lean_ptr_addr(x_5);
x_8 = x_4 == 0 ? 0 : x_7 % x_4;
x_238 = lean_ctor_get(x_6, 0);
lean_inc(x_238);
x_239 = lean_array_uget(x_238, x_8);
x_240 = lean_ptr_addr(x_239);
lean_dec(x_239);
x_241 = x_240 == x_7;
if (x_241 == 0)
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_5, 0);
lean_inc(x_242);
x_243 = lean_array_get_size(x_2);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(x_1, x_242, x_2, x_243, x_244);
lean_dec(x_243);
if (x_245 == 0)
{
lean_object* x_246; 
lean_dec(x_242);
lean_dec(x_238);
x_246 = lean_box(0);
x_9 = x_246;
goto block_237;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = l_Lean_mkConst(x_242, x_3);
x_248 = lean_array_uset(x_238, x_8, x_5);
x_249 = lean_ctor_get(x_6, 1);
lean_inc(x_249);
lean_dec(x_6);
lean_inc(x_247);
x_250 = lean_array_uset(x_249, x_8, x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_247);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
else
{
lean_object* x_253; 
lean_dec(x_238);
x_253 = lean_box(0);
x_9 = x_253;
goto block_237;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_238);
lean_dec(x_5);
lean_dec(x_3);
x_254 = lean_ctor_get(x_6, 1);
lean_inc(x_254);
x_255 = lean_array_uget(x_254, x_8);
lean_dec(x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_6);
return x_256;
}
block_237:
{
lean_dec(x_9);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_10);
lean_inc(x_3);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_10, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_11, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_inc(x_5);
x_21 = lean_array_uset(x_20, x_8, x_5);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_expr_update_app(x_5, x_14, x_18);
lean_inc(x_26);
x_27 = lean_array_uset(x_25, x_8, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_12);
x_31 = lean_expr_update_app(x_30, x_14, x_18);
lean_inc(x_31);
x_32 = lean_array_uset(x_29, x_8, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_16, 1, x_33);
lean_ctor_set(x_16, 0, x_31);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_inc(x_5);
x_37 = lean_array_uset(x_36, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_38 = x_5;
} else {
 lean_dec_ref(x_5);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(5, 2, 8);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set_uint64(x_40, sizeof(void*)*2, x_12);
x_41 = lean_expr_update_app(x_40, x_14, x_34);
lean_inc(x_41);
x_42 = lean_array_uset(x_39, x_8, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_46);
lean_inc(x_3);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_46, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_47);
x_52 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_47, x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_inc(x_5);
x_57 = lean_array_uset(x_56, x_8, x_5);
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_5, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_5, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_5, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = (uint8_t)((x_48 << 24) >> 61);
x_64 = lean_expr_update_lambda(x_5, x_63, x_50, x_54);
lean_inc(x_64);
x_65 = lean_array_uset(x_62, x_8, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_52, 1, x_66);
lean_ctor_set(x_52, 0, x_64);
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_68, 0, x_45);
lean_ctor_set(x_68, 1, x_46);
lean_ctor_set(x_68, 2, x_47);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_48);
x_69 = (uint8_t)((x_48 << 24) >> 61);
x_70 = lean_expr_update_lambda(x_68, x_69, x_50, x_54);
lean_inc(x_70);
x_71 = lean_array_uset(x_67, x_8, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_52, 1, x_72);
lean_ctor_set(x_52, 0, x_70);
return x_52;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_52, 0);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_52);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_inc(x_5);
x_76 = lean_array_uset(x_75, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_77 = x_5;
} else {
 lean_dec_ref(x_5);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(6, 3, 8);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_45);
lean_ctor_set(x_79, 1, x_46);
lean_ctor_set(x_79, 2, x_47);
lean_ctor_set_uint64(x_79, sizeof(void*)*3, x_48);
x_80 = (uint8_t)((x_48 << 24) >> 61);
x_81 = lean_expr_update_lambda(x_79, x_80, x_50, x_73);
lean_inc(x_81);
x_82 = lean_array_uset(x_78, x_8, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_85 = lean_ctor_get(x_5, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_5, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_5, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_86);
lean_inc(x_3);
x_89 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_86, x_6);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_87);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_87, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_inc(x_5);
x_97 = lean_array_uset(x_96, x_8, x_5);
x_98 = !lean_is_exclusive(x_5);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_5, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_5, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_5, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_dec(x_95);
x_103 = (uint8_t)((x_88 << 24) >> 61);
x_104 = lean_expr_update_forall(x_5, x_103, x_90, x_94);
lean_inc(x_104);
x_105 = lean_array_uset(x_102, x_8, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_92, 1, x_106);
lean_ctor_set(x_92, 0, x_104);
return x_92;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_5);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_dec(x_95);
x_108 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_108, 0, x_85);
lean_ctor_set(x_108, 1, x_86);
lean_ctor_set(x_108, 2, x_87);
lean_ctor_set_uint64(x_108, sizeof(void*)*3, x_88);
x_109 = (uint8_t)((x_88 << 24) >> 61);
x_110 = lean_expr_update_forall(x_108, x_109, x_90, x_94);
lean_inc(x_110);
x_111 = lean_array_uset(x_107, x_8, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_97);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_92, 1, x_112);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_92, 0);
x_114 = lean_ctor_get(x_92, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_92);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_inc(x_5);
x_116 = lean_array_uset(x_115, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_117 = x_5;
} else {
 lean_dec_ref(x_5);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(7, 3, 8);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_85);
lean_ctor_set(x_119, 1, x_86);
lean_ctor_set(x_119, 2, x_87);
lean_ctor_set_uint64(x_119, sizeof(void*)*3, x_88);
x_120 = (uint8_t)((x_88 << 24) >> 61);
x_121 = lean_expr_update_forall(x_119, x_120, x_90, x_113);
lean_inc(x_121);
x_122 = lean_array_uset(x_118, x_8, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
case 8:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_125 = lean_ctor_get(x_5, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_5, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_5, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_5, 3);
lean_inc(x_128);
x_129 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_126);
lean_inc(x_3);
x_130 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_126, x_6);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_127);
lean_inc(x_3);
x_133 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_127, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_128);
x_136 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_128, x_135);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_inc(x_5);
x_141 = lean_array_uset(x_140, x_8, x_5);
x_142 = !lean_is_exclusive(x_5);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_5, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_5, 2);
lean_dec(x_144);
x_145 = lean_ctor_get(x_5, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_5, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_139, 1);
lean_inc(x_147);
lean_dec(x_139);
x_148 = lean_expr_update_let(x_5, x_131, x_134, x_138);
lean_inc(x_148);
x_149 = lean_array_uset(x_147, x_8, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_136, 1, x_150);
lean_ctor_set(x_136, 0, x_148);
return x_136;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_5);
x_151 = lean_ctor_get(x_139, 1);
lean_inc(x_151);
lean_dec(x_139);
x_152 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_152, 0, x_125);
lean_ctor_set(x_152, 1, x_126);
lean_ctor_set(x_152, 2, x_127);
lean_ctor_set(x_152, 3, x_128);
lean_ctor_set_uint64(x_152, sizeof(void*)*4, x_129);
x_153 = lean_expr_update_let(x_152, x_131, x_134, x_138);
lean_inc(x_153);
x_154 = lean_array_uset(x_151, x_8, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_141);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_136, 1, x_155);
lean_ctor_set(x_136, 0, x_153);
return x_136;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_136, 0);
x_157 = lean_ctor_get(x_136, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_136);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_inc(x_5);
x_159 = lean_array_uset(x_158, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_160 = x_5;
} else {
 lean_dec_ref(x_5);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(8, 4, 8);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_125);
lean_ctor_set(x_162, 1, x_126);
lean_ctor_set(x_162, 2, x_127);
lean_ctor_set(x_162, 3, x_128);
lean_ctor_set_uint64(x_162, sizeof(void*)*4, x_129);
x_163 = lean_expr_update_let(x_162, x_131, x_134, x_156);
lean_inc(x_163);
x_164 = lean_array_uset(x_161, x_8, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
case 10:
{
lean_object* x_167; lean_object* x_168; uint64_t x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_5, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_5, 1);
lean_inc(x_168);
x_169 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_168);
x_170 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_168, x_6);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = lean_ctor_get(x_170, 1);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_inc(x_5);
x_175 = lean_array_uset(x_174, x_8, x_5);
x_176 = !lean_is_exclusive(x_5);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_5, 1);
lean_dec(x_177);
x_178 = lean_ctor_get(x_5, 0);
lean_dec(x_178);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec(x_173);
x_180 = lean_expr_update_mdata(x_5, x_172);
lean_inc(x_180);
x_181 = lean_array_uset(x_179, x_8, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_170, 1, x_182);
lean_ctor_set(x_170, 0, x_180);
return x_170;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_5);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
lean_dec(x_173);
x_184 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_168);
lean_ctor_set_uint64(x_184, sizeof(void*)*2, x_169);
x_185 = lean_expr_update_mdata(x_184, x_172);
lean_inc(x_185);
x_186 = lean_array_uset(x_183, x_8, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_175);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_170, 1, x_187);
lean_ctor_set(x_170, 0, x_185);
return x_170;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_188 = lean_ctor_get(x_170, 0);
x_189 = lean_ctor_get(x_170, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_170);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_inc(x_5);
x_191 = lean_array_uset(x_190, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_192 = x_5;
} else {
 lean_dec_ref(x_5);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
lean_dec(x_189);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(10, 2, 8);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_167);
lean_ctor_set(x_194, 1, x_168);
lean_ctor_set_uint64(x_194, sizeof(void*)*2, x_169);
x_195 = lean_expr_update_mdata(x_194, x_188);
lean_inc(x_195);
x_196 = lean_array_uset(x_193, x_8, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_191);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
case 11:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint64_t x_202; lean_object* x_203; uint8_t x_204; 
x_199 = lean_ctor_get(x_5, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_5, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_5, 2);
lean_inc(x_201);
x_202 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_201);
x_203 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_201, x_6);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_inc(x_5);
x_208 = lean_array_uset(x_207, x_8, x_5);
x_209 = !lean_is_exclusive(x_5);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_5, 2);
lean_dec(x_210);
x_211 = lean_ctor_get(x_5, 1);
lean_dec(x_211);
x_212 = lean_ctor_get(x_5, 0);
lean_dec(x_212);
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_dec(x_206);
x_214 = lean_expr_update_proj(x_5, x_205);
lean_inc(x_214);
x_215 = lean_array_uset(x_213, x_8, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_203, 1, x_216);
lean_ctor_set(x_203, 0, x_214);
return x_203;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_5);
x_217 = lean_ctor_get(x_206, 1);
lean_inc(x_217);
lean_dec(x_206);
x_218 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_218, 0, x_199);
lean_ctor_set(x_218, 1, x_200);
lean_ctor_set(x_218, 2, x_201);
lean_ctor_set_uint64(x_218, sizeof(void*)*3, x_202);
x_219 = lean_expr_update_proj(x_218, x_205);
lean_inc(x_219);
x_220 = lean_array_uset(x_217, x_8, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_208);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_203, 1, x_221);
lean_ctor_set(x_203, 0, x_219);
return x_203;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_222 = lean_ctor_get(x_203, 0);
x_223 = lean_ctor_get(x_203, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_203);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_inc(x_5);
x_225 = lean_array_uset(x_224, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_226 = x_5;
} else {
 lean_dec_ref(x_5);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(11, 3, 8);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_199);
lean_ctor_set(x_228, 1, x_200);
lean_ctor_set(x_228, 2, x_201);
lean_ctor_set_uint64(x_228, sizeof(void*)*3, x_202);
x_229 = lean_expr_update_proj(x_228, x_222);
lean_inc(x_229);
x_230 = lean_array_uset(x_227, x_8, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_225);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
case 12:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_5);
lean_dec(x_3);
x_233 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
x_234 = l_unreachable_x21___rarg(x_233);
x_235 = lean_apply_1(x_234, x_6);
return x_235;
}
default: 
{
lean_object* x_236; 
lean_dec(x_3);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_5);
lean_ctor_set(x_236, 1, x_6);
return x_236;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = x_6;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_6, x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_6, x_5, x_11);
x_13 = x_10;
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_13, 3);
x_16 = lean_ctor_get(x_13, 4);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = 8192;
x_19 = l_Lean_Expr_ReplaceImpl_initCache;
lean_inc(x_4);
x_20 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_4, x_18, x_15, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_4);
x_22 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_4, x_18, x_16, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_3);
lean_ctor_set(x_13, 4, x_23);
lean_ctor_set(x_13, 3, x_21);
lean_ctor_set(x_13, 0, x_3);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
x_26 = x_13;
x_27 = lean_array_fset(x_12, x_5, x_26);
lean_dec(x_5);
x_5 = x_25;
x_6 = x_27;
goto _start;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
x_30 = lean_ctor_get(x_13, 1);
x_31 = lean_ctor_get(x_13, 2);
x_32 = lean_ctor_get(x_13, 3);
x_33 = lean_ctor_get(x_13, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_34 = 8192;
x_35 = l_Lean_Expr_ReplaceImpl_initCache;
lean_inc(x_4);
x_36 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_4, x_34, x_32, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_4);
x_38 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_4, x_34, x_33, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_3);
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_29);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_5, x_41);
x_43 = x_40;
x_44 = lean_array_fset(x_12, x_5, x_43);
lean_dec(x_5);
x_5 = x_42;
x_6 = x_44;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_fixLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shareCommon(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(x_14);
lean_inc(x_11);
x_16 = x_11;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_11, x_14, x_15, x_17, x_16);
lean_dec(x_11);
lean_dec(x_1);
x_19 = x_18;
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_20);
x_22 = l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(x_20);
lean_inc(x_11);
x_23 = x_11;
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_11, x_20, x_22, x_24, x_23);
lean_dec(x_11);
lean_dec(x_1);
x_26 = x_25;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_fixLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_fixLevelParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_20 = l_Lean_Elab_Term_applyAttributesAt(x_16, x_18, x_1, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = x_4 + x_22;
x_24 = lean_box(0);
x_4 = x_23;
x_5 = x_24;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Elab_applyAttributesOf(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(0);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(x_2, x_1, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_applyAttributesOf(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = l_Lean_Elab_DefKind_isTheorem(x_7);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Elab_DefKind_isExample(x_7);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 4);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
lean_inc(x_10);
x_21 = l_Lean_Meta_abstractNestedProofs(x_10, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_1, 4, x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_1, 4, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_1);
lean_inc(x_10);
x_31 = l_Lean_Meta_abstractNestedProofs(x_10, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_10);
lean_ctor_set(x_35, 3, x_11);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_7);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_6);
return x_42;
}
}
}
lean_object* l_Lean_Elab_addAsAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*2 + 3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(x_14, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addAsAxiom(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_5, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux_match__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PreDefinition.Basic");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.Basic.0.Lean.Elab.addNonRecAux");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2;
x_3 = lean_unsigned_to_nat(98u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_abstractNestedProofs(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 4);
lean_inc(x_22);
switch (x_17) {
case 0:
{
lean_object* x_75; lean_object* x_76; uint32_t x_77; uint32_t x_78; uint32_t x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_20);
lean_ctor_set(x_75, 1, x_18);
lean_ctor_set(x_75, 2, x_21);
lean_inc(x_22);
x_76 = l_Lean_getMaxHeight(x_16, x_22);
x_77 = lean_unbox_uint32(x_76);
lean_dec(x_76);
x_78 = 1;
x_79 = x_77 + x_78;
x_80 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_80, 0, x_79);
x_81 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 3);
lean_dec(x_19);
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_22);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_23 = x_83;
goto block_74;
}
case 1:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_19);
lean_dec(x_16);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_20);
lean_ctor_set(x_84, 1, x_18);
lean_ctor_set(x_84, 2, x_21);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_22);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_23 = x_86;
goto block_74;
}
case 2:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
x_87 = l_Lean_Declaration_inhabited;
x_88 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
x_89 = lean_panic_fn(x_87, x_88);
x_23 = x_89;
goto block_74;
}
case 3:
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_16);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_20);
lean_ctor_set(x_90, 1, x_18);
lean_ctor_set(x_90, 2, x_21);
x_91 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 3);
lean_dec(x_19);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_22);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_91);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_23 = x_93;
goto block_74;
}
default: 
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_16);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_20);
lean_ctor_set(x_94, 1, x_18);
lean_ctor_set(x_94, 2, x_21);
x_95 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 3);
lean_dec(x_19);
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_22);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*3, x_95);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_23 = x_98;
goto block_74;
}
}
block_74:
{
lean_object* x_24; 
lean_inc(x_7);
lean_inc(x_3);
x_24 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_mkOptionalNode___closed__2;
x_27 = lean_array_push(x_26, x_11);
x_28 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_29 = l_Lean_Elab_applyAttributesOf(x_27, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (x_2 == 0)
{
uint8_t x_63; 
x_63 = 0;
x_31 = x_63;
goto block_62;
}
else
{
uint8_t x_64; 
x_64 = l_Lean_Elab_DefKind_isTheorem(x_17);
if (x_64 == 0)
{
x_31 = x_2;
goto block_62;
}
else
{
uint8_t x_65; 
x_65 = 0;
x_31 = x_65;
goto block_62;
}
}
block_62:
{
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; 
lean_dec(x_23);
x_32 = 1;
x_33 = l_Lean_Elab_applyAttributesOf(x_27, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_27);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_inc(x_7);
lean_inc(x_3);
x_44 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_23);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 1;
x_47 = l_Lean_Elab_applyAttributesOf(x_27, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_27);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
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
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
return x_44;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_44, 0);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_44);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_29);
if (x_66 == 0)
{
return x_29;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_29, 0);
x_68 = lean_ctor_get(x_29, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_29);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_24);
if (x_70 == 0)
{
return x_24;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_24, 0);
x_72 = lean_ctor_get(x_24, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_24);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_10);
if (x_99 == 0)
{
return x_10;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_10, 0);
x_101 = lean_ctor_get(x_10, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_10);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_addAndCompileNonRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_addAndCompileNonRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_addNonRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_addNonRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_List_map___main___at_Lean_Elab_addAndCompileUnsafe___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
x_11 = lean_box(0);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
x_14 = l_List_map___main___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_5);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 4);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_19);
x_22 = lean_box(0);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
x_25 = l_List_map___main___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Array_toList___rarg(x_1);
x_10 = l_List_map___main___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_9);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_15 = l_Lean_Elab_applyAttributesOf(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_2);
x_17 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = l_Lean_Elab_applyAttributesOf(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
return x_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_addAndCompileUnsafe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_addAndCompileUnsafeRec_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Elab_addAndCompileUnsafeRec_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addAndCompileUnsafeRec_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_236; lean_object* x_237; size_t x_238; uint8_t x_239; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_236 = lean_ctor_get(x_4, 0);
lean_inc(x_236);
x_237 = lean_array_uget(x_236, x_6);
x_238 = lean_ptr_addr(x_237);
lean_dec(x_237);
x_239 = x_238 == x_5;
if (x_239 == 0)
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_240 = lean_ctor_get(x_3, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_3, 1);
lean_inc(x_241);
x_242 = lean_array_get_size(x_1);
x_243 = lean_unsigned_to_nat(0u);
x_244 = l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1(x_1, x_240, x_1, x_242, x_243);
lean_dec(x_242);
if (x_244 == 0)
{
lean_object* x_245; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_236);
x_245 = lean_box(0);
x_7 = x_245;
goto block_235;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_246 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_247 = lean_name_mk_string(x_240, x_246);
x_248 = l_Lean_mkConst(x_247, x_241);
x_249 = lean_array_uset(x_236, x_6, x_3);
x_250 = lean_ctor_get(x_4, 1);
lean_inc(x_250);
lean_dec(x_4);
lean_inc(x_248);
x_251 = lean_array_uset(x_250, x_6, x_248);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_248);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
else
{
lean_object* x_254; 
lean_dec(x_236);
x_254 = lean_box(0);
x_7 = x_254;
goto block_235;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_236);
lean_dec(x_3);
x_255 = lean_ctor_get(x_4, 1);
lean_inc(x_255);
x_256 = lean_array_uget(x_255, x_6);
lean_dec(x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_4);
return x_257;
}
block_235:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_8);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_8, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_9, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_3);
x_19 = lean_array_uset(x_18, x_6, x_3);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_expr_update_app(x_3, x_12, x_16);
lean_inc(x_24);
x_25 = lean_array_uset(x_23, x_6, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_14, 1, x_26);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_10);
x_29 = lean_expr_update_app(x_28, x_12, x_16);
lean_inc(x_29);
x_30 = lean_array_uset(x_27, x_6, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_14, 1, x_31);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_inc(x_3);
x_35 = lean_array_uset(x_34, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_36 = x_3;
} else {
 lean_dec_ref(x_3);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(5, 2, 8);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_10);
x_39 = lean_expr_update_app(x_38, x_12, x_32);
lean_inc(x_39);
x_40 = lean_array_uset(x_37, x_6, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 6:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_44);
x_47 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_44, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_45);
x_50 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_45, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_inc(x_3);
x_55 = lean_array_uset(x_54, x_6, x_3);
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_3, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_3, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_3, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_dec(x_53);
x_61 = (uint8_t)((x_46 << 24) >> 61);
x_62 = lean_expr_update_lambda(x_3, x_61, x_48, x_52);
lean_inc(x_62);
x_63 = lean_array_uset(x_60, x_6, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_50, 1, x_64);
lean_ctor_set(x_50, 0, x_62);
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_3);
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_44);
lean_ctor_set(x_66, 2, x_45);
lean_ctor_set_uint64(x_66, sizeof(void*)*3, x_46);
x_67 = (uint8_t)((x_46 << 24) >> 61);
x_68 = lean_expr_update_lambda(x_66, x_67, x_48, x_52);
lean_inc(x_68);
x_69 = lean_array_uset(x_65, x_6, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_50, 1, x_70);
lean_ctor_set(x_50, 0, x_68);
return x_50;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_50, 0);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_50);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_inc(x_3);
x_74 = lean_array_uset(x_73, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_75 = x_3;
} else {
 lean_dec_ref(x_3);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(6, 3, 8);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_43);
lean_ctor_set(x_77, 1, x_44);
lean_ctor_set(x_77, 2, x_45);
lean_ctor_set_uint64(x_77, sizeof(void*)*3, x_46);
x_78 = (uint8_t)((x_46 << 24) >> 61);
x_79 = lean_expr_update_lambda(x_77, x_78, x_48, x_71);
lean_inc(x_79);
x_80 = lean_array_uset(x_76, x_6, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 2);
lean_inc(x_85);
x_86 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_84);
x_87 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_84, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_85);
x_90 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_85, x_89);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_inc(x_3);
x_95 = lean_array_uset(x_94, x_6, x_3);
x_96 = !lean_is_exclusive(x_3);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_3, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_3, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_3, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_101 = (uint8_t)((x_86 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_88, x_92);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_6, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_90, 1, x_104);
lean_ctor_set(x_90, 0, x_102);
return x_90;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_105 = lean_ctor_get(x_93, 1);
lean_inc(x_105);
lean_dec(x_93);
x_106 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_106, 0, x_83);
lean_ctor_set(x_106, 1, x_84);
lean_ctor_set(x_106, 2, x_85);
lean_ctor_set_uint64(x_106, sizeof(void*)*3, x_86);
x_107 = (uint8_t)((x_86 << 24) >> 61);
x_108 = lean_expr_update_forall(x_106, x_107, x_88, x_92);
lean_inc(x_108);
x_109 = lean_array_uset(x_105, x_6, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_90, 1, x_110);
lean_ctor_set(x_90, 0, x_108);
return x_90;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_90, 0);
x_112 = lean_ctor_get(x_90, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_90);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_inc(x_3);
x_114 = lean_array_uset(x_113, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_115 = x_3;
} else {
 lean_dec_ref(x_3);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(7, 3, 8);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_83);
lean_ctor_set(x_117, 1, x_84);
lean_ctor_set(x_117, 2, x_85);
lean_ctor_set_uint64(x_117, sizeof(void*)*3, x_86);
x_118 = (uint8_t)((x_86 << 24) >> 61);
x_119 = lean_expr_update_forall(x_117, x_118, x_88, x_111);
lean_inc(x_119);
x_120 = lean_array_uset(x_116, x_6, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
case 8:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint64_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_123 = lean_ctor_get(x_3, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_3, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_3, 3);
lean_inc(x_126);
x_127 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_124);
x_128 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_124, x_4);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_125);
x_131 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_125, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_126);
x_134 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_126, x_133);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_inc(x_3);
x_139 = lean_array_uset(x_138, x_6, x_3);
x_140 = !lean_is_exclusive(x_3);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_3, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_3, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_3, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_3, 0);
lean_dec(x_144);
x_145 = lean_ctor_get(x_137, 1);
lean_inc(x_145);
lean_dec(x_137);
x_146 = lean_expr_update_let(x_3, x_129, x_132, x_136);
lean_inc(x_146);
x_147 = lean_array_uset(x_145, x_6, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_134, 1, x_148);
lean_ctor_set(x_134, 0, x_146);
return x_134;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_3);
x_149 = lean_ctor_get(x_137, 1);
lean_inc(x_149);
lean_dec(x_137);
x_150 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_150, 0, x_123);
lean_ctor_set(x_150, 1, x_124);
lean_ctor_set(x_150, 2, x_125);
lean_ctor_set(x_150, 3, x_126);
lean_ctor_set_uint64(x_150, sizeof(void*)*4, x_127);
x_151 = lean_expr_update_let(x_150, x_129, x_132, x_136);
lean_inc(x_151);
x_152 = lean_array_uset(x_149, x_6, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_139);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_134, 1, x_153);
lean_ctor_set(x_134, 0, x_151);
return x_134;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_134, 0);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_134);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_inc(x_3);
x_157 = lean_array_uset(x_156, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_158 = x_3;
} else {
 lean_dec_ref(x_3);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(8, 4, 8);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_123);
lean_ctor_set(x_160, 1, x_124);
lean_ctor_set(x_160, 2, x_125);
lean_ctor_set(x_160, 3, x_126);
lean_ctor_set_uint64(x_160, sizeof(void*)*4, x_127);
x_161 = lean_expr_update_let(x_160, x_129, x_132, x_154);
lean_inc(x_161);
x_162 = lean_array_uset(x_159, x_6, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_157);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
case 10:
{
lean_object* x_165; lean_object* x_166; uint64_t x_167; lean_object* x_168; uint8_t x_169; 
x_165 = lean_ctor_get(x_3, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_3, 1);
lean_inc(x_166);
x_167 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_166);
x_168 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_166, x_4);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_inc(x_3);
x_173 = lean_array_uset(x_172, x_6, x_3);
x_174 = !lean_is_exclusive(x_3);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_3, 1);
lean_dec(x_175);
x_176 = lean_ctor_get(x_3, 0);
lean_dec(x_176);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_dec(x_171);
x_178 = lean_expr_update_mdata(x_3, x_170);
lean_inc(x_178);
x_179 = lean_array_uset(x_177, x_6, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_168, 1, x_180);
lean_ctor_set(x_168, 0, x_178);
return x_168;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_3);
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
lean_dec(x_171);
x_182 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_182, 0, x_165);
lean_ctor_set(x_182, 1, x_166);
lean_ctor_set_uint64(x_182, sizeof(void*)*2, x_167);
x_183 = lean_expr_update_mdata(x_182, x_170);
lean_inc(x_183);
x_184 = lean_array_uset(x_181, x_6, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_173);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_168, 1, x_185);
lean_ctor_set(x_168, 0, x_183);
return x_168;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_186 = lean_ctor_get(x_168, 0);
x_187 = lean_ctor_get(x_168, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_168);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_inc(x_3);
x_189 = lean_array_uset(x_188, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_190 = x_3;
} else {
 lean_dec_ref(x_3);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(10, 2, 8);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_165);
lean_ctor_set(x_192, 1, x_166);
lean_ctor_set_uint64(x_192, sizeof(void*)*2, x_167);
x_193 = lean_expr_update_mdata(x_192, x_186);
lean_inc(x_193);
x_194 = lean_array_uset(x_191, x_6, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
case 11:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_3, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_3, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_3, 2);
lean_inc(x_199);
x_200 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_199);
x_201 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_199, x_4);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_201, 1);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_inc(x_3);
x_206 = lean_array_uset(x_205, x_6, x_3);
x_207 = !lean_is_exclusive(x_3);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_3, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_3, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_3, 0);
lean_dec(x_210);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_dec(x_204);
x_212 = lean_expr_update_proj(x_3, x_203);
lean_inc(x_212);
x_213 = lean_array_uset(x_211, x_6, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_206);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_201, 1, x_214);
lean_ctor_set(x_201, 0, x_212);
return x_201;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_3);
x_215 = lean_ctor_get(x_204, 1);
lean_inc(x_215);
lean_dec(x_204);
x_216 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_216, 0, x_197);
lean_ctor_set(x_216, 1, x_198);
lean_ctor_set(x_216, 2, x_199);
lean_ctor_set_uint64(x_216, sizeof(void*)*3, x_200);
x_217 = lean_expr_update_proj(x_216, x_203);
lean_inc(x_217);
x_218 = lean_array_uset(x_215, x_6, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_206);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_201, 1, x_219);
lean_ctor_set(x_201, 0, x_217);
return x_201;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_220 = lean_ctor_get(x_201, 0);
x_221 = lean_ctor_get(x_201, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_201);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_inc(x_3);
x_223 = lean_array_uset(x_222, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_224 = x_3;
} else {
 lean_dec_ref(x_3);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(11, 3, 8);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_197);
lean_ctor_set(x_226, 1, x_198);
lean_ctor_set(x_226, 2, x_199);
lean_ctor_set_uint64(x_226, sizeof(void*)*3, x_200);
x_227 = lean_expr_update_proj(x_226, x_220);
lean_inc(x_227);
x_228 = lean_array_uset(x_225, x_6, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_223);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
case 12:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_3);
x_231 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
x_232 = l_unreachable_x21___rarg(x_231);
x_233 = lean_apply_1(x_232, x_4);
return x_233;
}
default: 
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_3);
lean_ctor_set(x_234, 1, x_4);
return x_234;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_10, 2);
x_13 = lean_ctor_get(x_10, 4);
x_14 = lean_ctor_get(x_10, 1);
lean_dec(x_14);
x_15 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_16 = lean_name_mk_string(x_12, x_15);
x_17 = 8192;
x_18 = l_Lean_Expr_ReplaceImpl_initCache;
x_19 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_17, x_13, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_PreDefinition_inhabited___closed__1;
lean_ctor_set(x_10, 4, x_20);
lean_ctor_set(x_10, 2, x_16);
lean_ctor_set(x_10, 1, x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = x_10;
x_25 = lean_array_fset(x_9, x_2, x_24);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_25;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 2);
x_30 = lean_ctor_get(x_10, 3);
x_31 = lean_ctor_get(x_10, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_32 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_33 = lean_name_mk_string(x_29, x_32);
x_34 = 8192;
x_35 = l_Lean_Expr_ReplaceImpl_initCache;
x_36 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_34, x_31, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Elab_PreDefinition_inhabited___closed__1;
x_39 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_30);
lean_ctor_set(x_39, 4, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_27);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_2, x_40);
x_42 = x_39;
x_43 = lean_array_fset(x_9, x_2, x_42);
lean_dec(x_2);
x_2 = x_41;
x_3 = x_43;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_addAndCompileUnsafeRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3(x_1, x_10, x_9);
lean_dec(x_1);
x_12 = x_11;
x_13 = l_Lean_Elab_addAndCompileUnsafe(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_12);
return x_13;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_addAndCompileUnsafeRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_addAndCompileUnsafeRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_SCC(lean_object*);
lean_object* initialize_Lean_Meta_AbstractNestedProofs(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_DefView(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_PreDefinition_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SCC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractNestedProofs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_MkInhabitant(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_PreDefinition_inhabited___closed__1 = _init_l_Lean_Elab_PreDefinition_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_PreDefinition_inhabited___closed__1);
l_Lean_Elab_PreDefinition_inhabited___closed__2 = _init_l_Lean_Elab_PreDefinition_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_PreDefinition_inhabited___closed__2);
l_Lean_Elab_PreDefinition_inhabited = _init_l_Lean_Elab_PreDefinition_inhabited();
lean_mark_persistent(l_Lean_Elab_PreDefinition_inhabited);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
