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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_5__shareCommon___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Declaration_inhabited;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Std_ShareCommon_State_empty;
lean_object* l_Lean_Elab_addAndCompileUnsafeRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_inhabited;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* lean_state_sharecommon(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Elab_fixLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_fixLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafeRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_5__shareCommon(lean_object*);
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_applyAttributesOf___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PreDefinition_inhabited___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_List_map___main___at_Lean_Elab_addAndCompileUnsafe___spec__1(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_PreDefinition_inhabited___closed__1;
extern lean_object* l_Lean_Compiler_mkUnsafeRecName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_fixLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_Std_ShareCommonT_withShareCommon___at___private_Lean_Elab_PreDefinition_Basic_5__shareCommon___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l___private_Lean_Elab_PreDefinition_Basic_3__collectLevelParamsExpr(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_PreDefinition_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Elab_PreDefinition_inhabited___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_Elab_PreDefinition_inhabited___closed__1;
x_4 = lean_box(0);
x_5 = l_Lean_Expr_Inhabited___closed__1;
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
lean_object* _init_l_Lean_Elab_PreDefinition_inhabited() {
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
lean_dec(x_3);
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
lean_inc(x_3);
x_21 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_3);
x_24 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
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
lean_inc(x_3);
x_38 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_3);
x_41 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
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
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_22 = l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_4);
x_25 = l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
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
x_39 = l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_4);
x_42 = l___private_Lean_Elab_PreDefinition_Basic_1__levelMVarToParamExpr(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
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
lean_object* l___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = x_1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux___spec__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = x_12;
x_14 = lean_apply_8(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_13 = l___private_Lean_Elab_PreDefinition_Basic_2__levelMVarToParamPreDeclsAux(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
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
lean_object* l___private_Lean_Elab_PreDefinition_Basic_3__collectLevelParamsExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_CollectLevelParams_main___main(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = l___private_Lean_Elab_PreDefinition_Basic_3__collectLevelParamsExpr(x_9, x_3);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 4);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l___private_Lean_Elab_PreDefinition_Basic_3__collectLevelParamsExpr(x_12, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_14;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___closed__1;
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___spec__1(x_1, x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_ShareCommonT_withShareCommon___at___private_Lean_Elab_PreDefinition_Basic_5__shareCommon___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_state_sharecommon(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_5__shareCommon___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Basic_5__shareCommon(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = x_1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Basic_5__shareCommon___spec__2), 3, 2);
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
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_161; lean_object* x_162; size_t x_163; uint8_t x_164; 
x_7 = lean_ptr_addr(x_5);
x_8 = x_4 == 0 ? 0 : x_7 % x_4;
x_161 = lean_ctor_get(x_6, 0);
lean_inc(x_161);
x_162 = lean_array_uget(x_161, x_8);
x_163 = lean_ptr_addr(x_162);
lean_dec(x_162);
x_164 = x_163 == x_7;
if (x_164 == 0)
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_5, 0);
lean_inc(x_165);
x_166 = lean_array_get_size(x_2);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(x_1, x_165, x_2, x_166, x_167);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_165);
lean_dec(x_161);
x_169 = lean_box(0);
x_9 = x_169;
goto block_160;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = l_Lean_mkConst(x_165, x_3);
x_171 = lean_array_uset(x_161, x_8, x_5);
x_172 = lean_ctor_get(x_6, 1);
lean_inc(x_172);
lean_dec(x_6);
lean_inc(x_170);
x_173 = lean_array_uset(x_172, x_8, x_170);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
else
{
lean_object* x_176; 
lean_dec(x_161);
x_176 = lean_box(0);
x_9 = x_176;
goto block_160;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_3);
x_177 = lean_ctor_get(x_6, 1);
lean_inc(x_177);
x_178 = lean_array_uget(x_177, x_8);
lean_dec(x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_6);
return x_179;
}
block_160:
{
lean_dec(x_9);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_10, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_11, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_inc(x_5);
x_20 = lean_array_uset(x_19, x_8, x_5);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_expr_update_app(x_5, x_13, x_17);
lean_inc(x_22);
x_23 = lean_array_uset(x_21, x_8, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_inc(x_5);
x_28 = lean_array_uset(x_27, x_8, x_5);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_expr_update_app(x_5, x_13, x_25);
lean_inc(x_30);
x_31 = lean_array_uset(x_29, x_8, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_3);
x_37 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_34, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_35, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_inc(x_5);
x_45 = lean_array_uset(x_44, x_8, x_5);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = (uint8_t)((x_36 << 24) >> 61);
x_48 = lean_expr_update_lambda(x_5, x_47, x_38, x_42);
lean_inc(x_48);
x_49 = lean_array_uset(x_46, x_8, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_40, 1, x_50);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_inc(x_5);
x_54 = lean_array_uset(x_53, x_8, x_5);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = (uint8_t)((x_36 << 24) >> 61);
x_57 = lean_expr_update_lambda(x_5, x_56, x_38, x_51);
lean_inc(x_57);
x_58 = lean_array_uset(x_55, x_8, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
case 7:
{
lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_3);
x_64 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_62, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_5);
x_72 = lean_array_uset(x_71, x_8, x_5);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_63 << 24) >> 61);
x_75 = lean_expr_update_forall(x_5, x_74, x_65, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_8, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_67, 1, x_77);
lean_ctor_set(x_67, 0, x_75);
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_inc(x_5);
x_81 = lean_array_uset(x_80, x_8, x_5);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = (uint8_t)((x_63 << 24) >> 61);
x_84 = lean_expr_update_forall(x_5, x_83, x_65, x_78);
lean_inc(x_84);
x_85 = lean_array_uset(x_82, x_8, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
case 8:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_5, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_5, 3);
lean_inc(x_90);
lean_inc(x_3);
x_91 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_88, x_6);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_3);
x_94 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_89, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_90, x_96);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_inc(x_5);
x_102 = lean_array_uset(x_101, x_8, x_5);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_expr_update_let(x_5, x_92, x_95, x_99);
lean_inc(x_104);
x_105 = lean_array_uset(x_103, x_8, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_97, 1, x_106);
lean_ctor_set(x_97, 0, x_104);
return x_97;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_97, 0);
x_108 = lean_ctor_get(x_97, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_97);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_inc(x_5);
x_110 = lean_array_uset(x_109, x_8, x_5);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_expr_update_let(x_5, x_92, x_95, x_107);
lean_inc(x_112);
x_113 = lean_array_uset(x_111, x_8, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
x_117 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_116, x_6);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_inc(x_5);
x_122 = lean_array_uset(x_121, x_8, x_5);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_expr_update_mdata(x_5, x_119);
lean_inc(x_124);
x_125 = lean_array_uset(x_123, x_8, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_117, 1, x_126);
lean_ctor_set(x_117, 0, x_124);
return x_117;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_127 = lean_ctor_get(x_117, 0);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_117);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_inc(x_5);
x_130 = lean_array_uset(x_129, x_8, x_5);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_expr_update_mdata(x_5, x_127);
lean_inc(x_132);
x_133 = lean_array_uset(x_131, x_8, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
case 11:
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_5, 2);
lean_inc(x_136);
x_137 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4, x_136, x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_inc(x_5);
x_142 = lean_array_uset(x_141, x_8, x_5);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_expr_update_proj(x_5, x_139);
lean_inc(x_144);
x_145 = lean_array_uset(x_143, x_8, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_137, 1, x_146);
lean_ctor_set(x_137, 0, x_144);
return x_137;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_147 = lean_ctor_get(x_137, 0);
x_148 = lean_ctor_get(x_137, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_137);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_inc(x_5);
x_150 = lean_array_uset(x_149, x_8, x_5);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_expr_update_proj(x_5, x_147);
lean_inc(x_152);
x_153 = lean_array_uset(x_151, x_8, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
case 12:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_5);
lean_dec(x_3);
x_156 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_157 = l_unreachable_x21___rarg(x_156);
x_158 = lean_apply_1(x_157, x_6);
return x_158;
}
default: 
{
lean_object* x_159; 
lean_dec(x_3);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_5);
lean_ctor_set(x_159, 1, x_6);
return x_159;
}
}
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_161; lean_object* x_162; size_t x_163; uint8_t x_164; 
x_7 = lean_ptr_addr(x_5);
x_8 = x_4 == 0 ? 0 : x_7 % x_4;
x_161 = lean_ctor_get(x_6, 0);
lean_inc(x_161);
x_162 = lean_array_uget(x_161, x_8);
x_163 = lean_ptr_addr(x_162);
lean_dec(x_162);
x_164 = x_163 == x_7;
if (x_164 == 0)
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_5, 0);
lean_inc(x_165);
x_166 = lean_array_get_size(x_2);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Array_anyRangeMAux___main___at_Lean_Elab_fixLevelParams___spec__1(x_1, x_165, x_2, x_166, x_167);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_165);
lean_dec(x_161);
x_169 = lean_box(0);
x_9 = x_169;
goto block_160;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = l_Lean_mkConst(x_165, x_3);
x_171 = lean_array_uset(x_161, x_8, x_5);
x_172 = lean_ctor_get(x_6, 1);
lean_inc(x_172);
lean_dec(x_6);
lean_inc(x_170);
x_173 = lean_array_uset(x_172, x_8, x_170);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
else
{
lean_object* x_176; 
lean_dec(x_161);
x_176 = lean_box(0);
x_9 = x_176;
goto block_160;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_3);
x_177 = lean_ctor_get(x_6, 1);
lean_inc(x_177);
x_178 = lean_array_uget(x_177, x_8);
lean_dec(x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_6);
return x_179;
}
block_160:
{
lean_dec(x_9);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_10, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_11, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_inc(x_5);
x_20 = lean_array_uset(x_19, x_8, x_5);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_expr_update_app(x_5, x_13, x_17);
lean_inc(x_22);
x_23 = lean_array_uset(x_21, x_8, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_inc(x_5);
x_28 = lean_array_uset(x_27, x_8, x_5);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_expr_update_app(x_5, x_13, x_25);
lean_inc(x_30);
x_31 = lean_array_uset(x_29, x_8, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_3);
x_37 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_34, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_35, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_inc(x_5);
x_45 = lean_array_uset(x_44, x_8, x_5);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = (uint8_t)((x_36 << 24) >> 61);
x_48 = lean_expr_update_lambda(x_5, x_47, x_38, x_42);
lean_inc(x_48);
x_49 = lean_array_uset(x_46, x_8, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_40, 1, x_50);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_inc(x_5);
x_54 = lean_array_uset(x_53, x_8, x_5);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = (uint8_t)((x_36 << 24) >> 61);
x_57 = lean_expr_update_lambda(x_5, x_56, x_38, x_51);
lean_inc(x_57);
x_58 = lean_array_uset(x_55, x_8, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
case 7:
{
lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_3);
x_64 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_62, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_5);
x_72 = lean_array_uset(x_71, x_8, x_5);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_63 << 24) >> 61);
x_75 = lean_expr_update_forall(x_5, x_74, x_65, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_8, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_67, 1, x_77);
lean_ctor_set(x_67, 0, x_75);
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_inc(x_5);
x_81 = lean_array_uset(x_80, x_8, x_5);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = (uint8_t)((x_63 << 24) >> 61);
x_84 = lean_expr_update_forall(x_5, x_83, x_65, x_78);
lean_inc(x_84);
x_85 = lean_array_uset(x_82, x_8, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
case 8:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_5, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_5, 3);
lean_inc(x_90);
lean_inc(x_3);
x_91 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_88, x_6);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_3);
x_94 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_89, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_90, x_96);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_inc(x_5);
x_102 = lean_array_uset(x_101, x_8, x_5);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_expr_update_let(x_5, x_92, x_95, x_99);
lean_inc(x_104);
x_105 = lean_array_uset(x_103, x_8, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_97, 1, x_106);
lean_ctor_set(x_97, 0, x_104);
return x_97;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_97, 0);
x_108 = lean_ctor_get(x_97, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_97);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_inc(x_5);
x_110 = lean_array_uset(x_109, x_8, x_5);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_expr_update_let(x_5, x_92, x_95, x_107);
lean_inc(x_112);
x_113 = lean_array_uset(x_111, x_8, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
x_117 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_116, x_6);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_inc(x_5);
x_122 = lean_array_uset(x_121, x_8, x_5);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_expr_update_mdata(x_5, x_119);
lean_inc(x_124);
x_125 = lean_array_uset(x_123, x_8, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_117, 1, x_126);
lean_ctor_set(x_117, 0, x_124);
return x_117;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_127 = lean_ctor_get(x_117, 0);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_117);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_inc(x_5);
x_130 = lean_array_uset(x_129, x_8, x_5);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_expr_update_mdata(x_5, x_127);
lean_inc(x_132);
x_133 = lean_array_uset(x_131, x_8, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
case 11:
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_5, 2);
lean_inc(x_136);
x_137 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4, x_136, x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_inc(x_5);
x_142 = lean_array_uset(x_141, x_8, x_5);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_expr_update_proj(x_5, x_139);
lean_inc(x_144);
x_145 = lean_array_uset(x_143, x_8, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_137, 1, x_146);
lean_ctor_set(x_137, 0, x_144);
return x_137;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_147 = lean_ctor_get(x_137, 0);
x_148 = lean_ctor_get(x_137, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_137);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_inc(x_5);
x_150 = lean_array_uset(x_149, x_8, x_5);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_expr_update_proj(x_5, x_147);
lean_inc(x_152);
x_153 = lean_array_uset(x_151, x_8, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
case 12:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_5);
lean_dec(x_3);
x_156 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_157 = l_unreachable_x21___rarg(x_156);
x_158 = lean_apply_1(x_157, x_6);
return x_158;
}
default: 
{
lean_object* x_159; 
lean_dec(x_3);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_5);
lean_ctor_set(x_159, 1, x_6);
return x_159;
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
x_11 = l___private_Lean_Elab_PreDefinition_Basic_5__shareCommon(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_applyAttributesOf___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_1, x_3, x_2, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_16, x_1, x_18, x_19, x_8, x_9, x_10);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_Elab_applyAttributesOf(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_2, x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_applyAttributes___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_applyAttributes___at_Lean_Elab_applyAttributesOf___spec__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
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
lean_dec(x_3);
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
lean_object* l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 2);
lean_dec(x_18);
x_19 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_15, 2, x_19);
x_20 = lean_st_ref_set(x_8, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Elab_abstractNestedProofs(x_1, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get_uint8(x_23, sizeof(void*)*5);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_23, 4);
lean_inc(x_36);
switch (x_31) {
case 0:
{
lean_object* x_99; lean_object* x_100; uint32_t x_101; uint32_t x_102; uint32_t x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_34);
lean_ctor_set(x_99, 1, x_32);
lean_ctor_set(x_99, 2, x_35);
lean_inc(x_36);
x_100 = l_Lean_getMaxHeight(x_30, x_36);
x_101 = lean_unbox_uint32(x_100);
lean_dec(x_100);
x_102 = 1;
x_103 = x_101 + x_102;
x_104 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_104, 0, x_103);
x_105 = lean_ctor_get_uint8(x_33, sizeof(void*)*2 + 3);
lean_dec(x_33);
x_106 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_36);
lean_ctor_set(x_106, 2, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*3, x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_37 = x_107;
goto block_98;
}
case 1:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_33);
lean_dec(x_30);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_34);
lean_ctor_set(x_108, 1, x_32);
lean_ctor_set(x_108, 2, x_35);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_36);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_37 = x_110;
goto block_98;
}
case 2:
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
x_111 = l_Lean_Declaration_inhabited;
x_112 = l_unreachable_x21___rarg(x_111);
x_37 = x_112;
goto block_98;
}
case 3:
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_30);
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_34);
lean_ctor_set(x_113, 1, x_32);
lean_ctor_set(x_113, 2, x_35);
x_114 = lean_ctor_get_uint8(x_33, sizeof(void*)*2 + 3);
lean_dec(x_33);
x_115 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_114);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_37 = x_116;
goto block_98;
}
default: 
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_30);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_34);
lean_ctor_set(x_117, 1, x_32);
lean_ctor_set(x_117, 2, x_35);
x_118 = lean_ctor_get_uint8(x_33, sizeof(void*)*2 + 3);
lean_dec(x_33);
x_119 = lean_box(1);
x_120 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_36);
lean_ctor_set(x_120, 2, x_119);
lean_ctor_set_uint8(x_120, sizeof(void*)*3, x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_37 = x_121;
goto block_98;
}
}
block_98:
{
lean_object* x_38; 
lean_inc(x_7);
lean_inc(x_3);
x_38 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_mkOptionalNode___closed__2;
x_41 = lean_array_push(x_40, x_23);
x_42 = 0;
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
x_44 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_42, x_41, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_44) == 0)
{
if (x_2 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 1;
x_47 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_46, x_41, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_41);
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
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
lean_dec(x_44);
x_59 = l_Lean_Elab_DefKind_isTheorem(x_31);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_7);
lean_inc(x_3);
x_60 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_37);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = 1;
x_63 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_62, x_41, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_41);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
return x_63;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_63, 0);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; lean_object* x_79; 
lean_dec(x_37);
x_78 = 1;
x_79 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_78, x_41, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_41);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_79);
if (x_86 == 0)
{
return x_79;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_79, 0);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_79);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_44);
if (x_90 == 0)
{
return x_44;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_44, 0);
x_92 = lean_ctor_get(x_44, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_44);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_37);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_38);
if (x_94 == 0)
{
return x_38;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_38, 0);
x_96 = lean_ctor_get(x_38, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_38);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_22, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_22, 1);
lean_inc(x_123);
lean_dec(x_22);
x_124 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_123);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_124, 0);
lean_dec(x_126);
lean_ctor_set_tag(x_124, 1);
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_15, 0);
x_130 = lean_ctor_get(x_15, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_15);
x_131 = l_Lean_TraceState_Inhabited___closed__1;
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_131);
x_133 = lean_st_ref_set(x_8, x_132, x_16);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_135 = l_Lean_Elab_abstractNestedProofs(x_1, x_5, x_6, x_7, x_8, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_3);
x_138 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_137);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_st_ref_get(x_8, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get_uint8(x_136, sizeof(void*)*5);
x_145 = lean_ctor_get(x_136, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_136, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_136, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_136, 4);
lean_inc(x_149);
switch (x_144) {
case 0:
{
lean_object* x_206; lean_object* x_207; uint32_t x_208; uint32_t x_209; uint32_t x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_206 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_206, 0, x_147);
lean_ctor_set(x_206, 1, x_145);
lean_ctor_set(x_206, 2, x_148);
lean_inc(x_149);
x_207 = l_Lean_getMaxHeight(x_143, x_149);
x_208 = lean_unbox_uint32(x_207);
lean_dec(x_207);
x_209 = 1;
x_210 = x_208 + x_209;
x_211 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_211, 0, x_210);
x_212 = lean_ctor_get_uint8(x_146, sizeof(void*)*2 + 3);
lean_dec(x_146);
x_213 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_213, 0, x_206);
lean_ctor_set(x_213, 1, x_149);
lean_ctor_set(x_213, 2, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*3, x_212);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_150 = x_214;
goto block_205;
}
case 1:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_146);
lean_dec(x_143);
x_215 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_215, 0, x_147);
lean_ctor_set(x_215, 1, x_145);
lean_ctor_set(x_215, 2, x_148);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_149);
x_217 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_217, 0, x_216);
x_150 = x_217;
goto block_205;
}
case 2:
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_143);
x_218 = l_Lean_Declaration_inhabited;
x_219 = l_unreachable_x21___rarg(x_218);
x_150 = x_219;
goto block_205;
}
case 3:
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_143);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_147);
lean_ctor_set(x_220, 1, x_145);
lean_ctor_set(x_220, 2, x_148);
x_221 = lean_ctor_get_uint8(x_146, sizeof(void*)*2 + 3);
lean_dec(x_146);
x_222 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_149);
lean_ctor_set_uint8(x_222, sizeof(void*)*2, x_221);
x_223 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_150 = x_223;
goto block_205;
}
default: 
{
lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_143);
x_224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_224, 0, x_147);
lean_ctor_set(x_224, 1, x_145);
lean_ctor_set(x_224, 2, x_148);
x_225 = lean_ctor_get_uint8(x_146, sizeof(void*)*2 + 3);
lean_dec(x_146);
x_226 = lean_box(1);
x_227 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_149);
lean_ctor_set(x_227, 2, x_226);
lean_ctor_set_uint8(x_227, sizeof(void*)*3, x_225);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_150 = x_228;
goto block_205;
}
}
block_205:
{
lean_object* x_151; 
lean_inc(x_7);
lean_inc(x_3);
x_151 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_150, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = l_Lean_mkOptionalNode___closed__2;
x_154 = lean_array_push(x_153, x_136);
x_155 = 0;
x_156 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
x_157 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_155, x_154, x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_152);
if (lean_obj_tag(x_157) == 0)
{
if (x_2 == 0)
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; 
lean_dec(x_150);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = 1;
x_160 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_159, x_154, x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_158);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_154);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_160, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_167 = x_160;
} else {
 lean_dec_ref(x_160);
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
else
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_157, 1);
lean_inc(x_169);
lean_dec(x_157);
x_170 = l_Lean_Elab_DefKind_isTheorem(x_144);
if (x_170 == 0)
{
lean_object* x_171; 
lean_inc(x_7);
lean_inc(x_3);
x_171 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_150, x_3, x_4, x_5, x_6, x_7, x_8, x_169);
lean_dec(x_150);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = 1;
x_174 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_173, x_154, x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_172);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_154);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
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
x_177 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_174, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_154);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_183 = lean_ctor_get(x_171, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_171, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_185 = x_171;
} else {
 lean_dec_ref(x_171);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
uint8_t x_187; lean_object* x_188; 
lean_dec(x_150);
x_187 = 1;
x_188 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_187, x_154, x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_169);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_154);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
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
x_191 = lean_box(0);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_189);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_195 = x_188;
} else {
 lean_dec_ref(x_188);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_197 = lean_ctor_get(x_157, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_157, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_199 = x_157;
} else {
 lean_dec_ref(x_157);
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
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_150);
lean_dec(x_136);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_201 = lean_ctor_get(x_151, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_151, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_203 = x_151;
} else {
 lean_dec_ref(x_151);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = lean_ctor_get(x_135, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_135, 1);
lean_inc(x_230);
lean_dec(x_135);
x_231 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_230);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
 lean_ctor_set_tag(x_234, 1);
}
lean_ctor_set(x_234, 0, x_229);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_10 = l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_14, x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_18 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesOf___spec__2(x_20, x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_2);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_159; lean_object* x_160; size_t x_161; uint8_t x_162; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_159 = lean_ctor_get(x_4, 0);
lean_inc(x_159);
x_160 = lean_array_uget(x_159, x_6);
x_161 = lean_ptr_addr(x_160);
lean_dec(x_160);
x_162 = x_161 == x_5;
if (x_162 == 0)
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_3, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_3, 1);
lean_inc(x_164);
x_165 = lean_array_get_size(x_1);
x_166 = lean_unsigned_to_nat(0u);
x_167 = l_Array_anyRangeMAux___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__1(x_1, x_163, x_1, x_165, x_166);
lean_dec(x_165);
if (x_167 == 0)
{
lean_object* x_168; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_159);
x_168 = lean_box(0);
x_7 = x_168;
goto block_158;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_170 = lean_name_mk_string(x_163, x_169);
x_171 = l_Lean_mkConst(x_170, x_164);
x_172 = lean_array_uset(x_159, x_6, x_3);
x_173 = lean_ctor_get(x_4, 1);
lean_inc(x_173);
lean_dec(x_4);
lean_inc(x_171);
x_174 = lean_array_uset(x_173, x_6, x_171);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
lean_object* x_177; 
lean_dec(x_159);
x_177 = lean_box(0);
x_7 = x_177;
goto block_158;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_159);
lean_dec(x_3);
x_178 = lean_ctor_get(x_4, 1);
lean_inc(x_178);
x_179 = lean_array_uget(x_178, x_6);
lean_dec(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_4);
return x_180;
}
block_158:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_8, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_inc(x_3);
x_18 = lean_array_uset(x_17, x_6, x_3);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_expr_update_app(x_3, x_11, x_15);
lean_inc(x_20);
x_21 = lean_array_uset(x_19, x_6, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_inc(x_3);
x_26 = lean_array_uset(x_25, x_6, x_3);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_expr_update_app(x_3, x_11, x_23);
lean_inc(x_28);
x_29 = lean_array_uset(x_27, x_6, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
case 6:
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_35 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_32, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_33, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_inc(x_3);
x_43 = lean_array_uset(x_42, x_6, x_3);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = (uint8_t)((x_34 << 24) >> 61);
x_46 = lean_expr_update_lambda(x_3, x_45, x_36, x_40);
lean_inc(x_46);
x_47 = lean_array_uset(x_44, x_6, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_38, 1, x_48);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_inc(x_3);
x_52 = lean_array_uset(x_51, x_6, x_3);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = (uint8_t)((x_34 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_3, x_54, x_36, x_49);
lean_inc(x_55);
x_56 = lean_array_uset(x_53, x_6, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_62 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_59, x_4);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_60, x_64);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_inc(x_3);
x_70 = lean_array_uset(x_69, x_6, x_3);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = (uint8_t)((x_61 << 24) >> 61);
x_73 = lean_expr_update_forall(x_3, x_72, x_63, x_67);
lean_inc(x_73);
x_74 = lean_array_uset(x_71, x_6, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_65, 1, x_75);
lean_ctor_set(x_65, 0, x_73);
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_65, 0);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_65);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_inc(x_3);
x_79 = lean_array_uset(x_78, x_6, x_3);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = (uint8_t)((x_61 << 24) >> 61);
x_82 = lean_expr_update_forall(x_3, x_81, x_63, x_76);
lean_inc(x_82);
x_83 = lean_array_uset(x_80, x_6, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
case 8:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 3);
lean_inc(x_88);
x_89 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_86, x_4);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_87, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_88, x_94);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_inc(x_3);
x_100 = lean_array_uset(x_99, x_6, x_3);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_expr_update_let(x_3, x_90, x_93, x_97);
lean_inc(x_102);
x_103 = lean_array_uset(x_101, x_6, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_95, 1, x_104);
lean_ctor_set(x_95, 0, x_102);
return x_95;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_95, 0);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_95);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_inc(x_3);
x_108 = lean_array_uset(x_107, x_6, x_3);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_expr_update_let(x_3, x_90, x_93, x_105);
lean_inc(x_110);
x_111 = lean_array_uset(x_109, x_6, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
case 10:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_3, 1);
lean_inc(x_114);
x_115 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_114, x_4);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_6, x_3);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_expr_update_mdata(x_3, x_117);
lean_inc(x_122);
x_123 = lean_array_uset(x_121, x_6, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_115, 1, x_124);
lean_ctor_set(x_115, 0, x_122);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_inc(x_3);
x_128 = lean_array_uset(x_127, x_6, x_3);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_expr_update_mdata(x_3, x_125);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_6, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
case 11:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_3, 2);
lean_inc(x_134);
x_135 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_addAndCompileUnsafeRec___spec__2(x_1, x_2, x_134, x_4);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_inc(x_3);
x_140 = lean_array_uset(x_139, x_6, x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_expr_update_proj(x_3, x_137);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_6, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_135, 1, x_144);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_135, 0);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_135);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_3);
x_148 = lean_array_uset(x_147, x_6, x_3);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_expr_update_proj(x_3, x_145);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_6, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
case 12:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_3);
x_154 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_155 = l_unreachable_x21___rarg(x_154);
x_156 = lean_apply_1(x_155, x_4);
return x_156;
}
default: 
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_3);
lean_ctor_set(x_157, 1, x_4);
return x_157;
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
l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_4__getLevelParamsPreDecls___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
