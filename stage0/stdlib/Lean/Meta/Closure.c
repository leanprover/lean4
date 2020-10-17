// Lean compiler output
// Module: Lean.Meta.Closure
// Imports: Init Std.ShareCommon Lean.MetavarContext Lean.Environment Lean.Util.FoldConsts Lean.Meta.Basic Lean.Meta.Check
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
lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1___boxed(lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4;
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__3;
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_Inhabited;
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_ToProcessElement_inhabited___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*);
extern lean_object* l_Lean_Level_updateMax_x21___closed__2;
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__1;
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process(lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalDecl_Inhabited;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitExpr___spec__7(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitExpr___spec__5(lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object*);
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__1;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__2;
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_ToProcessElement_inhabited;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process___main(lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Meta_Closure_process___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_Closure_visitExpr___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process___main___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateSucc_x21___closed__2;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_mkValueTypeClosure___spec__2(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_mkValueTypeClosure___spec__1(lean_object*);
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_Closure_process___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__2;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Closure_ToProcessElement_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_ToProcessElement_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_ToProcessElement_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_level_eq(x_4, x_1);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_level_eq(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_hash(x_4);
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
x_16 = l_Lean_Level_hash(x_12);
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_Closure_visitLevel___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_level_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_level_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Level_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_2, x_3, x_10);
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
x_23 = l_Lean_Level_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_53; 
x_53 = l_Lean_Level_hasMVar(x_2);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Level_hasParam(x_2);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_9);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_st_ref_get(x_4, x_9);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_10 = x_57;
x_11 = x_58;
goto block_52;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_st_ref_get(x_4, x_9);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_10 = x_60;
x_11 = x_61;
goto block_52;
}
block_52:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_12, x_2);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_inc(x_4);
lean_inc(x_2);
x_14 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_15);
x_22 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_21, x_2, x_15);
lean_ctor_set(x_18, 0, x_22);
x_23 = lean_st_ref_set(x_4, x_18, x_19);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_15);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get(x_18, 7);
x_36 = lean_ctor_get(x_18, 8);
x_37 = lean_ctor_get(x_18, 9);
x_38 = lean_ctor_get(x_18, 10);
x_39 = lean_ctor_get(x_18, 11);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
lean_inc(x_15);
x_40 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_28, x_2, x_15);
x_41 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
lean_ctor_set(x_41, 9, x_37);
lean_ctor_set(x_41, 10, x_38);
lean_ctor_set(x_41, 11, x_39);
x_42 = lean_st_ref_set(x_4, x_41, x_19);
lean_dec(x_4);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_4);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_13, 0);
lean_inc(x_50);
lean_dec(x_13);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_equal(x_4, x_1);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_equal(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitExpr___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_Closure_visitExpr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitExpr___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitExpr___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at_Lean_Meta_Closure_visitExpr___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_expr_equal(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_expr_equal(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitExpr___spec__5(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(x_2, x_3, x_10);
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
x_26 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitExpr___spec__5(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_53; 
x_53 = l_Lean_Expr_hasLevelParam(x_2);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_hasFVar(x_2);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Expr_hasMVar(x_2);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_9);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_st_ref_get(x_4, x_9);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_10 = x_58;
x_11 = x_59;
goto block_52;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_st_ref_get(x_4, x_9);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_10 = x_61;
x_11 = x_62;
goto block_52;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_st_ref_get(x_4, x_9);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_10 = x_64;
x_11 = x_65;
goto block_52;
}
block_52:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_12, x_2);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_inc(x_4);
lean_inc(x_2);
x_14 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_15);
x_22 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_21, x_2, x_15);
lean_ctor_set(x_18, 1, x_22);
x_23 = lean_st_ref_set(x_4, x_18, x_19);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_15);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get(x_18, 7);
x_36 = lean_ctor_get(x_18, 8);
x_37 = lean_ctor_get(x_18, 9);
x_38 = lean_ctor_get(x_18, 10);
x_39 = lean_ctor_get(x_18, 11);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
lean_inc(x_15);
x_40 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_29, x_2, x_15);
x_41 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
lean_ctor_set(x_41, 9, x_37);
lean_ctor_set(x_41, 10, x_38);
lean_ctor_set(x_41, 11, x_39);
x_42 = lean_st_ref_set(x_4, x_41, x_19);
lean_dec(x_4);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_4);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_13, 0);
lean_inc(x_50);
lean_dec(x_13);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Closure_mkNewLevelParam___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
x_14 = l_Lean_Name_appendIndexAfter(x_13, x_12);
x_15 = lean_st_ref_take(x_3, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_16, 2);
x_20 = lean_ctor_get(x_16, 3);
x_21 = lean_ctor_get(x_16, 4);
lean_inc(x_14);
x_22 = lean_array_push(x_19, x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_20, x_23);
lean_dec(x_20);
x_25 = lean_array_push(x_21, x_1);
lean_ctor_set(x_16, 4, x_25);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_22);
x_26 = lean_st_ref_set(x_3, x_16, x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lean_mkLevelParam(x_14);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_mkLevelParam(x_14);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
x_35 = lean_ctor_get(x_16, 2);
x_36 = lean_ctor_get(x_16, 3);
x_37 = lean_ctor_get(x_16, 4);
x_38 = lean_ctor_get(x_16, 5);
x_39 = lean_ctor_get(x_16, 6);
x_40 = lean_ctor_get(x_16, 7);
x_41 = lean_ctor_get(x_16, 8);
x_42 = lean_ctor_get(x_16, 9);
x_43 = lean_ctor_get(x_16, 10);
x_44 = lean_ctor_get(x_16, 11);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
lean_inc(x_14);
x_45 = lean_array_push(x_35, x_14);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_36, x_46);
lean_dec(x_36);
x_48 = lean_array_push(x_37, x_1);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_34);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_38);
lean_ctor_set(x_49, 6, x_39);
lean_ctor_set(x_49, 7, x_40);
lean_ctor_set(x_49, 8, x_41);
lean_ctor_set(x_49, 9, x_42);
lean_ctor_set(x_49, 10, x_43);
lean_ctor_set(x_49, 11, x_44);
x_50 = lean_st_ref_set(x_3, x_49, x_17);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = l_Lean_mkLevelParam(x_14);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_53; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_53 = l_Lean_Level_hasMVar(x_19);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Level_hasParam(x_19);
if (x_54 == 0)
{
x_9 = x_19;
x_10 = x_8;
goto block_17;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_st_ref_get(x_3, x_8);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_20 = x_56;
x_21 = x_57;
goto block_52;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_st_ref_get(x_3, x_8);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_20 = x_59;
x_21 = x_60;
goto block_52;
}
block_52:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_22, x_19);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_inc(x_19);
x_24 = l_Lean_Meta_Closure_collectLevelAux___main(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_25);
x_32 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_31, x_19, x_25);
lean_ctor_set(x_28, 0, x_32);
x_33 = lean_st_ref_set(x_3, x_28, x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_9 = x_25;
x_10 = x_34;
goto block_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
x_37 = lean_ctor_get(x_28, 2);
x_38 = lean_ctor_get(x_28, 3);
x_39 = lean_ctor_get(x_28, 4);
x_40 = lean_ctor_get(x_28, 5);
x_41 = lean_ctor_get(x_28, 6);
x_42 = lean_ctor_get(x_28, 7);
x_43 = lean_ctor_get(x_28, 8);
x_44 = lean_ctor_get(x_28, 9);
x_45 = lean_ctor_get(x_28, 10);
x_46 = lean_ctor_get(x_28, 11);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
lean_inc(x_25);
x_47 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_35, x_19, x_25);
x_48 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_36);
lean_ctor_set(x_48, 2, x_37);
lean_ctor_set(x_48, 3, x_38);
lean_ctor_set(x_48, 4, x_39);
lean_ctor_set(x_48, 5, x_40);
lean_ctor_set(x_48, 6, x_41);
lean_ctor_set(x_48, 7, x_42);
lean_ctor_set(x_48, 8, x_43);
lean_ctor_set(x_48, 9, x_44);
lean_ctor_set(x_48, 10, x_45);
lean_ctor_set(x_48, 11, x_46);
x_49 = lean_st_ref_set(x_3, x_48, x_29);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_9 = x_25;
x_10 = x_50;
goto block_17;
}
}
else
{
lean_object* x_51; 
lean_dec(x_19);
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_9 = x_51;
x_10 = x_21;
goto block_17;
}
}
}
case 2:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_116; lean_object* x_117; uint8_t x_149; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_149 = l_Lean_Level_hasMVar(x_61);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Level_hasParam(x_61);
if (x_150 == 0)
{
x_63 = x_61;
x_64 = x_8;
goto block_115;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_st_ref_get(x_3, x_8);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_116 = x_152;
x_117 = x_153;
goto block_148;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_st_ref_get(x_3, x_8);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_116 = x_155;
x_117 = x_156;
goto block_148;
}
block_115:
{
lean_object* x_65; lean_object* x_66; lean_object* x_74; lean_object* x_75; uint8_t x_107; 
x_107 = l_Lean_Level_hasMVar(x_62);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Level_hasParam(x_62);
if (x_108 == 0)
{
x_65 = x_62;
x_66 = x_64;
goto block_73;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_st_ref_get(x_3, x_64);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_74 = x_110;
x_75 = x_111;
goto block_106;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_st_ref_get(x_3, x_64);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_74 = x_113;
x_75 = x_114;
goto block_106;
}
block_73:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_level_update_max(x_1, x_63, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_1);
x_69 = l_Lean_Level_Inhabited;
x_70 = l_Lean_Level_updateMax_x21___closed__2;
x_71 = lean_panic_fn(x_69, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
}
block_106:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_76, x_62);
lean_dec(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_inc(x_62);
x_78 = l_Lean_Meta_Closure_collectLevelAux___main(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_75);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_take(x_3, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_79);
x_86 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_85, x_62, x_79);
lean_ctor_set(x_82, 0, x_86);
x_87 = lean_st_ref_set(x_3, x_82, x_83);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_65 = x_79;
x_66 = x_88;
goto block_73;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 3);
x_93 = lean_ctor_get(x_82, 4);
x_94 = lean_ctor_get(x_82, 5);
x_95 = lean_ctor_get(x_82, 6);
x_96 = lean_ctor_get(x_82, 7);
x_97 = lean_ctor_get(x_82, 8);
x_98 = lean_ctor_get(x_82, 9);
x_99 = lean_ctor_get(x_82, 10);
x_100 = lean_ctor_get(x_82, 11);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
lean_inc(x_79);
x_101 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_89, x_62, x_79);
x_102 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
lean_ctor_set(x_102, 2, x_91);
lean_ctor_set(x_102, 3, x_92);
lean_ctor_set(x_102, 4, x_93);
lean_ctor_set(x_102, 5, x_94);
lean_ctor_set(x_102, 6, x_95);
lean_ctor_set(x_102, 7, x_96);
lean_ctor_set(x_102, 8, x_97);
lean_ctor_set(x_102, 9, x_98);
lean_ctor_set(x_102, 10, x_99);
lean_ctor_set(x_102, 11, x_100);
x_103 = lean_st_ref_set(x_3, x_102, x_83);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_65 = x_79;
x_66 = x_104;
goto block_73;
}
}
else
{
lean_object* x_105; 
lean_dec(x_62);
x_105 = lean_ctor_get(x_77, 0);
lean_inc(x_105);
lean_dec(x_77);
x_65 = x_105;
x_66 = x_75;
goto block_73;
}
}
}
block_148:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_118, x_61);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_inc(x_61);
x_120 = l_Lean_Meta_Closure_collectLevelAux___main(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_st_ref_take(x_3, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_121);
x_128 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_127, x_61, x_121);
lean_ctor_set(x_124, 0, x_128);
x_129 = lean_st_ref_set(x_3, x_124, x_125);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_63 = x_121;
x_64 = x_130;
goto block_115;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_131 = lean_ctor_get(x_124, 0);
x_132 = lean_ctor_get(x_124, 1);
x_133 = lean_ctor_get(x_124, 2);
x_134 = lean_ctor_get(x_124, 3);
x_135 = lean_ctor_get(x_124, 4);
x_136 = lean_ctor_get(x_124, 5);
x_137 = lean_ctor_get(x_124, 6);
x_138 = lean_ctor_get(x_124, 7);
x_139 = lean_ctor_get(x_124, 8);
x_140 = lean_ctor_get(x_124, 9);
x_141 = lean_ctor_get(x_124, 10);
x_142 = lean_ctor_get(x_124, 11);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_124);
lean_inc(x_121);
x_143 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_131, x_61, x_121);
x_144 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_132);
lean_ctor_set(x_144, 2, x_133);
lean_ctor_set(x_144, 3, x_134);
lean_ctor_set(x_144, 4, x_135);
lean_ctor_set(x_144, 5, x_136);
lean_ctor_set(x_144, 6, x_137);
lean_ctor_set(x_144, 7, x_138);
lean_ctor_set(x_144, 8, x_139);
lean_ctor_set(x_144, 9, x_140);
lean_ctor_set(x_144, 10, x_141);
lean_ctor_set(x_144, 11, x_142);
x_145 = lean_st_ref_set(x_3, x_144, x_125);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_63 = x_121;
x_64 = x_146;
goto block_115;
}
}
else
{
lean_object* x_147; 
lean_dec(x_61);
x_147 = lean_ctor_get(x_119, 0);
lean_inc(x_147);
lean_dec(x_119);
x_63 = x_147;
x_64 = x_117;
goto block_115;
}
}
}
case 3:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_212; lean_object* x_213; uint8_t x_245; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
x_245 = l_Lean_Level_hasMVar(x_157);
if (x_245 == 0)
{
uint8_t x_246; 
x_246 = l_Lean_Level_hasParam(x_157);
if (x_246 == 0)
{
x_159 = x_157;
x_160 = x_8;
goto block_211;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_st_ref_get(x_3, x_8);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_212 = x_248;
x_213 = x_249;
goto block_244;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_st_ref_get(x_3, x_8);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_212 = x_251;
x_213 = x_252;
goto block_244;
}
block_211:
{
lean_object* x_161; lean_object* x_162; lean_object* x_170; lean_object* x_171; uint8_t x_203; 
x_203 = l_Lean_Level_hasMVar(x_158);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = l_Lean_Level_hasParam(x_158);
if (x_204 == 0)
{
x_161 = x_158;
x_162 = x_160;
goto block_169;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_st_ref_get(x_3, x_160);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_170 = x_206;
x_171 = x_207;
goto block_202;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_st_ref_get(x_3, x_160);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_170 = x_209;
x_171 = x_210;
goto block_202;
}
block_169:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_level_update_imax(x_1, x_159, x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_1);
x_165 = l_Lean_Level_Inhabited;
x_166 = l_Lean_Level_updateIMax_x21___closed__2;
x_167 = lean_panic_fn(x_165, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_162);
return x_168;
}
}
block_202:
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_172, x_158);
lean_dec(x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_158);
x_174 = l_Lean_Meta_Closure_collectLevelAux___main(x_158, x_2, x_3, x_4, x_5, x_6, x_7, x_171);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_st_ref_take(x_3, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_178, 0);
lean_inc(x_175);
x_182 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_181, x_158, x_175);
lean_ctor_set(x_178, 0, x_182);
x_183 = lean_st_ref_set(x_3, x_178, x_179);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_161 = x_175;
x_162 = x_184;
goto block_169;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_185 = lean_ctor_get(x_178, 0);
x_186 = lean_ctor_get(x_178, 1);
x_187 = lean_ctor_get(x_178, 2);
x_188 = lean_ctor_get(x_178, 3);
x_189 = lean_ctor_get(x_178, 4);
x_190 = lean_ctor_get(x_178, 5);
x_191 = lean_ctor_get(x_178, 6);
x_192 = lean_ctor_get(x_178, 7);
x_193 = lean_ctor_get(x_178, 8);
x_194 = lean_ctor_get(x_178, 9);
x_195 = lean_ctor_get(x_178, 10);
x_196 = lean_ctor_get(x_178, 11);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_178);
lean_inc(x_175);
x_197 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_185, x_158, x_175);
x_198 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_186);
lean_ctor_set(x_198, 2, x_187);
lean_ctor_set(x_198, 3, x_188);
lean_ctor_set(x_198, 4, x_189);
lean_ctor_set(x_198, 5, x_190);
lean_ctor_set(x_198, 6, x_191);
lean_ctor_set(x_198, 7, x_192);
lean_ctor_set(x_198, 8, x_193);
lean_ctor_set(x_198, 9, x_194);
lean_ctor_set(x_198, 10, x_195);
lean_ctor_set(x_198, 11, x_196);
x_199 = lean_st_ref_set(x_3, x_198, x_179);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_161 = x_175;
x_162 = x_200;
goto block_169;
}
}
else
{
lean_object* x_201; 
lean_dec(x_158);
x_201 = lean_ctor_get(x_173, 0);
lean_inc(x_201);
lean_dec(x_173);
x_161 = x_201;
x_162 = x_171;
goto block_169;
}
}
}
block_244:
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_214, x_157);
lean_dec(x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_inc(x_157);
x_216 = l_Lean_Meta_Closure_collectLevelAux___main(x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_213);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_st_ref_take(x_3, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = !lean_is_exclusive(x_220);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_217);
x_224 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_223, x_157, x_217);
lean_ctor_set(x_220, 0, x_224);
x_225 = lean_st_ref_set(x_3, x_220, x_221);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_159 = x_217;
x_160 = x_226;
goto block_211;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_227 = lean_ctor_get(x_220, 0);
x_228 = lean_ctor_get(x_220, 1);
x_229 = lean_ctor_get(x_220, 2);
x_230 = lean_ctor_get(x_220, 3);
x_231 = lean_ctor_get(x_220, 4);
x_232 = lean_ctor_get(x_220, 5);
x_233 = lean_ctor_get(x_220, 6);
x_234 = lean_ctor_get(x_220, 7);
x_235 = lean_ctor_get(x_220, 8);
x_236 = lean_ctor_get(x_220, 9);
x_237 = lean_ctor_get(x_220, 10);
x_238 = lean_ctor_get(x_220, 11);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_220);
lean_inc(x_217);
x_239 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_227, x_157, x_217);
x_240 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_228);
lean_ctor_set(x_240, 2, x_229);
lean_ctor_set(x_240, 3, x_230);
lean_ctor_set(x_240, 4, x_231);
lean_ctor_set(x_240, 5, x_232);
lean_ctor_set(x_240, 6, x_233);
lean_ctor_set(x_240, 7, x_234);
lean_ctor_set(x_240, 8, x_235);
lean_ctor_set(x_240, 9, x_236);
lean_ctor_set(x_240, 10, x_237);
lean_ctor_set(x_240, 11, x_238);
x_241 = lean_st_ref_set(x_3, x_240, x_221);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_159 = x_217;
x_160 = x_242;
goto block_211;
}
}
else
{
lean_object* x_243; 
lean_dec(x_157);
x_243 = lean_ctor_get(x_215, 0);
lean_inc(x_243);
lean_dec(x_215);
x_159 = x_243;
x_160 = x_213;
goto block_211;
}
}
}
default: 
{
lean_object* x_253; 
x_253 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_253;
}
}
block_17:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_level_update_succ(x_1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = l_Lean_Level_Inhabited;
x_14 = l_Lean_Level_updateSucc_x21___closed__2;
x_15 = lean_panic_fn(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevelAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevelAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_48; 
x_48 = l_Lean_Level_hasMVar(x_1);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Level_hasParam(x_1);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_8);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_st_ref_get(x_3, x_8);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_9 = x_52;
x_10 = x_53;
goto block_47;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_st_ref_get(x_3, x_8);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_9 = x_55;
x_10 = x_56;
goto block_47;
}
block_47:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Closure_collectLevelAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_14);
x_21 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_20, x_1, x_14);
lean_ctor_set(x_17, 0, x_21);
x_22 = lean_st_ref_set(x_3, x_17, x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_14);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
x_29 = lean_ctor_get(x_17, 2);
x_30 = lean_ctor_get(x_17, 3);
x_31 = lean_ctor_get(x_17, 4);
x_32 = lean_ctor_get(x_17, 5);
x_33 = lean_ctor_get(x_17, 6);
x_34 = lean_ctor_get(x_17, 7);
x_35 = lean_ctor_get(x_17, 8);
x_36 = lean_ctor_get(x_17, 9);
x_37 = lean_ctor_get(x_17, 10);
x_38 = lean_ctor_get(x_17, 11);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
lean_inc(x_14);
x_39 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_27, x_1, x_14);
x_40 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_29);
lean_ctor_set(x_40, 3, x_30);
lean_ctor_set(x_40, 4, x_31);
lean_ctor_set(x_40, 5, x_32);
lean_ctor_set(x_40, 6, x_33);
lean_ctor_set(x_40, 7, x_34);
lean_ctor_set(x_40, 8, x_35);
lean_ctor_set(x_40, 9, x_36);
lean_ctor_set(x_40, 10, x_37);
lean_ctor_set(x_40, 11, x_38);
x_41 = lean_st_ref_set(x_3, x_40, x_18);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_12, 0);
lean_inc(x_45);
lean_dec(x_12);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_MetavarContext_instantiateMVars(x_15, x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_18);
x_19 = lean_st_ref_set(x_5, x_12, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_27 = l_Lean_MetavarContext_instantiateMVars(x_24, x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_st_ref_set(x_5, x_30, x_13);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_Closure_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_unbox(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_11);
x_13 = l_Lean_Meta_check(x_11, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_x");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 8);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
x_12 = l_Lean_Name_appendIndexAfter(x_11, x_10);
x_13 = lean_st_ref_take(x_1, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_14, 8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_14, 8, x_19);
x_20 = lean_st_ref_set(x_1, x_14, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_12);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_14, 5);
x_31 = lean_ctor_get(x_14, 6);
x_32 = lean_ctor_get(x_14, 7);
x_33 = lean_ctor_get(x_14, 8);
x_34 = lean_ctor_get(x_14, 9);
x_35 = lean_ctor_get(x_14, 10);
x_36 = lean_ctor_get(x_14, 11);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_33, x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_30);
lean_ctor_set(x_39, 6, x_31);
lean_ctor_set(x_39, 7, x_32);
lean_ctor_set(x_39, 8, x_38);
lean_ctor_set(x_39, 9, x_34);
lean_ctor_set(x_39, 10, x_35);
lean_ctor_set(x_39, 11, x_36);
x_40 = lean_st_ref_set(x_1, x_39, x_15);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkNextUserName___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Closure_mkNextUserName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 11);
x_14 = lean_array_push(x_13, x_1);
lean_ctor_set(x_10, 11, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get(x_10, 6);
x_29 = lean_ctor_get(x_10, 7);
x_30 = lean_ctor_get(x_10, 8);
x_31 = lean_ctor_get(x_10, 9);
x_32 = lean_ctor_get(x_10, 10);
x_33 = lean_ctor_get(x_10, 11);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_34 = lean_array_push(x_33, x_1);
x_35 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
lean_ctor_set(x_35, 5, x_27);
lean_ctor_set(x_35, 6, x_28);
lean_ctor_set(x_35, 7, x_29);
lean_ctor_set(x_35, 8, x_30);
lean_ctor_set(x_35, 9, x_31);
lean_ctor_set(x_35, 10, x_32);
lean_ctor_set(x_35, 11, x_34);
x_36 = lean_st_ref_set(x_3, x_35, x_11);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_pushToProcess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_local_ctx_find(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_name_mk_numeral(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_1, x_26, x_15);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_name_mk_numeral(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_32, x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_take(x_1, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 4, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_42);
x_45 = lean_st_ref_set(x_1, x_44, x_39);
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
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg___boxed), 2, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = lean_metavar_ctx_find_decl(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
x_15 = l_Lean_mkMVar(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_20, x_4, x_5, x_6, x_7, x_12);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = lean_metavar_ctx_find_decl(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = l_Lean_mkMVar(x_1);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_4, x_5, x_6, x_7, x_24);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Lean_Meta_Closure_collectLevel(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = l_Lean_Meta_Closure_collectLevel(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_18; lean_object* x_19; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_27);
x_28 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__1(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_45; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_45 = lean_unbox(x_2);
if (x_45 == 0)
{
lean_object* x_46; 
lean_free_object(x_28);
lean_dec(x_30);
x_46 = lean_box(0);
x_32 = x_46;
goto block_44;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_LocalDecl_value_x3f(x_30);
lean_dec(x_30);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_free_object(x_28);
x_48 = lean_box(0);
x_32 = x_48;
goto block_44;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_27);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_50 = l_Lean_Meta_Closure_preprocess(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_97; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_97 = l_Lean_Expr_hasLevelParam(x_51);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l_Lean_Expr_hasFVar(x_51);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Expr_hasMVar(x_51);
if (x_99 == 0)
{
lean_dec(x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_28, 1, x_52);
lean_ctor_set(x_28, 0, x_51);
return x_28;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_free_object(x_28);
x_100 = lean_st_ref_get(x_3, x_52);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_54 = x_101;
x_55 = x_102;
goto block_96;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_28);
x_103 = lean_st_ref_get(x_3, x_52);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_54 = x_104;
x_55 = x_105;
goto block_96;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_free_object(x_28);
x_106 = lean_st_ref_get(x_3, x_52);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_54 = x_107;
x_55 = x_108;
goto block_96;
}
block_96:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_56, x_51);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_dec(x_53);
lean_inc(x_51);
x_58 = l_Lean_Meta_Closure_collectExprAux___main(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_take(x_3, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_59);
x_66 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_65, x_51, x_59);
lean_ctor_set(x_62, 1, x_66);
x_67 = lean_st_ref_set(x_3, x_62, x_63);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_59);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_62, 0);
x_73 = lean_ctor_get(x_62, 1);
x_74 = lean_ctor_get(x_62, 2);
x_75 = lean_ctor_get(x_62, 3);
x_76 = lean_ctor_get(x_62, 4);
x_77 = lean_ctor_get(x_62, 5);
x_78 = lean_ctor_get(x_62, 6);
x_79 = lean_ctor_get(x_62, 7);
x_80 = lean_ctor_get(x_62, 8);
x_81 = lean_ctor_get(x_62, 9);
x_82 = lean_ctor_get(x_62, 10);
x_83 = lean_ctor_get(x_62, 11);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_62);
lean_inc(x_59);
x_84 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_73, x_51, x_59);
x_85 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_74);
lean_ctor_set(x_85, 3, x_75);
lean_ctor_set(x_85, 4, x_76);
lean_ctor_set(x_85, 5, x_77);
lean_ctor_set(x_85, 6, x_78);
lean_ctor_set(x_85, 7, x_79);
lean_ctor_set(x_85, 8, x_80);
lean_ctor_set(x_85, 9, x_81);
lean_ctor_set(x_85, 10, x_82);
lean_ctor_set(x_85, 11, x_83);
x_86 = lean_st_ref_set(x_3, x_85, x_63);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_59);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_51);
x_90 = !lean_is_exclusive(x_58);
if (x_90 == 0)
{
return x_58;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_58, 0);
x_92 = lean_ctor_get(x_58, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_58);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = lean_ctor_get(x_57, 0);
lean_inc(x_94);
lean_dec(x_57);
if (lean_is_scalar(x_53)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_53;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_55);
return x_95;
}
}
}
else
{
uint8_t x_109; 
lean_free_object(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_50);
if (x_109 == 0)
{
return x_50;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_50, 0);
x_111 = lean_ctor_get(x_50, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_50);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
block_44:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_32);
x_33 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg(x_7, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Meta_Closure_pushToProcess(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = l_Lean_mkFVar(x_34);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = l_Lean_mkFVar(x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_126; 
x_113 = lean_ctor_get(x_28, 0);
x_114 = lean_ctor_get(x_28, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_28);
x_126 = lean_unbox(x_2);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_113);
x_127 = lean_box(0);
x_115 = x_127;
goto block_125;
}
else
{
lean_object* x_128; 
x_128 = l_Lean_LocalDecl_value_x3f(x_113);
lean_dec(x_113);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_box(0);
x_115 = x_129;
goto block_125;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_27);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_131 = l_Lean_Meta_Closure_preprocess(x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_171; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_171 = l_Lean_Expr_hasLevelParam(x_132);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_132);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_132);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_134);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_132);
lean_ctor_set(x_174, 1, x_133);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_st_ref_get(x_3, x_133);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_135 = x_176;
x_136 = x_177;
goto block_170;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_st_ref_get(x_3, x_133);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_135 = x_179;
x_136 = x_180;
goto block_170;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_st_ref_get(x_3, x_133);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_135 = x_182;
x_136 = x_183;
goto block_170;
}
block_170:
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_137, x_132);
lean_dec(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
lean_dec(x_134);
lean_inc(x_132);
x_139 = l_Lean_Meta_Closure_collectExprAux___main(x_132, x_2, x_3, x_4, x_5, x_6, x_7, x_136);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_st_ref_take(x_3, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 5);
lean_inc(x_150);
x_151 = lean_ctor_get(x_143, 6);
lean_inc(x_151);
x_152 = lean_ctor_get(x_143, 7);
lean_inc(x_152);
x_153 = lean_ctor_get(x_143, 8);
lean_inc(x_153);
x_154 = lean_ctor_get(x_143, 9);
lean_inc(x_154);
x_155 = lean_ctor_get(x_143, 10);
lean_inc(x_155);
x_156 = lean_ctor_get(x_143, 11);
lean_inc(x_156);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 lean_ctor_release(x_143, 5);
 lean_ctor_release(x_143, 6);
 lean_ctor_release(x_143, 7);
 lean_ctor_release(x_143, 8);
 lean_ctor_release(x_143, 9);
 lean_ctor_release(x_143, 10);
 lean_ctor_release(x_143, 11);
 x_157 = x_143;
} else {
 lean_dec_ref(x_143);
 x_157 = lean_box(0);
}
lean_inc(x_140);
x_158 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_146, x_132, x_140);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 12, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_145);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_147);
lean_ctor_set(x_159, 3, x_148);
lean_ctor_set(x_159, 4, x_149);
lean_ctor_set(x_159, 5, x_150);
lean_ctor_set(x_159, 6, x_151);
lean_ctor_set(x_159, 7, x_152);
lean_ctor_set(x_159, 8, x_153);
lean_ctor_set(x_159, 9, x_154);
lean_ctor_set(x_159, 10, x_155);
lean_ctor_set(x_159, 11, x_156);
x_160 = lean_st_ref_set(x_3, x_159, x_144);
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
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_140);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_132);
x_164 = lean_ctor_get(x_139, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_139, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_166 = x_139;
} else {
 lean_dec_ref(x_139);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_168 = lean_ctor_get(x_138, 0);
lean_inc(x_168);
lean_dec(x_138);
if (lean_is_scalar(x_134)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_134;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_136);
return x_169;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_184 = lean_ctor_get(x_131, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_131, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_186 = x_131;
} else {
 lean_dec_ref(x_131);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
block_125:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_115);
x_116 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg(x_7, x_114);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_27);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_Lean_Meta_Closure_pushToProcess(x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_118);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = l_Lean_mkFVar(x_117);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_188 = !lean_is_exclusive(x_28);
if (x_188 == 0)
{
return x_28;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_28, 0);
x_190 = lean_ctor_get(x_28, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_28);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 2:
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_1, 0);
lean_inc(x_192);
x_193 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__3(x_192, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_246; lean_object* x_247; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_246 = lean_ctor_get(x_194, 2);
lean_inc(x_246);
lean_dec(x_194);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_247 = l_Lean_Meta_Closure_preprocess(x_246, x_2, x_3, x_4, x_5, x_6, x_7, x_195);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_287; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_287 = l_Lean_Expr_hasLevelParam(x_248);
if (x_287 == 0)
{
uint8_t x_288; 
x_288 = l_Lean_Expr_hasFVar(x_248);
if (x_288 == 0)
{
uint8_t x_289; 
x_289 = l_Lean_Expr_hasMVar(x_248);
if (x_289 == 0)
{
x_196 = x_248;
x_197 = x_249;
goto block_245;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_st_ref_get(x_3, x_249);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_250 = x_291;
x_251 = x_292;
goto block_286;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_st_ref_get(x_3, x_249);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_250 = x_294;
x_251 = x_295;
goto block_286;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_st_ref_get(x_3, x_249);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_250 = x_297;
x_251 = x_298;
goto block_286;
}
block_286:
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_252, x_248);
lean_dec(x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_248);
x_254 = l_Lean_Meta_Closure_collectExprAux___main(x_248, x_2, x_3, x_4, x_5, x_6, x_7, x_251);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_st_ref_take(x_3, x_256);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = !lean_is_exclusive(x_258);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_255);
x_262 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_261, x_248, x_255);
lean_ctor_set(x_258, 1, x_262);
x_263 = lean_st_ref_set(x_3, x_258, x_259);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_196 = x_255;
x_197 = x_264;
goto block_245;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_265 = lean_ctor_get(x_258, 0);
x_266 = lean_ctor_get(x_258, 1);
x_267 = lean_ctor_get(x_258, 2);
x_268 = lean_ctor_get(x_258, 3);
x_269 = lean_ctor_get(x_258, 4);
x_270 = lean_ctor_get(x_258, 5);
x_271 = lean_ctor_get(x_258, 6);
x_272 = lean_ctor_get(x_258, 7);
x_273 = lean_ctor_get(x_258, 8);
x_274 = lean_ctor_get(x_258, 9);
x_275 = lean_ctor_get(x_258, 10);
x_276 = lean_ctor_get(x_258, 11);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_258);
lean_inc(x_255);
x_277 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_266, x_248, x_255);
x_278 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_278, 0, x_265);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_278, 2, x_267);
lean_ctor_set(x_278, 3, x_268);
lean_ctor_set(x_278, 4, x_269);
lean_ctor_set(x_278, 5, x_270);
lean_ctor_set(x_278, 6, x_271);
lean_ctor_set(x_278, 7, x_272);
lean_ctor_set(x_278, 8, x_273);
lean_ctor_set(x_278, 9, x_274);
lean_ctor_set(x_278, 10, x_275);
lean_ctor_set(x_278, 11, x_276);
x_279 = lean_st_ref_set(x_3, x_278, x_259);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_196 = x_255;
x_197 = x_280;
goto block_245;
}
}
else
{
uint8_t x_281; 
lean_dec(x_248);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_254);
if (x_281 == 0)
{
return x_254;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_254, 0);
x_283 = lean_ctor_get(x_254, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_254);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
else
{
lean_object* x_285; 
lean_dec(x_248);
x_285 = lean_ctor_get(x_253, 0);
lean_inc(x_285);
lean_dec(x_253);
x_196 = x_285;
x_197 = x_251;
goto block_245;
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_247);
if (x_299 == 0)
{
return x_247;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_247, 0);
x_301 = lean_ctor_get(x_247, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_247);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
block_245:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_198 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg(x_7, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_200);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_st_ref_take(x_3, x_203);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = !lean_is_exclusive(x_205);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_208 = lean_ctor_get(x_205, 6);
x_209 = lean_ctor_get(x_205, 9);
x_210 = lean_unsigned_to_nat(0u);
x_211 = 0;
lean_inc(x_199);
x_212 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_199);
lean_ctor_set(x_212, 2, x_202);
lean_ctor_set(x_212, 3, x_196);
lean_ctor_set_uint8(x_212, sizeof(void*)*4, x_211);
x_213 = lean_array_push(x_208, x_212);
x_214 = lean_array_push(x_209, x_1);
lean_ctor_set(x_205, 9, x_214);
lean_ctor_set(x_205, 6, x_213);
x_215 = lean_st_ref_set(x_3, x_205, x_206);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_215, 0);
lean_dec(x_217);
x_218 = l_Lean_mkFVar(x_199);
lean_ctor_set(x_215, 0, x_218);
return x_215;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_220 = l_Lean_mkFVar(x_199);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_222 = lean_ctor_get(x_205, 0);
x_223 = lean_ctor_get(x_205, 1);
x_224 = lean_ctor_get(x_205, 2);
x_225 = lean_ctor_get(x_205, 3);
x_226 = lean_ctor_get(x_205, 4);
x_227 = lean_ctor_get(x_205, 5);
x_228 = lean_ctor_get(x_205, 6);
x_229 = lean_ctor_get(x_205, 7);
x_230 = lean_ctor_get(x_205, 8);
x_231 = lean_ctor_get(x_205, 9);
x_232 = lean_ctor_get(x_205, 10);
x_233 = lean_ctor_get(x_205, 11);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_205);
x_234 = lean_unsigned_to_nat(0u);
x_235 = 0;
lean_inc(x_199);
x_236 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_199);
lean_ctor_set(x_236, 2, x_202);
lean_ctor_set(x_236, 3, x_196);
lean_ctor_set_uint8(x_236, sizeof(void*)*4, x_235);
x_237 = lean_array_push(x_228, x_236);
x_238 = lean_array_push(x_231, x_1);
x_239 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_239, 0, x_222);
lean_ctor_set(x_239, 1, x_223);
lean_ctor_set(x_239, 2, x_224);
lean_ctor_set(x_239, 3, x_225);
lean_ctor_set(x_239, 4, x_226);
lean_ctor_set(x_239, 5, x_227);
lean_ctor_set(x_239, 6, x_237);
lean_ctor_set(x_239, 7, x_229);
lean_ctor_set(x_239, 8, x_230);
lean_ctor_set(x_239, 9, x_238);
lean_ctor_set(x_239, 10, x_232);
lean_ctor_set(x_239, 11, x_233);
x_240 = lean_st_ref_set(x_3, x_239, x_206);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
x_243 = l_Lean_mkFVar(x_199);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
}
}
else
{
uint8_t x_303; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_303 = !lean_is_exclusive(x_193);
if (x_303 == 0)
{
return x_193;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_193, 0);
x_305 = lean_ctor_get(x_193, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_193);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
case 3:
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_1, 0);
lean_inc(x_307);
x_308 = l_Lean_Meta_Closure_collectLevel(x_307, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_expr_update_sort(x_1, x_310);
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
x_314 = lean_expr_update_sort(x_1, x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
case 4:
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_1, 1);
lean_inc(x_316);
x_317 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4(x_316, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_317, 0);
x_320 = lean_expr_update_const(x_1, x_319);
lean_ctor_set(x_317, 0, x_320);
return x_317;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_317, 0);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_317);
x_323 = lean_expr_update_const(x_1, x_321);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
case 5:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_388; lean_object* x_389; uint8_t x_425; 
x_325 = lean_ctor_get(x_1, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_1, 1);
lean_inc(x_326);
x_425 = l_Lean_Expr_hasLevelParam(x_325);
if (x_425 == 0)
{
uint8_t x_426; 
x_426 = l_Lean_Expr_hasFVar(x_325);
if (x_426 == 0)
{
uint8_t x_427; 
x_427 = l_Lean_Expr_hasMVar(x_325);
if (x_427 == 0)
{
x_327 = x_325;
x_328 = x_8;
goto block_387;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_st_ref_get(x_3, x_8);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_388 = x_429;
x_389 = x_430;
goto block_424;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_st_ref_get(x_3, x_8);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_388 = x_432;
x_389 = x_433;
goto block_424;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_st_ref_get(x_3, x_8);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_388 = x_435;
x_389 = x_436;
goto block_424;
}
block_387:
{
lean_object* x_329; lean_object* x_330; lean_object* x_338; lean_object* x_339; uint8_t x_375; 
x_375 = l_Lean_Expr_hasLevelParam(x_326);
if (x_375 == 0)
{
uint8_t x_376; 
x_376 = l_Lean_Expr_hasFVar(x_326);
if (x_376 == 0)
{
uint8_t x_377; 
x_377 = l_Lean_Expr_hasMVar(x_326);
if (x_377 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_329 = x_326;
x_330 = x_328;
goto block_337;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_st_ref_get(x_3, x_328);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_338 = x_379;
x_339 = x_380;
goto block_374;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_st_ref_get(x_3, x_328);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_338 = x_382;
x_339 = x_383;
goto block_374;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_st_ref_get(x_3, x_328);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_338 = x_385;
x_339 = x_386;
goto block_374;
}
block_337:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_expr_update_app(x_1, x_327, x_329);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_329);
lean_dec(x_327);
lean_dec(x_1);
x_333 = l_Lean_Expr_Inhabited;
x_334 = l_Lean_Expr_updateApp_x21___closed__1;
x_335 = lean_panic_fn(x_333, x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_330);
return x_336;
}
}
block_374:
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_340, x_326);
lean_dec(x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
lean_inc(x_326);
x_342 = l_Lean_Meta_Closure_collectExprAux___main(x_326, x_2, x_3, x_4, x_5, x_6, x_7, x_339);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_st_ref_take(x_3, x_344);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = !lean_is_exclusive(x_346);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_343);
x_350 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_349, x_326, x_343);
lean_ctor_set(x_346, 1, x_350);
x_351 = lean_st_ref_set(x_3, x_346, x_347);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_329 = x_343;
x_330 = x_352;
goto block_337;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_353 = lean_ctor_get(x_346, 0);
x_354 = lean_ctor_get(x_346, 1);
x_355 = lean_ctor_get(x_346, 2);
x_356 = lean_ctor_get(x_346, 3);
x_357 = lean_ctor_get(x_346, 4);
x_358 = lean_ctor_get(x_346, 5);
x_359 = lean_ctor_get(x_346, 6);
x_360 = lean_ctor_get(x_346, 7);
x_361 = lean_ctor_get(x_346, 8);
x_362 = lean_ctor_get(x_346, 9);
x_363 = lean_ctor_get(x_346, 10);
x_364 = lean_ctor_get(x_346, 11);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_346);
lean_inc(x_343);
x_365 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_354, x_326, x_343);
x_366 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_366, 0, x_353);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set(x_366, 2, x_355);
lean_ctor_set(x_366, 3, x_356);
lean_ctor_set(x_366, 4, x_357);
lean_ctor_set(x_366, 5, x_358);
lean_ctor_set(x_366, 6, x_359);
lean_ctor_set(x_366, 7, x_360);
lean_ctor_set(x_366, 8, x_361);
lean_ctor_set(x_366, 9, x_362);
lean_ctor_set(x_366, 10, x_363);
lean_ctor_set(x_366, 11, x_364);
x_367 = lean_st_ref_set(x_3, x_366, x_347);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_329 = x_343;
x_330 = x_368;
goto block_337;
}
}
else
{
uint8_t x_369; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_1);
x_369 = !lean_is_exclusive(x_342);
if (x_369 == 0)
{
return x_342;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_342, 0);
x_371 = lean_ctor_get(x_342, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_342);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
lean_object* x_373; 
lean_dec(x_326);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_373 = lean_ctor_get(x_341, 0);
lean_inc(x_373);
lean_dec(x_341);
x_329 = x_373;
x_330 = x_339;
goto block_337;
}
}
}
block_424:
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_390, x_325);
lean_dec(x_390);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_325);
x_392 = l_Lean_Meta_Closure_collectExprAux___main(x_325, x_2, x_3, x_4, x_5, x_6, x_7, x_389);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_st_ref_take(x_3, x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = !lean_is_exclusive(x_396);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_393);
x_400 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_399, x_325, x_393);
lean_ctor_set(x_396, 1, x_400);
x_401 = lean_st_ref_set(x_3, x_396, x_397);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_327 = x_393;
x_328 = x_402;
goto block_387;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_403 = lean_ctor_get(x_396, 0);
x_404 = lean_ctor_get(x_396, 1);
x_405 = lean_ctor_get(x_396, 2);
x_406 = lean_ctor_get(x_396, 3);
x_407 = lean_ctor_get(x_396, 4);
x_408 = lean_ctor_get(x_396, 5);
x_409 = lean_ctor_get(x_396, 6);
x_410 = lean_ctor_get(x_396, 7);
x_411 = lean_ctor_get(x_396, 8);
x_412 = lean_ctor_get(x_396, 9);
x_413 = lean_ctor_get(x_396, 10);
x_414 = lean_ctor_get(x_396, 11);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_inc(x_408);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_396);
lean_inc(x_393);
x_415 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_404, x_325, x_393);
x_416 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_416, 0, x_403);
lean_ctor_set(x_416, 1, x_415);
lean_ctor_set(x_416, 2, x_405);
lean_ctor_set(x_416, 3, x_406);
lean_ctor_set(x_416, 4, x_407);
lean_ctor_set(x_416, 5, x_408);
lean_ctor_set(x_416, 6, x_409);
lean_ctor_set(x_416, 7, x_410);
lean_ctor_set(x_416, 8, x_411);
lean_ctor_set(x_416, 9, x_412);
lean_ctor_set(x_416, 10, x_413);
lean_ctor_set(x_416, 11, x_414);
x_417 = lean_st_ref_set(x_3, x_416, x_397);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_327 = x_393;
x_328 = x_418;
goto block_387;
}
}
else
{
uint8_t x_419; 
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_419 = !lean_is_exclusive(x_392);
if (x_419 == 0)
{
return x_392;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_392, 0);
x_421 = lean_ctor_get(x_392, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_392);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
}
}
else
{
lean_object* x_423; 
lean_dec(x_325);
x_423 = lean_ctor_get(x_391, 0);
lean_inc(x_423);
lean_dec(x_391);
x_327 = x_423;
x_328 = x_389;
goto block_387;
}
}
}
case 6:
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_502; lean_object* x_503; uint8_t x_539; 
x_437 = lean_ctor_get(x_1, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_1, 2);
lean_inc(x_438);
x_539 = l_Lean_Expr_hasLevelParam(x_437);
if (x_539 == 0)
{
uint8_t x_540; 
x_540 = l_Lean_Expr_hasFVar(x_437);
if (x_540 == 0)
{
uint8_t x_541; 
x_541 = l_Lean_Expr_hasMVar(x_437);
if (x_541 == 0)
{
x_439 = x_437;
x_440 = x_8;
goto block_501;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_st_ref_get(x_3, x_8);
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_502 = x_543;
x_503 = x_544;
goto block_538;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_st_ref_get(x_3, x_8);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_502 = x_546;
x_503 = x_547;
goto block_538;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_st_ref_get(x_3, x_8);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_502 = x_549;
x_503 = x_550;
goto block_538;
}
block_501:
{
lean_object* x_441; lean_object* x_442; lean_object* x_452; lean_object* x_453; uint8_t x_489; 
x_489 = l_Lean_Expr_hasLevelParam(x_438);
if (x_489 == 0)
{
uint8_t x_490; 
x_490 = l_Lean_Expr_hasFVar(x_438);
if (x_490 == 0)
{
uint8_t x_491; 
x_491 = l_Lean_Expr_hasMVar(x_438);
if (x_491 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_441 = x_438;
x_442 = x_440;
goto block_451;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_st_ref_get(x_3, x_440);
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
x_452 = x_493;
x_453 = x_494;
goto block_488;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_st_ref_get(x_3, x_440);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_452 = x_496;
x_453 = x_497;
goto block_488;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_st_ref_get(x_3, x_440);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_452 = x_499;
x_453 = x_500;
goto block_488;
}
block_451:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_444 = (uint8_t)((x_443 << 24) >> 61);
x_445 = lean_expr_update_lambda(x_1, x_444, x_439, x_441);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_442);
return x_446;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_441);
lean_dec(x_439);
lean_dec(x_1);
x_447 = l_Lean_Expr_Inhabited;
x_448 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_449 = lean_panic_fn(x_447, x_448);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_442);
return x_450;
}
}
block_488:
{
lean_object* x_454; lean_object* x_455; 
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_454, x_438);
lean_dec(x_454);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; 
lean_inc(x_438);
x_456 = l_Lean_Meta_Closure_collectExprAux___main(x_438, x_2, x_3, x_4, x_5, x_6, x_7, x_453);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_st_ref_take(x_3, x_458);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = !lean_is_exclusive(x_460);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_463 = lean_ctor_get(x_460, 1);
lean_inc(x_457);
x_464 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_463, x_438, x_457);
lean_ctor_set(x_460, 1, x_464);
x_465 = lean_st_ref_set(x_3, x_460, x_461);
x_466 = lean_ctor_get(x_465, 1);
lean_inc(x_466);
lean_dec(x_465);
x_441 = x_457;
x_442 = x_466;
goto block_451;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_467 = lean_ctor_get(x_460, 0);
x_468 = lean_ctor_get(x_460, 1);
x_469 = lean_ctor_get(x_460, 2);
x_470 = lean_ctor_get(x_460, 3);
x_471 = lean_ctor_get(x_460, 4);
x_472 = lean_ctor_get(x_460, 5);
x_473 = lean_ctor_get(x_460, 6);
x_474 = lean_ctor_get(x_460, 7);
x_475 = lean_ctor_get(x_460, 8);
x_476 = lean_ctor_get(x_460, 9);
x_477 = lean_ctor_get(x_460, 10);
x_478 = lean_ctor_get(x_460, 11);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_inc(x_472);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_460);
lean_inc(x_457);
x_479 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_468, x_438, x_457);
x_480 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_480, 0, x_467);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set(x_480, 2, x_469);
lean_ctor_set(x_480, 3, x_470);
lean_ctor_set(x_480, 4, x_471);
lean_ctor_set(x_480, 5, x_472);
lean_ctor_set(x_480, 6, x_473);
lean_ctor_set(x_480, 7, x_474);
lean_ctor_set(x_480, 8, x_475);
lean_ctor_set(x_480, 9, x_476);
lean_ctor_set(x_480, 10, x_477);
lean_ctor_set(x_480, 11, x_478);
x_481 = lean_st_ref_set(x_3, x_480, x_461);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec(x_481);
x_441 = x_457;
x_442 = x_482;
goto block_451;
}
}
else
{
uint8_t x_483; 
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_1);
x_483 = !lean_is_exclusive(x_456);
if (x_483 == 0)
{
return x_456;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_456, 0);
x_485 = lean_ctor_get(x_456, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_456);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
else
{
lean_object* x_487; 
lean_dec(x_438);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_487 = lean_ctor_get(x_455, 0);
lean_inc(x_487);
lean_dec(x_455);
x_441 = x_487;
x_442 = x_453;
goto block_451;
}
}
}
block_538:
{
lean_object* x_504; lean_object* x_505; 
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
x_505 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_504, x_437);
lean_dec(x_504);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_437);
x_506 = l_Lean_Meta_Closure_collectExprAux___main(x_437, x_2, x_3, x_4, x_5, x_6, x_7, x_503);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_st_ref_take(x_3, x_508);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec(x_509);
x_512 = !lean_is_exclusive(x_510);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = lean_ctor_get(x_510, 1);
lean_inc(x_507);
x_514 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_513, x_437, x_507);
lean_ctor_set(x_510, 1, x_514);
x_515 = lean_st_ref_set(x_3, x_510, x_511);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_439 = x_507;
x_440 = x_516;
goto block_501;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_517 = lean_ctor_get(x_510, 0);
x_518 = lean_ctor_get(x_510, 1);
x_519 = lean_ctor_get(x_510, 2);
x_520 = lean_ctor_get(x_510, 3);
x_521 = lean_ctor_get(x_510, 4);
x_522 = lean_ctor_get(x_510, 5);
x_523 = lean_ctor_get(x_510, 6);
x_524 = lean_ctor_get(x_510, 7);
x_525 = lean_ctor_get(x_510, 8);
x_526 = lean_ctor_get(x_510, 9);
x_527 = lean_ctor_get(x_510, 10);
x_528 = lean_ctor_get(x_510, 11);
lean_inc(x_528);
lean_inc(x_527);
lean_inc(x_526);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
lean_inc(x_522);
lean_inc(x_521);
lean_inc(x_520);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_510);
lean_inc(x_507);
x_529 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_518, x_437, x_507);
x_530 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_530, 0, x_517);
lean_ctor_set(x_530, 1, x_529);
lean_ctor_set(x_530, 2, x_519);
lean_ctor_set(x_530, 3, x_520);
lean_ctor_set(x_530, 4, x_521);
lean_ctor_set(x_530, 5, x_522);
lean_ctor_set(x_530, 6, x_523);
lean_ctor_set(x_530, 7, x_524);
lean_ctor_set(x_530, 8, x_525);
lean_ctor_set(x_530, 9, x_526);
lean_ctor_set(x_530, 10, x_527);
lean_ctor_set(x_530, 11, x_528);
x_531 = lean_st_ref_set(x_3, x_530, x_511);
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
lean_dec(x_531);
x_439 = x_507;
x_440 = x_532;
goto block_501;
}
}
else
{
uint8_t x_533; 
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_533 = !lean_is_exclusive(x_506);
if (x_533 == 0)
{
return x_506;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_506, 0);
x_535 = lean_ctor_get(x_506, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_506);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
return x_536;
}
}
}
else
{
lean_object* x_537; 
lean_dec(x_437);
x_537 = lean_ctor_get(x_505, 0);
lean_inc(x_537);
lean_dec(x_505);
x_439 = x_537;
x_440 = x_503;
goto block_501;
}
}
}
case 7:
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_616; lean_object* x_617; uint8_t x_653; 
x_551 = lean_ctor_get(x_1, 1);
lean_inc(x_551);
x_552 = lean_ctor_get(x_1, 2);
lean_inc(x_552);
x_653 = l_Lean_Expr_hasLevelParam(x_551);
if (x_653 == 0)
{
uint8_t x_654; 
x_654 = l_Lean_Expr_hasFVar(x_551);
if (x_654 == 0)
{
uint8_t x_655; 
x_655 = l_Lean_Expr_hasMVar(x_551);
if (x_655 == 0)
{
x_553 = x_551;
x_554 = x_8;
goto block_615;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_st_ref_get(x_3, x_8);
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_616 = x_657;
x_617 = x_658;
goto block_652;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_st_ref_get(x_3, x_8);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
lean_dec(x_659);
x_616 = x_660;
x_617 = x_661;
goto block_652;
}
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_st_ref_get(x_3, x_8);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_616 = x_663;
x_617 = x_664;
goto block_652;
}
block_615:
{
lean_object* x_555; lean_object* x_556; lean_object* x_566; lean_object* x_567; uint8_t x_603; 
x_603 = l_Lean_Expr_hasLevelParam(x_552);
if (x_603 == 0)
{
uint8_t x_604; 
x_604 = l_Lean_Expr_hasFVar(x_552);
if (x_604 == 0)
{
uint8_t x_605; 
x_605 = l_Lean_Expr_hasMVar(x_552);
if (x_605 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_555 = x_552;
x_556 = x_554;
goto block_565;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_st_ref_get(x_3, x_554);
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_566 = x_607;
x_567 = x_608;
goto block_602;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_st_ref_get(x_3, x_554);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_566 = x_610;
x_567 = x_611;
goto block_602;
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = lean_st_ref_get(x_3, x_554);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_566 = x_613;
x_567 = x_614;
goto block_602;
}
block_565:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_557; uint8_t x_558; lean_object* x_559; lean_object* x_560; 
x_557 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_558 = (uint8_t)((x_557 << 24) >> 61);
x_559 = lean_expr_update_forall(x_1, x_558, x_553, x_555);
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_556);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_555);
lean_dec(x_553);
lean_dec(x_1);
x_561 = l_Lean_Expr_Inhabited;
x_562 = l_Lean_Expr_updateForallE_x21___closed__1;
x_563 = lean_panic_fn(x_561, x_562);
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_556);
return x_564;
}
}
block_602:
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_568, x_552);
lean_dec(x_568);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; 
lean_inc(x_552);
x_570 = l_Lean_Meta_Closure_collectExprAux___main(x_552, x_2, x_3, x_4, x_5, x_6, x_7, x_567);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
x_573 = lean_st_ref_take(x_3, x_572);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = !lean_is_exclusive(x_574);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_577 = lean_ctor_get(x_574, 1);
lean_inc(x_571);
x_578 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_577, x_552, x_571);
lean_ctor_set(x_574, 1, x_578);
x_579 = lean_st_ref_set(x_3, x_574, x_575);
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
x_555 = x_571;
x_556 = x_580;
goto block_565;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_581 = lean_ctor_get(x_574, 0);
x_582 = lean_ctor_get(x_574, 1);
x_583 = lean_ctor_get(x_574, 2);
x_584 = lean_ctor_get(x_574, 3);
x_585 = lean_ctor_get(x_574, 4);
x_586 = lean_ctor_get(x_574, 5);
x_587 = lean_ctor_get(x_574, 6);
x_588 = lean_ctor_get(x_574, 7);
x_589 = lean_ctor_get(x_574, 8);
x_590 = lean_ctor_get(x_574, 9);
x_591 = lean_ctor_get(x_574, 10);
x_592 = lean_ctor_get(x_574, 11);
lean_inc(x_592);
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_587);
lean_inc(x_586);
lean_inc(x_585);
lean_inc(x_584);
lean_inc(x_583);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_574);
lean_inc(x_571);
x_593 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_582, x_552, x_571);
x_594 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_594, 0, x_581);
lean_ctor_set(x_594, 1, x_593);
lean_ctor_set(x_594, 2, x_583);
lean_ctor_set(x_594, 3, x_584);
lean_ctor_set(x_594, 4, x_585);
lean_ctor_set(x_594, 5, x_586);
lean_ctor_set(x_594, 6, x_587);
lean_ctor_set(x_594, 7, x_588);
lean_ctor_set(x_594, 8, x_589);
lean_ctor_set(x_594, 9, x_590);
lean_ctor_set(x_594, 10, x_591);
lean_ctor_set(x_594, 11, x_592);
x_595 = lean_st_ref_set(x_3, x_594, x_575);
x_596 = lean_ctor_get(x_595, 1);
lean_inc(x_596);
lean_dec(x_595);
x_555 = x_571;
x_556 = x_596;
goto block_565;
}
}
else
{
uint8_t x_597; 
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_1);
x_597 = !lean_is_exclusive(x_570);
if (x_597 == 0)
{
return x_570;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_570, 0);
x_599 = lean_ctor_get(x_570, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_570);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
return x_600;
}
}
}
else
{
lean_object* x_601; 
lean_dec(x_552);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_601 = lean_ctor_get(x_569, 0);
lean_inc(x_601);
lean_dec(x_569);
x_555 = x_601;
x_556 = x_567;
goto block_565;
}
}
}
block_652:
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_618, x_551);
lean_dec(x_618);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_551);
x_620 = l_Lean_Meta_Closure_collectExprAux___main(x_551, x_2, x_3, x_4, x_5, x_6, x_7, x_617);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = lean_st_ref_take(x_3, x_622);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
x_626 = !lean_is_exclusive(x_624);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_627 = lean_ctor_get(x_624, 1);
lean_inc(x_621);
x_628 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_627, x_551, x_621);
lean_ctor_set(x_624, 1, x_628);
x_629 = lean_st_ref_set(x_3, x_624, x_625);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
lean_dec(x_629);
x_553 = x_621;
x_554 = x_630;
goto block_615;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_631 = lean_ctor_get(x_624, 0);
x_632 = lean_ctor_get(x_624, 1);
x_633 = lean_ctor_get(x_624, 2);
x_634 = lean_ctor_get(x_624, 3);
x_635 = lean_ctor_get(x_624, 4);
x_636 = lean_ctor_get(x_624, 5);
x_637 = lean_ctor_get(x_624, 6);
x_638 = lean_ctor_get(x_624, 7);
x_639 = lean_ctor_get(x_624, 8);
x_640 = lean_ctor_get(x_624, 9);
x_641 = lean_ctor_get(x_624, 10);
x_642 = lean_ctor_get(x_624, 11);
lean_inc(x_642);
lean_inc(x_641);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
lean_inc(x_633);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_624);
lean_inc(x_621);
x_643 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_632, x_551, x_621);
x_644 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_644, 0, x_631);
lean_ctor_set(x_644, 1, x_643);
lean_ctor_set(x_644, 2, x_633);
lean_ctor_set(x_644, 3, x_634);
lean_ctor_set(x_644, 4, x_635);
lean_ctor_set(x_644, 5, x_636);
lean_ctor_set(x_644, 6, x_637);
lean_ctor_set(x_644, 7, x_638);
lean_ctor_set(x_644, 8, x_639);
lean_ctor_set(x_644, 9, x_640);
lean_ctor_set(x_644, 10, x_641);
lean_ctor_set(x_644, 11, x_642);
x_645 = lean_st_ref_set(x_3, x_644, x_625);
x_646 = lean_ctor_get(x_645, 1);
lean_inc(x_646);
lean_dec(x_645);
x_553 = x_621;
x_554 = x_646;
goto block_615;
}
}
else
{
uint8_t x_647; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_647 = !lean_is_exclusive(x_620);
if (x_647 == 0)
{
return x_620;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_620, 0);
x_649 = lean_ctor_get(x_620, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_620);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
else
{
lean_object* x_651; 
lean_dec(x_551);
x_651 = lean_ctor_get(x_619, 0);
lean_inc(x_651);
lean_dec(x_619);
x_553 = x_651;
x_554 = x_617;
goto block_615;
}
}
}
case 8:
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_781; lean_object* x_782; uint8_t x_818; 
x_665 = lean_ctor_get(x_1, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_1, 2);
lean_inc(x_666);
x_667 = lean_ctor_get(x_1, 3);
lean_inc(x_667);
x_818 = l_Lean_Expr_hasLevelParam(x_665);
if (x_818 == 0)
{
uint8_t x_819; 
x_819 = l_Lean_Expr_hasFVar(x_665);
if (x_819 == 0)
{
uint8_t x_820; 
x_820 = l_Lean_Expr_hasMVar(x_665);
if (x_820 == 0)
{
x_668 = x_665;
x_669 = x_8;
goto block_780;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_st_ref_get(x_3, x_8);
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec(x_821);
x_781 = x_822;
x_782 = x_823;
goto block_817;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_824 = lean_st_ref_get(x_3, x_8);
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
lean_dec(x_824);
x_781 = x_825;
x_782 = x_826;
goto block_817;
}
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_827 = lean_st_ref_get(x_3, x_8);
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
lean_dec(x_827);
x_781 = x_828;
x_782 = x_829;
goto block_817;
}
block_780:
{
lean_object* x_670; lean_object* x_671; lean_object* x_731; lean_object* x_732; uint8_t x_768; 
x_768 = l_Lean_Expr_hasLevelParam(x_666);
if (x_768 == 0)
{
uint8_t x_769; 
x_769 = l_Lean_Expr_hasFVar(x_666);
if (x_769 == 0)
{
uint8_t x_770; 
x_770 = l_Lean_Expr_hasMVar(x_666);
if (x_770 == 0)
{
x_670 = x_666;
x_671 = x_669;
goto block_730;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_st_ref_get(x_3, x_669);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_731 = x_772;
x_732 = x_773;
goto block_767;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_st_ref_get(x_3, x_669);
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
x_731 = x_775;
x_732 = x_776;
goto block_767;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_st_ref_get(x_3, x_669);
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_731 = x_778;
x_732 = x_779;
goto block_767;
}
block_730:
{
lean_object* x_672; lean_object* x_673; lean_object* x_681; lean_object* x_682; uint8_t x_718; 
x_718 = l_Lean_Expr_hasLevelParam(x_667);
if (x_718 == 0)
{
uint8_t x_719; 
x_719 = l_Lean_Expr_hasFVar(x_667);
if (x_719 == 0)
{
uint8_t x_720; 
x_720 = l_Lean_Expr_hasMVar(x_667);
if (x_720 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_672 = x_667;
x_673 = x_671;
goto block_680;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_st_ref_get(x_3, x_671);
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_681 = x_722;
x_682 = x_723;
goto block_717;
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_724 = lean_st_ref_get(x_3, x_671);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_681 = x_725;
x_682 = x_726;
goto block_717;
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_st_ref_get(x_3, x_671);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_681 = x_728;
x_682 = x_729;
goto block_717;
}
block_680:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_674; lean_object* x_675; 
x_674 = lean_expr_update_let(x_1, x_668, x_670, x_672);
x_675 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_673);
return x_675;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_672);
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_1);
x_676 = l_Lean_Expr_Inhabited;
x_677 = l_Lean_Expr_updateLet_x21___closed__1;
x_678 = lean_panic_fn(x_676, x_677);
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_678);
lean_ctor_set(x_679, 1, x_673);
return x_679;
}
}
block_717:
{
lean_object* x_683; lean_object* x_684; 
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_684 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_683, x_667);
lean_dec(x_683);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; 
lean_inc(x_667);
x_685 = l_Lean_Meta_Closure_collectExprAux___main(x_667, x_2, x_3, x_4, x_5, x_6, x_7, x_682);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
x_688 = lean_st_ref_take(x_3, x_687);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_691 = !lean_is_exclusive(x_689);
if (x_691 == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_692 = lean_ctor_get(x_689, 1);
lean_inc(x_686);
x_693 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_692, x_667, x_686);
lean_ctor_set(x_689, 1, x_693);
x_694 = lean_st_ref_set(x_3, x_689, x_690);
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
lean_dec(x_694);
x_672 = x_686;
x_673 = x_695;
goto block_680;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_696 = lean_ctor_get(x_689, 0);
x_697 = lean_ctor_get(x_689, 1);
x_698 = lean_ctor_get(x_689, 2);
x_699 = lean_ctor_get(x_689, 3);
x_700 = lean_ctor_get(x_689, 4);
x_701 = lean_ctor_get(x_689, 5);
x_702 = lean_ctor_get(x_689, 6);
x_703 = lean_ctor_get(x_689, 7);
x_704 = lean_ctor_get(x_689, 8);
x_705 = lean_ctor_get(x_689, 9);
x_706 = lean_ctor_get(x_689, 10);
x_707 = lean_ctor_get(x_689, 11);
lean_inc(x_707);
lean_inc(x_706);
lean_inc(x_705);
lean_inc(x_704);
lean_inc(x_703);
lean_inc(x_702);
lean_inc(x_701);
lean_inc(x_700);
lean_inc(x_699);
lean_inc(x_698);
lean_inc(x_697);
lean_inc(x_696);
lean_dec(x_689);
lean_inc(x_686);
x_708 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_697, x_667, x_686);
x_709 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_709, 0, x_696);
lean_ctor_set(x_709, 1, x_708);
lean_ctor_set(x_709, 2, x_698);
lean_ctor_set(x_709, 3, x_699);
lean_ctor_set(x_709, 4, x_700);
lean_ctor_set(x_709, 5, x_701);
lean_ctor_set(x_709, 6, x_702);
lean_ctor_set(x_709, 7, x_703);
lean_ctor_set(x_709, 8, x_704);
lean_ctor_set(x_709, 9, x_705);
lean_ctor_set(x_709, 10, x_706);
lean_ctor_set(x_709, 11, x_707);
x_710 = lean_st_ref_set(x_3, x_709, x_690);
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
lean_dec(x_710);
x_672 = x_686;
x_673 = x_711;
goto block_680;
}
}
else
{
uint8_t x_712; 
lean_dec(x_670);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_1);
x_712 = !lean_is_exclusive(x_685);
if (x_712 == 0)
{
return x_685;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_685, 0);
x_714 = lean_ctor_get(x_685, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_685);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
else
{
lean_object* x_716; 
lean_dec(x_667);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_716 = lean_ctor_get(x_684, 0);
lean_inc(x_716);
lean_dec(x_684);
x_672 = x_716;
x_673 = x_682;
goto block_680;
}
}
}
block_767:
{
lean_object* x_733; lean_object* x_734; 
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
x_734 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_733, x_666);
lean_dec(x_733);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_666);
x_735 = l_Lean_Meta_Closure_collectExprAux___main(x_666, x_2, x_3, x_4, x_5, x_6, x_7, x_732);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; uint8_t x_741; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
x_738 = lean_st_ref_take(x_3, x_737);
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
lean_dec(x_738);
x_741 = !lean_is_exclusive(x_739);
if (x_741 == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_742 = lean_ctor_get(x_739, 1);
lean_inc(x_736);
x_743 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_742, x_666, x_736);
lean_ctor_set(x_739, 1, x_743);
x_744 = lean_st_ref_set(x_3, x_739, x_740);
x_745 = lean_ctor_get(x_744, 1);
lean_inc(x_745);
lean_dec(x_744);
x_670 = x_736;
x_671 = x_745;
goto block_730;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_746 = lean_ctor_get(x_739, 0);
x_747 = lean_ctor_get(x_739, 1);
x_748 = lean_ctor_get(x_739, 2);
x_749 = lean_ctor_get(x_739, 3);
x_750 = lean_ctor_get(x_739, 4);
x_751 = lean_ctor_get(x_739, 5);
x_752 = lean_ctor_get(x_739, 6);
x_753 = lean_ctor_get(x_739, 7);
x_754 = lean_ctor_get(x_739, 8);
x_755 = lean_ctor_get(x_739, 9);
x_756 = lean_ctor_get(x_739, 10);
x_757 = lean_ctor_get(x_739, 11);
lean_inc(x_757);
lean_inc(x_756);
lean_inc(x_755);
lean_inc(x_754);
lean_inc(x_753);
lean_inc(x_752);
lean_inc(x_751);
lean_inc(x_750);
lean_inc(x_749);
lean_inc(x_748);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_739);
lean_inc(x_736);
x_758 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_747, x_666, x_736);
x_759 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_759, 0, x_746);
lean_ctor_set(x_759, 1, x_758);
lean_ctor_set(x_759, 2, x_748);
lean_ctor_set(x_759, 3, x_749);
lean_ctor_set(x_759, 4, x_750);
lean_ctor_set(x_759, 5, x_751);
lean_ctor_set(x_759, 6, x_752);
lean_ctor_set(x_759, 7, x_753);
lean_ctor_set(x_759, 8, x_754);
lean_ctor_set(x_759, 9, x_755);
lean_ctor_set(x_759, 10, x_756);
lean_ctor_set(x_759, 11, x_757);
x_760 = lean_st_ref_set(x_3, x_759, x_740);
x_761 = lean_ctor_get(x_760, 1);
lean_inc(x_761);
lean_dec(x_760);
x_670 = x_736;
x_671 = x_761;
goto block_730;
}
}
else
{
uint8_t x_762; 
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_762 = !lean_is_exclusive(x_735);
if (x_762 == 0)
{
return x_735;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_735, 0);
x_764 = lean_ctor_get(x_735, 1);
lean_inc(x_764);
lean_inc(x_763);
lean_dec(x_735);
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
return x_765;
}
}
}
else
{
lean_object* x_766; 
lean_dec(x_666);
x_766 = lean_ctor_get(x_734, 0);
lean_inc(x_766);
lean_dec(x_734);
x_670 = x_766;
x_671 = x_732;
goto block_730;
}
}
}
block_817:
{
lean_object* x_783; lean_object* x_784; 
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
lean_dec(x_781);
x_784 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_783, x_665);
lean_dec(x_783);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_665);
x_785 = l_Lean_Meta_Closure_collectExprAux___main(x_665, x_2, x_3, x_4, x_5, x_6, x_7, x_782);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_785, 1);
lean_inc(x_787);
lean_dec(x_785);
x_788 = lean_st_ref_take(x_3, x_787);
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec(x_788);
x_791 = !lean_is_exclusive(x_789);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_792 = lean_ctor_get(x_789, 1);
lean_inc(x_786);
x_793 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_792, x_665, x_786);
lean_ctor_set(x_789, 1, x_793);
x_794 = lean_st_ref_set(x_3, x_789, x_790);
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
lean_dec(x_794);
x_668 = x_786;
x_669 = x_795;
goto block_780;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_796 = lean_ctor_get(x_789, 0);
x_797 = lean_ctor_get(x_789, 1);
x_798 = lean_ctor_get(x_789, 2);
x_799 = lean_ctor_get(x_789, 3);
x_800 = lean_ctor_get(x_789, 4);
x_801 = lean_ctor_get(x_789, 5);
x_802 = lean_ctor_get(x_789, 6);
x_803 = lean_ctor_get(x_789, 7);
x_804 = lean_ctor_get(x_789, 8);
x_805 = lean_ctor_get(x_789, 9);
x_806 = lean_ctor_get(x_789, 10);
x_807 = lean_ctor_get(x_789, 11);
lean_inc(x_807);
lean_inc(x_806);
lean_inc(x_805);
lean_inc(x_804);
lean_inc(x_803);
lean_inc(x_802);
lean_inc(x_801);
lean_inc(x_800);
lean_inc(x_799);
lean_inc(x_798);
lean_inc(x_797);
lean_inc(x_796);
lean_dec(x_789);
lean_inc(x_786);
x_808 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_797, x_665, x_786);
x_809 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_809, 0, x_796);
lean_ctor_set(x_809, 1, x_808);
lean_ctor_set(x_809, 2, x_798);
lean_ctor_set(x_809, 3, x_799);
lean_ctor_set(x_809, 4, x_800);
lean_ctor_set(x_809, 5, x_801);
lean_ctor_set(x_809, 6, x_802);
lean_ctor_set(x_809, 7, x_803);
lean_ctor_set(x_809, 8, x_804);
lean_ctor_set(x_809, 9, x_805);
lean_ctor_set(x_809, 10, x_806);
lean_ctor_set(x_809, 11, x_807);
x_810 = lean_st_ref_set(x_3, x_809, x_790);
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
x_668 = x_786;
x_669 = x_811;
goto block_780;
}
}
else
{
uint8_t x_812; 
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_812 = !lean_is_exclusive(x_785);
if (x_812 == 0)
{
return x_785;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_785, 0);
x_814 = lean_ctor_get(x_785, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_785);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
return x_815;
}
}
}
else
{
lean_object* x_816; 
lean_dec(x_665);
x_816 = lean_ctor_get(x_784, 0);
lean_inc(x_816);
lean_dec(x_784);
x_668 = x_816;
x_669 = x_782;
goto block_780;
}
}
}
case 10:
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; uint8_t x_868; 
x_830 = lean_ctor_get(x_1, 1);
lean_inc(x_830);
x_868 = l_Lean_Expr_hasLevelParam(x_830);
if (x_868 == 0)
{
uint8_t x_869; 
x_869 = l_Lean_Expr_hasFVar(x_830);
if (x_869 == 0)
{
uint8_t x_870; 
x_870 = l_Lean_Expr_hasMVar(x_830);
if (x_870 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_830;
x_10 = x_8;
goto block_17;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_871 = lean_st_ref_get(x_3, x_8);
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
x_831 = x_872;
x_832 = x_873;
goto block_867;
}
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_874 = lean_st_ref_get(x_3, x_8);
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
lean_dec(x_874);
x_831 = x_875;
x_832 = x_876;
goto block_867;
}
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_st_ref_get(x_3, x_8);
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_831 = x_878;
x_832 = x_879;
goto block_867;
}
block_867:
{
lean_object* x_833; lean_object* x_834; 
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
lean_dec(x_831);
x_834 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_833, x_830);
lean_dec(x_833);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; 
lean_inc(x_830);
x_835 = l_Lean_Meta_Closure_collectExprAux___main(x_830, x_2, x_3, x_4, x_5, x_6, x_7, x_832);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; uint8_t x_841; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
lean_dec(x_835);
x_838 = lean_st_ref_take(x_3, x_837);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
lean_dec(x_838);
x_841 = !lean_is_exclusive(x_839);
if (x_841 == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_842 = lean_ctor_get(x_839, 1);
lean_inc(x_836);
x_843 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_842, x_830, x_836);
lean_ctor_set(x_839, 1, x_843);
x_844 = lean_st_ref_set(x_3, x_839, x_840);
x_845 = lean_ctor_get(x_844, 1);
lean_inc(x_845);
lean_dec(x_844);
x_9 = x_836;
x_10 = x_845;
goto block_17;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_846 = lean_ctor_get(x_839, 0);
x_847 = lean_ctor_get(x_839, 1);
x_848 = lean_ctor_get(x_839, 2);
x_849 = lean_ctor_get(x_839, 3);
x_850 = lean_ctor_get(x_839, 4);
x_851 = lean_ctor_get(x_839, 5);
x_852 = lean_ctor_get(x_839, 6);
x_853 = lean_ctor_get(x_839, 7);
x_854 = lean_ctor_get(x_839, 8);
x_855 = lean_ctor_get(x_839, 9);
x_856 = lean_ctor_get(x_839, 10);
x_857 = lean_ctor_get(x_839, 11);
lean_inc(x_857);
lean_inc(x_856);
lean_inc(x_855);
lean_inc(x_854);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_850);
lean_inc(x_849);
lean_inc(x_848);
lean_inc(x_847);
lean_inc(x_846);
lean_dec(x_839);
lean_inc(x_836);
x_858 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_847, x_830, x_836);
x_859 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_859, 0, x_846);
lean_ctor_set(x_859, 1, x_858);
lean_ctor_set(x_859, 2, x_848);
lean_ctor_set(x_859, 3, x_849);
lean_ctor_set(x_859, 4, x_850);
lean_ctor_set(x_859, 5, x_851);
lean_ctor_set(x_859, 6, x_852);
lean_ctor_set(x_859, 7, x_853);
lean_ctor_set(x_859, 8, x_854);
lean_ctor_set(x_859, 9, x_855);
lean_ctor_set(x_859, 10, x_856);
lean_ctor_set(x_859, 11, x_857);
x_860 = lean_st_ref_set(x_3, x_859, x_840);
x_861 = lean_ctor_get(x_860, 1);
lean_inc(x_861);
lean_dec(x_860);
x_9 = x_836;
x_10 = x_861;
goto block_17;
}
}
else
{
uint8_t x_862; 
lean_dec(x_830);
lean_dec(x_1);
x_862 = !lean_is_exclusive(x_835);
if (x_862 == 0)
{
return x_835;
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_863 = lean_ctor_get(x_835, 0);
x_864 = lean_ctor_get(x_835, 1);
lean_inc(x_864);
lean_inc(x_863);
lean_dec(x_835);
x_865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_865, 0, x_863);
lean_ctor_set(x_865, 1, x_864);
return x_865;
}
}
}
else
{
lean_object* x_866; 
lean_dec(x_830);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_866 = lean_ctor_get(x_834, 0);
lean_inc(x_866);
lean_dec(x_834);
x_9 = x_866;
x_10 = x_832;
goto block_17;
}
}
}
case 11:
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; uint8_t x_918; 
x_880 = lean_ctor_get(x_1, 2);
lean_inc(x_880);
x_918 = l_Lean_Expr_hasLevelParam(x_880);
if (x_918 == 0)
{
uint8_t x_919; 
x_919 = l_Lean_Expr_hasFVar(x_880);
if (x_919 == 0)
{
uint8_t x_920; 
x_920 = l_Lean_Expr_hasMVar(x_880);
if (x_920 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = x_880;
x_19 = x_8;
goto block_26;
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_921 = lean_st_ref_get(x_3, x_8);
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
lean_dec(x_921);
x_881 = x_922;
x_882 = x_923;
goto block_917;
}
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_924 = lean_st_ref_get(x_3, x_8);
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
lean_dec(x_924);
x_881 = x_925;
x_882 = x_926;
goto block_917;
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_927 = lean_st_ref_get(x_3, x_8);
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_881 = x_928;
x_882 = x_929;
goto block_917;
}
block_917:
{
lean_object* x_883; lean_object* x_884; 
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_884 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_883, x_880);
lean_dec(x_883);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; 
lean_inc(x_880);
x_885 = l_Lean_Meta_Closure_collectExprAux___main(x_880, x_2, x_3, x_4, x_5, x_6, x_7, x_882);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; uint8_t x_891; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
x_888 = lean_st_ref_take(x_3, x_887);
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
lean_dec(x_888);
x_891 = !lean_is_exclusive(x_889);
if (x_891 == 0)
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_892 = lean_ctor_get(x_889, 1);
lean_inc(x_886);
x_893 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_892, x_880, x_886);
lean_ctor_set(x_889, 1, x_893);
x_894 = lean_st_ref_set(x_3, x_889, x_890);
x_895 = lean_ctor_get(x_894, 1);
lean_inc(x_895);
lean_dec(x_894);
x_18 = x_886;
x_19 = x_895;
goto block_26;
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_896 = lean_ctor_get(x_889, 0);
x_897 = lean_ctor_get(x_889, 1);
x_898 = lean_ctor_get(x_889, 2);
x_899 = lean_ctor_get(x_889, 3);
x_900 = lean_ctor_get(x_889, 4);
x_901 = lean_ctor_get(x_889, 5);
x_902 = lean_ctor_get(x_889, 6);
x_903 = lean_ctor_get(x_889, 7);
x_904 = lean_ctor_get(x_889, 8);
x_905 = lean_ctor_get(x_889, 9);
x_906 = lean_ctor_get(x_889, 10);
x_907 = lean_ctor_get(x_889, 11);
lean_inc(x_907);
lean_inc(x_906);
lean_inc(x_905);
lean_inc(x_904);
lean_inc(x_903);
lean_inc(x_902);
lean_inc(x_901);
lean_inc(x_900);
lean_inc(x_899);
lean_inc(x_898);
lean_inc(x_897);
lean_inc(x_896);
lean_dec(x_889);
lean_inc(x_886);
x_908 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_897, x_880, x_886);
x_909 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_909, 0, x_896);
lean_ctor_set(x_909, 1, x_908);
lean_ctor_set(x_909, 2, x_898);
lean_ctor_set(x_909, 3, x_899);
lean_ctor_set(x_909, 4, x_900);
lean_ctor_set(x_909, 5, x_901);
lean_ctor_set(x_909, 6, x_902);
lean_ctor_set(x_909, 7, x_903);
lean_ctor_set(x_909, 8, x_904);
lean_ctor_set(x_909, 9, x_905);
lean_ctor_set(x_909, 10, x_906);
lean_ctor_set(x_909, 11, x_907);
x_910 = lean_st_ref_set(x_3, x_909, x_890);
x_911 = lean_ctor_get(x_910, 1);
lean_inc(x_911);
lean_dec(x_910);
x_18 = x_886;
x_19 = x_911;
goto block_26;
}
}
else
{
uint8_t x_912; 
lean_dec(x_880);
lean_dec(x_1);
x_912 = !lean_is_exclusive(x_885);
if (x_912 == 0)
{
return x_885;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = lean_ctor_get(x_885, 0);
x_914 = lean_ctor_get(x_885, 1);
lean_inc(x_914);
lean_inc(x_913);
lean_dec(x_885);
x_915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
return x_915;
}
}
}
else
{
lean_object* x_916; 
lean_dec(x_880);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_916 = lean_ctor_get(x_884, 0);
lean_inc(x_916);
lean_dec(x_884);
x_18 = x_916;
x_19 = x_882;
goto block_26;
}
}
}
default: 
{
lean_object* x_930; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_930 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_930, 0, x_1);
lean_ctor_set(x_930, 1, x_8);
return x_930;
}
}
block_17:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_update_mdata(x_1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = l_Lean_Expr_Inhabited;
x_14 = l_Lean_Expr_updateMData_x21___closed__2;
x_15 = lean_panic_fn(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
block_26:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_expr_update_proj(x_1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_1);
x_22 = l_Lean_Expr_Inhabited;
x_23 = l_Lean_Expr_updateProj_x21___closed__2;
x_24 = lean_panic_fn(x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectExprAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectExprAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_Closure_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_56; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_56 = l_Lean_Expr_hasLevelParam(x_10);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Expr_hasFVar(x_10);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Expr_hasMVar(x_10);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_10);
lean_ctor_set(x_59, 1, x_11);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_st_ref_get(x_3, x_11);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_13 = x_61;
x_14 = x_62;
goto block_55;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_st_ref_get(x_3, x_11);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_13 = x_64;
x_14 = x_65;
goto block_55;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_st_ref_get(x_3, x_11);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_13 = x_67;
x_14 = x_68;
goto block_55;
}
block_55:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_15, x_10);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_inc(x_10);
x_17 = l_Lean_Meta_Closure_collectExprAux___main(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_3, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_18);
x_25 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_24, x_10, x_18);
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_3, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_18);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 2);
x_34 = lean_ctor_get(x_21, 3);
x_35 = lean_ctor_get(x_21, 4);
x_36 = lean_ctor_get(x_21, 5);
x_37 = lean_ctor_get(x_21, 6);
x_38 = lean_ctor_get(x_21, 7);
x_39 = lean_ctor_get(x_21, 8);
x_40 = lean_ctor_get(x_21, 9);
x_41 = lean_ctor_get(x_21, 10);
x_42 = lean_ctor_get(x_21, 11);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
lean_inc(x_18);
x_43 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_32, x_10, x_18);
x_44 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_33);
lean_ctor_set(x_44, 3, x_34);
lean_ctor_set(x_44, 4, x_35);
lean_ctor_set(x_44, 5, x_36);
lean_ctor_set(x_44, 6, x_37);
lean_ctor_set(x_44, 7, x_38);
lean_ctor_set(x_44, 8, x_39);
lean_ctor_set(x_44, 9, x_40);
lean_ctor_set(x_44, 10, x_41);
lean_ctor_set(x_44, 11, x_42);
x_45 = lean_st_ref_set(x_3, x_44, x_22);
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
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_10);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_dec(x_16);
if (lean_is_scalar(x_12)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_12;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_14);
return x_54;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_9);
if (x_69 == 0)
{
return x_9;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_9, 0);
x_71 = lean_ctor_get(x_9, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_9);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_LocalContext_get_x21(x_1, x_9);
x_11 = l_Lean_LocalDecl_index(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_inc(x_1);
x_13 = l_Lean_LocalContext_get_x21(x_1, x_12);
x_14 = l_Lean_LocalDecl_index(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_lt(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = lean_array_fset(x_3, x_2, x_4);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_21;
x_4 = x_8;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Closure_pickNextToProcessAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Meta_Closure_ToProcessElement_inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_st_ref_get(x_1, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 11);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_isEmpty___rarg(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_8);
x_14 = lean_st_ref_take(x_1, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_15, 11);
x_19 = l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(x_18);
x_20 = lean_array_pop(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Meta_Closure_pickNextToProcessAux___main(x_7, x_21, x_20, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_15, 11, x_24);
x_26 = lean_st_ref_set(x_1, x_15, x_16);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
x_33 = lean_ctor_get(x_15, 2);
x_34 = lean_ctor_get(x_15, 3);
x_35 = lean_ctor_get(x_15, 4);
x_36 = lean_ctor_get(x_15, 5);
x_37 = lean_ctor_get(x_15, 6);
x_38 = lean_ctor_get(x_15, 7);
x_39 = lean_ctor_get(x_15, 8);
x_40 = lean_ctor_get(x_15, 9);
x_41 = lean_ctor_get(x_15, 10);
x_42 = lean_ctor_get(x_15, 11);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_43 = l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(x_42);
x_44 = lean_array_pop(x_42);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Meta_Closure_pickNextToProcessAux___main(x_7, x_45, x_44, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_50, 0, x_31);
lean_ctor_set(x_50, 1, x_32);
lean_ctor_set(x_50, 2, x_33);
lean_ctor_set(x_50, 3, x_34);
lean_ctor_set(x_50, 4, x_35);
lean_ctor_set(x_50, 5, x_36);
lean_ctor_set(x_50, 6, x_37);
lean_ctor_set(x_50, 7, x_38);
lean_ctor_set(x_50, 8, x_39);
lean_ctor_set(x_50, 9, x_40);
lean_ctor_set(x_50, 10, x_41);
lean_ctor_set(x_50, 11, x_48);
x_51 = lean_st_ref_set(x_1, x_50, x_16);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_7);
x_55 = lean_box(0);
lean_ctor_set(x_8, 0, x_55);
return x_8;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_8, 0);
x_57 = lean_ctor_get(x_8, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_8);
x_58 = lean_ctor_get(x_56, 11);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Array_isEmpty___rarg(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_60 = lean_st_ref_take(x_1, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 6);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 7);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 8);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 9);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 10);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 11);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 lean_ctor_release(x_61, 6);
 lean_ctor_release(x_61, 7);
 lean_ctor_release(x_61, 8);
 lean_ctor_release(x_61, 9);
 lean_ctor_release(x_61, 10);
 lean_ctor_release(x_61, 11);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
 x_75 = lean_box(0);
}
x_76 = l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(x_74);
x_77 = lean_array_pop(x_74);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Meta_Closure_pickNextToProcessAux___main(x_7, x_78, x_77, x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_80);
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 12, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_63);
lean_ctor_set(x_83, 1, x_64);
lean_ctor_set(x_83, 2, x_65);
lean_ctor_set(x_83, 3, x_66);
lean_ctor_set(x_83, 4, x_67);
lean_ctor_set(x_83, 5, x_68);
lean_ctor_set(x_83, 6, x_69);
lean_ctor_set(x_83, 7, x_70);
lean_ctor_set(x_83, 8, x_71);
lean_ctor_set(x_83, 9, x_72);
lean_ctor_set(x_83, 10, x_73);
lean_ctor_set(x_83, 11, x_81);
x_84 = lean_st_ref_set(x_1, x_83, x_62);
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
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_7);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_57);
return x_89;
}
}
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Closure_pickNextToProcess_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 10);
x_14 = lean_array_push(x_13, x_1);
lean_ctor_set(x_10, 10, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get(x_10, 6);
x_29 = lean_ctor_get(x_10, 7);
x_30 = lean_ctor_get(x_10, 8);
x_31 = lean_ctor_get(x_10, 9);
x_32 = lean_ctor_get(x_10, 10);
x_33 = lean_ctor_get(x_10, 11);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_34 = lean_array_push(x_32, x_1);
x_35 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
lean_ctor_set(x_35, 5, x_27);
lean_ctor_set(x_35, 6, x_28);
lean_ctor_set(x_35, 7, x_29);
lean_ctor_set(x_35, 8, x_30);
lean_ctor_set(x_35, 9, x_31);
lean_ctor_set(x_35, 10, x_34);
lean_ctor_set(x_35, 11, x_33);
x_36 = lean_st_ref_set(x_3, x_35, x_11);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_pushFVarArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Closure_collectExpr(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_16, 5);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_4);
x_22 = lean_array_push(x_19, x_21);
lean_ctor_set(x_16, 5, x_22);
x_23 = lean_st_ref_set(x_6, x_16, x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_33 = lean_ctor_get(x_16, 3);
x_34 = lean_ctor_get(x_16, 4);
x_35 = lean_ctor_get(x_16, 5);
x_36 = lean_ctor_get(x_16, 6);
x_37 = lean_ctor_get(x_16, 7);
x_38 = lean_ctor_get(x_16, 8);
x_39 = lean_ctor_get(x_16, 9);
x_40 = lean_ctor_get(x_16, 10);
x_41 = lean_ctor_get(x_16, 11);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_2);
lean_ctor_set(x_43, 3, x_13);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_4);
x_44 = lean_array_push(x_35, x_43);
x_45 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_31);
lean_ctor_set(x_45, 2, x_32);
lean_ctor_set(x_45, 3, x_33);
lean_ctor_set(x_45, 4, x_34);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_45, 6, x_36);
lean_ctor_set(x_45, 7, x_37);
lean_ctor_set(x_45, 8, x_38);
lean_ctor_set(x_45, 9, x_39);
lean_ctor_set(x_45, 10, x_40);
lean_ctor_set(x_45, 11, x_41);
x_46 = lean_st_ref_set(x_6, x_45, x_17);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_12, 0);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_Closure_pushLocalDecl(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
lean_inc(x_1);
x_12 = l_Lean_replaceFVarIdAtLocalDecl(x_1, x_2, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_10, x_3, x_15);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Meta_Closure_process___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_8 = l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_18);
x_20 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___main___spec__1(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 3);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_23, x_24, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_mkFVar(x_18);
x_29 = l_Lean_Meta_Closure_pushFVarArg(x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_7 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_38 = lean_ctor_get(x_21, 2);
x_39 = lean_ctor_get(x_21, 3);
x_40 = lean_ctor_get(x_21, 4);
x_41 = lean_ctor_get(x_21, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_21, 0);
lean_dec(x_42);
x_43 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg(x_4, x_5, x_6, x_36);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_NameSet_contains(x_44, x_18);
lean_dec(x_44);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; 
lean_free_object(x_21);
lean_dec(x_40);
x_47 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_38, x_39, x_47, x_1, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_mkFVar(x_18);
x_51 = l_Lean_Meta_Closure_pushFVarArg(x_50, x_1, x_2, x_3, x_4, x_5, x_6, x_49);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_7 = x_52;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = l_Lean_Meta_Closure_collectExpr(x_39, x_1, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_61 = l_Lean_Meta_Closure_collectExpr(x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_take(x_2, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_68 = lean_ctor_get(x_65, 7);
x_69 = lean_unsigned_to_nat(0u);
x_70 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_69);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_70);
x_71 = lean_array_push(x_68, x_21);
lean_ctor_set(x_65, 7, x_71);
x_72 = lean_st_ref_set(x_2, x_65, x_66);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_take(x_2, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_75, 5);
x_79 = x_78;
x_80 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2(x_19, x_62, x_69, x_79);
lean_dec(x_62);
x_81 = x_80;
lean_ctor_set(x_75, 5, x_81);
x_82 = lean_st_ref_set(x_2, x_75, x_76);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_7 = x_83;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_85 = lean_ctor_get(x_75, 0);
x_86 = lean_ctor_get(x_75, 1);
x_87 = lean_ctor_get(x_75, 2);
x_88 = lean_ctor_get(x_75, 3);
x_89 = lean_ctor_get(x_75, 4);
x_90 = lean_ctor_get(x_75, 5);
x_91 = lean_ctor_get(x_75, 6);
x_92 = lean_ctor_get(x_75, 7);
x_93 = lean_ctor_get(x_75, 8);
x_94 = lean_ctor_get(x_75, 9);
x_95 = lean_ctor_get(x_75, 10);
x_96 = lean_ctor_get(x_75, 11);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_75);
x_97 = x_90;
x_98 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2(x_19, x_62, x_69, x_97);
lean_dec(x_62);
x_99 = x_98;
x_100 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_100, 0, x_85);
lean_ctor_set(x_100, 1, x_86);
lean_ctor_set(x_100, 2, x_87);
lean_ctor_set(x_100, 3, x_88);
lean_ctor_set(x_100, 4, x_89);
lean_ctor_set(x_100, 5, x_99);
lean_ctor_set(x_100, 6, x_91);
lean_ctor_set(x_100, 7, x_92);
lean_ctor_set(x_100, 8, x_93);
lean_ctor_set(x_100, 9, x_94);
lean_ctor_set(x_100, 10, x_95);
lean_ctor_set(x_100, 11, x_96);
x_101 = lean_st_ref_set(x_2, x_100, x_76);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_7 = x_102;
goto _start;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_104 = lean_ctor_get(x_65, 0);
x_105 = lean_ctor_get(x_65, 1);
x_106 = lean_ctor_get(x_65, 2);
x_107 = lean_ctor_get(x_65, 3);
x_108 = lean_ctor_get(x_65, 4);
x_109 = lean_ctor_get(x_65, 5);
x_110 = lean_ctor_get(x_65, 6);
x_111 = lean_ctor_get(x_65, 7);
x_112 = lean_ctor_get(x_65, 8);
x_113 = lean_ctor_get(x_65, 9);
x_114 = lean_ctor_get(x_65, 10);
x_115 = lean_ctor_get(x_65, 11);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_65);
x_116 = lean_unsigned_to_nat(0u);
x_117 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_116);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_117);
x_118 = lean_array_push(x_111, x_21);
x_119 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_119, 0, x_104);
lean_ctor_set(x_119, 1, x_105);
lean_ctor_set(x_119, 2, x_106);
lean_ctor_set(x_119, 3, x_107);
lean_ctor_set(x_119, 4, x_108);
lean_ctor_set(x_119, 5, x_109);
lean_ctor_set(x_119, 6, x_110);
lean_ctor_set(x_119, 7, x_118);
lean_ctor_set(x_119, 8, x_112);
lean_ctor_set(x_119, 9, x_113);
lean_ctor_set(x_119, 10, x_114);
lean_ctor_set(x_119, 11, x_115);
x_120 = lean_st_ref_set(x_2, x_119, x_66);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_st_ref_take(x_2, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 5);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 6);
lean_inc(x_131);
x_132 = lean_ctor_get(x_123, 7);
lean_inc(x_132);
x_133 = lean_ctor_get(x_123, 8);
lean_inc(x_133);
x_134 = lean_ctor_get(x_123, 9);
lean_inc(x_134);
x_135 = lean_ctor_get(x_123, 10);
lean_inc(x_135);
x_136 = lean_ctor_get(x_123, 11);
lean_inc(x_136);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 lean_ctor_release(x_123, 6);
 lean_ctor_release(x_123, 7);
 lean_ctor_release(x_123, 8);
 lean_ctor_release(x_123, 9);
 lean_ctor_release(x_123, 10);
 lean_ctor_release(x_123, 11);
 x_137 = x_123;
} else {
 lean_dec_ref(x_123);
 x_137 = lean_box(0);
}
x_138 = x_130;
x_139 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2(x_19, x_62, x_116, x_138);
lean_dec(x_62);
x_140 = x_139;
if (lean_is_scalar(x_137)) {
 x_141 = lean_alloc_ctor(0, 12, 0);
} else {
 x_141 = x_137;
}
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_126);
lean_ctor_set(x_141, 2, x_127);
lean_ctor_set(x_141, 3, x_128);
lean_ctor_set(x_141, 4, x_129);
lean_ctor_set(x_141, 5, x_140);
lean_ctor_set(x_141, 6, x_131);
lean_ctor_set(x_141, 7, x_132);
lean_ctor_set(x_141, 8, x_133);
lean_ctor_set(x_141, 9, x_134);
lean_ctor_set(x_141, 10, x_135);
lean_ctor_set(x_141, 11, x_136);
x_142 = lean_st_ref_set(x_2, x_141, x_124);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_7 = x_143;
goto _start;
}
}
else
{
uint8_t x_145; 
lean_dec(x_59);
lean_free_object(x_21);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_145 = !lean_is_exclusive(x_61);
if (x_145 == 0)
{
return x_61;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_61, 0);
x_147 = lean_ctor_get(x_61, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_61);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_free_object(x_21);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_58);
if (x_149 == 0)
{
return x_58;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_58, 0);
x_151 = lean_ctor_get(x_58, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_58);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_153 = lean_ctor_get(x_21, 2);
x_154 = lean_ctor_get(x_21, 3);
x_155 = lean_ctor_get(x_21, 4);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_21);
x_156 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg(x_4, x_5, x_6, x_36);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_NameSet_contains(x_157, x_18);
lean_dec(x_157);
if (x_159 == 0)
{
uint8_t x_160; lean_object* x_161; 
lean_dec(x_155);
x_160 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_161 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_153, x_154, x_160, x_1, x_2, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_mkFVar(x_18);
x_164 = l_Lean_Meta_Closure_pushFVarArg(x_163, x_1, x_2, x_3, x_4, x_5, x_6, x_162);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_7 = x_165;
goto _start;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_169 = x_161;
} else {
 lean_dec_ref(x_161);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_171 = l_Lean_Meta_Closure_collectExpr(x_154, x_1, x_2, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_174 = l_Lean_Meta_Closure_collectExpr(x_155, x_1, x_2, x_3, x_4, x_5, x_6, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_st_ref_take(x_2, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_178, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 5);
lean_inc(x_185);
x_186 = lean_ctor_get(x_178, 6);
lean_inc(x_186);
x_187 = lean_ctor_get(x_178, 7);
lean_inc(x_187);
x_188 = lean_ctor_get(x_178, 8);
lean_inc(x_188);
x_189 = lean_ctor_get(x_178, 9);
lean_inc(x_189);
x_190 = lean_ctor_get(x_178, 10);
lean_inc(x_190);
x_191 = lean_ctor_get(x_178, 11);
lean_inc(x_191);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 lean_ctor_release(x_178, 6);
 lean_ctor_release(x_178, 7);
 lean_ctor_release(x_178, 8);
 lean_ctor_release(x_178, 9);
 lean_ctor_release(x_178, 10);
 lean_ctor_release(x_178, 11);
 x_192 = x_178;
} else {
 lean_dec_ref(x_178);
 x_192 = lean_box(0);
}
x_193 = lean_unsigned_to_nat(0u);
x_194 = 0;
lean_inc(x_175);
lean_inc(x_19);
x_195 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_19);
lean_ctor_set(x_195, 2, x_153);
lean_ctor_set(x_195, 3, x_172);
lean_ctor_set(x_195, 4, x_175);
lean_ctor_set_uint8(x_195, sizeof(void*)*5, x_194);
x_196 = lean_array_push(x_187, x_195);
if (lean_is_scalar(x_192)) {
 x_197 = lean_alloc_ctor(0, 12, 0);
} else {
 x_197 = x_192;
}
lean_ctor_set(x_197, 0, x_180);
lean_ctor_set(x_197, 1, x_181);
lean_ctor_set(x_197, 2, x_182);
lean_ctor_set(x_197, 3, x_183);
lean_ctor_set(x_197, 4, x_184);
lean_ctor_set(x_197, 5, x_185);
lean_ctor_set(x_197, 6, x_186);
lean_ctor_set(x_197, 7, x_196);
lean_ctor_set(x_197, 8, x_188);
lean_ctor_set(x_197, 9, x_189);
lean_ctor_set(x_197, 10, x_190);
lean_ctor_set(x_197, 11, x_191);
x_198 = lean_st_ref_set(x_2, x_197, x_179);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_st_ref_take(x_2, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 5);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 6);
lean_inc(x_209);
x_210 = lean_ctor_get(x_201, 7);
lean_inc(x_210);
x_211 = lean_ctor_get(x_201, 8);
lean_inc(x_211);
x_212 = lean_ctor_get(x_201, 9);
lean_inc(x_212);
x_213 = lean_ctor_get(x_201, 10);
lean_inc(x_213);
x_214 = lean_ctor_get(x_201, 11);
lean_inc(x_214);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 lean_ctor_release(x_201, 4);
 lean_ctor_release(x_201, 5);
 lean_ctor_release(x_201, 6);
 lean_ctor_release(x_201, 7);
 lean_ctor_release(x_201, 8);
 lean_ctor_release(x_201, 9);
 lean_ctor_release(x_201, 10);
 lean_ctor_release(x_201, 11);
 x_215 = x_201;
} else {
 lean_dec_ref(x_201);
 x_215 = lean_box(0);
}
x_216 = x_208;
x_217 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2(x_19, x_175, x_193, x_216);
lean_dec(x_175);
x_218 = x_217;
if (lean_is_scalar(x_215)) {
 x_219 = lean_alloc_ctor(0, 12, 0);
} else {
 x_219 = x_215;
}
lean_ctor_set(x_219, 0, x_203);
lean_ctor_set(x_219, 1, x_204);
lean_ctor_set(x_219, 2, x_205);
lean_ctor_set(x_219, 3, x_206);
lean_ctor_set(x_219, 4, x_207);
lean_ctor_set(x_219, 5, x_218);
lean_ctor_set(x_219, 6, x_209);
lean_ctor_set(x_219, 7, x_210);
lean_ctor_set(x_219, 8, x_211);
lean_ctor_set(x_219, 9, x_212);
lean_ctor_set(x_219, 10, x_213);
lean_ctor_set(x_219, 11, x_214);
x_220 = lean_st_ref_set(x_2, x_219, x_202);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_7 = x_221;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_172);
lean_dec(x_153);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_223 = lean_ctor_get(x_174, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_174, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_225 = x_174;
} else {
 lean_dec_ref(x_174);
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
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_227 = lean_ctor_get(x_171, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_171, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_229 = x_171;
} else {
 lean_dec_ref(x_171);
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
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_231 = !lean_is_exclusive(x_20);
if (x_231 == 0)
{
return x_20;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_20, 0);
x_233 = lean_ctor_get(x_20, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_20);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
}
lean_object* l_Lean_Meta_Closure_process___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_process___main___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___main___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_Closure_process___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_process___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_Closure_process___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Closure_process___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_process___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_process___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_Closure_process(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_process___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_process___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_process___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Closure_process(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_LocalDecl_toExpr(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = l_Lean_LocalDecl_Inhabited;
x_11 = lean_array_get(x_10, x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*4);
lean_dec(x_11);
x_15 = lean_expr_abstract_range(x_13, x_9, x_3);
lean_dec(x_13);
if (x_1 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_mkForall(x_12, x_14, x_15, x_5);
x_4 = x_9;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_mkLambda(x_12, x_14, x_15, x_5);
x_4 = x_9;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_11, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 4);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
lean_dec(x_11);
x_24 = lean_expr_has_loose_bvar(x_5, x_6);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_25 = lean_expr_lower_loose_bvars(x_5, x_8, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_expr_abstract_range(x_21, x_9, x_3);
lean_dec(x_21);
x_28 = lean_expr_abstract_range(x_22, x_9, x_3);
lean_dec(x_22);
x_29 = l_Lean_mkLet(x_20, x_27, x_28, x_5, x_23);
x_4 = x_9;
x_5 = x_29;
goto _start;
}
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_4 = x_2;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(x_5, x_4);
x_7 = x_6;
x_8 = lean_expr_abstract(x_3, x_7);
x_9 = lean_array_get_size(x_2);
x_10 = l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2(x_1, x_2, x_7, x_9, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_Closure_mkBinding(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_LocalDecl_Inhabited;
x_10 = lean_array_get(x_9, x_1, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
lean_dec(x_10);
x_14 = lean_expr_abstract_range(x_12, x_8, x_2);
lean_dec(x_12);
x_15 = l_Lean_mkLambda(x_11, x_13, x_14, x_4);
x_3 = x_8;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
lean_dec(x_10);
x_21 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_expr_abstract_range(x_18, x_8, x_2);
lean_dec(x_18);
x_25 = lean_expr_abstract_range(x_19, x_8, x_2);
lean_dec(x_19);
x_26 = l_Lean_mkLet(x_17, x_24, x_25, x_4, x_20);
x_3 = x_8;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_3 = x_1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_3);
x_6 = x_5;
x_7 = lean_expr_abstract(x_2, x_6);
x_8 = lean_array_get_size(x_1);
x_9 = l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_6, x_8, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkLambda(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_LocalDecl_Inhabited;
x_10 = lean_array_get(x_9, x_1, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
lean_dec(x_10);
x_14 = lean_expr_abstract_range(x_12, x_8, x_2);
lean_dec(x_12);
x_15 = l_Lean_mkForall(x_11, x_13, x_14, x_4);
x_3 = x_8;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
lean_dec(x_10);
x_21 = lean_expr_has_loose_bvar(x_4, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_expr_lower_loose_bvars(x_4, x_7, x_7);
lean_dec(x_4);
x_3 = x_8;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_expr_abstract_range(x_18, x_8, x_2);
lean_dec(x_18);
x_25 = lean_expr_abstract_range(x_19, x_8, x_2);
lean_dec(x_19);
x_26 = l_Lean_mkLet(x_17, x_24, x_25, x_4, x_20);
x_3 = x_8;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l_Lean_Meta_Closure_mkForall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_3 = x_1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_3);
x_6 = x_5;
x_7 = lean_expr_abstract(x_2, x_6);
x_8 = lean_array_get_size(x_1);
x_9 = l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_6, x_8, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkForall(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
x_10 = l_Lean_NameSet_empty;
lean_ctor_set(x_6, 2, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = l_Lean_NameSet_empty;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_ref_set(x_1, x_21, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
lean_ctor_set_uint8(x_11, 7, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Closure_process___main___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_18);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get_uint8(x_11, 0);
x_43 = lean_ctor_get_uint8(x_11, 1);
x_44 = lean_ctor_get_uint8(x_11, 2);
x_45 = lean_ctor_get_uint8(x_11, 3);
x_46 = lean_ctor_get_uint8(x_11, 4);
x_47 = lean_ctor_get_uint8(x_11, 5);
x_48 = lean_ctor_get_uint8(x_11, 6);
lean_dec(x_11);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_50, 0, x_42);
lean_ctor_set_uint8(x_50, 1, x_43);
lean_ctor_set_uint8(x_50, 2, x_44);
lean_ctor_set_uint8(x_50, 3, x_45);
lean_ctor_set_uint8(x_50, 4, x_46);
lean_ctor_set_uint8(x_50, 5, x_47);
lean_ctor_set_uint8(x_50, 6, x_48);
lean_ctor_set_uint8(x_50, 7, x_49);
lean_ctor_set(x_5, 0, x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_51 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_54 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_Closure_process___main___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_55);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_55);
lean_dec(x_52);
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_52);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_66 = lean_ctor_get(x_54, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_68 = x_54;
} else {
 lean_dec_ref(x_54);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_72 = x_51;
} else {
 lean_dec_ref(x_51);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_5, 1);
x_75 = lean_ctor_get(x_5, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_5);
x_76 = lean_ctor_get_uint8(x_11, 0);
x_77 = lean_ctor_get_uint8(x_11, 1);
x_78 = lean_ctor_get_uint8(x_11, 2);
x_79 = lean_ctor_get_uint8(x_11, 3);
x_80 = lean_ctor_get_uint8(x_11, 4);
x_81 = lean_ctor_get_uint8(x_11, 5);
x_82 = lean_ctor_get_uint8(x_11, 6);
if (lean_is_exclusive(x_11)) {
 x_83 = x_11;
} else {
 lean_dec_ref(x_11);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 0, 8);
} else {
 x_85 = x_83;
}
lean_ctor_set_uint8(x_85, 0, x_76);
lean_ctor_set_uint8(x_85, 1, x_77);
lean_ctor_set_uint8(x_85, 2, x_78);
lean_ctor_set_uint8(x_85, 3, x_79);
lean_ctor_set_uint8(x_85, 4, x_80);
lean_ctor_set_uint8(x_85, 5, x_81);
lean_ctor_set_uint8(x_85, 6, x_82);
lean_ctor_set_uint8(x_85, 7, x_84);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_74);
lean_ctor_set(x_86, 2, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_86);
x_87 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_86, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_86);
x_90 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_86, x_6, x_7, x_8, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Meta_Closure_process___main___rarg(x_3, x_4, x_86, x_6, x_7, x_8, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
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
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_91);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_91);
lean_dec(x_88);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
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
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_104 = x_90;
} else {
 lean_dec_ref(x_90);
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
lean_dec(x_86);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_87, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_108 = x_87;
} else {
 lean_dec_ref(x_87);
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
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_mkValueTypeClosure___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_mkValueTypeClosure___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
x_2 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_3);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_4);
lean_ctor_set(x_5, 9, x_3);
lean_ctor_set(x_5, 10, x_3);
lean_ctor_set(x_5, 11, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__3;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(x_3);
x_14 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_13, x_11, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_19, 5);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_reverseAux___main___rarg(x_22, x_23);
x_25 = lean_ctor_get(x_19, 6);
lean_inc(x_25);
x_26 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_25, x_25, x_23, x_24);
lean_dec(x_25);
x_27 = lean_ctor_get(x_19, 7);
lean_inc(x_27);
x_28 = l_Array_reverseAux___main___rarg(x_27, x_23);
lean_inc(x_28);
x_29 = l_Lean_Meta_Closure_mkForall(x_28, x_20);
lean_dec(x_20);
lean_inc(x_26);
x_30 = l_Lean_Meta_Closure_mkForall(x_26, x_29);
lean_dec(x_29);
x_31 = l_Lean_Meta_Closure_mkLambda(x_28, x_21);
lean_dec(x_21);
x_32 = l_Lean_Meta_Closure_mkLambda(x_26, x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_19, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_19, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 10);
lean_inc(x_35);
x_36 = l_Array_reverseAux___main___rarg(x_35, x_23);
x_37 = lean_ctor_get(x_19, 9);
lean_inc(x_37);
lean_dec(x_19);
x_38 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_37, x_37, x_23, x_36);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_17, 0, x_39);
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_dec(x_15);
x_44 = lean_ctor_get(x_40, 5);
lean_inc(x_44);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_reverseAux___main___rarg(x_44, x_45);
x_47 = lean_ctor_get(x_40, 6);
lean_inc(x_47);
x_48 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_47, x_47, x_45, x_46);
lean_dec(x_47);
x_49 = lean_ctor_get(x_40, 7);
lean_inc(x_49);
x_50 = l_Array_reverseAux___main___rarg(x_49, x_45);
lean_inc(x_50);
x_51 = l_Lean_Meta_Closure_mkForall(x_50, x_42);
lean_dec(x_42);
lean_inc(x_48);
x_52 = l_Lean_Meta_Closure_mkForall(x_48, x_51);
lean_dec(x_51);
x_53 = l_Lean_Meta_Closure_mkLambda(x_50, x_43);
lean_dec(x_43);
x_54 = l_Lean_Meta_Closure_mkLambda(x_48, x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_40, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_40, 4);
lean_inc(x_56);
x_57 = lean_ctor_get(x_40, 10);
lean_inc(x_57);
x_58 = l_Array_reverseAux___main___rarg(x_57, x_45);
x_59 = lean_ctor_get(x_40, 9);
lean_inc(x_59);
lean_dec(x_40);
x_60 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_59, x_59, x_45, x_58);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_52);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_56);
lean_ctor_set(x_61, 4, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_41);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_11);
x_63 = !lean_is_exclusive(x_14);
if (x_63 == 0)
{
return x_14;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_14, 0);
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_14);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Lean_KernelException_toMessageData(x_1, x_7);
x_9 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_add_decl(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__3(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_15;
}
}
}
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_compile_decl(x_10, x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__3(x_13, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_15, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_16;
}
}
}
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_addDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_compileDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__4(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatEntry___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__1;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint32_t x_24; uint32_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_19);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_ctor_get(x_11, 2);
lean_inc(x_21);
lean_inc(x_21);
lean_inc(x_16);
x_22 = l_Lean_getMaxHeight(x_16, x_21);
x_23 = lean_unbox_uint32(x_22);
lean_dec(x_22);
x_24 = 1;
x_25 = x_23 + x_24;
x_26 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_26, 0, x_25);
lean_inc(x_19);
lean_inc(x_16);
x_27 = l_Lean_Environment_hasUnsafe(x_16, x_19);
lean_inc(x_21);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___boxed), 4, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_19);
lean_closure_set(x_28, 2, x_21);
x_29 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4;
x_30 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_29, x_28, x_5, x_6, x_7, x_8, x_15);
if (x_27 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_21);
x_32 = l_Lean_Environment_hasUnsafe(x_16, x_21);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_addAndCompile___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__1(x_34, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_11, 3);
lean_inc(x_38);
x_39 = l_Array_toList___rarg(x_38);
lean_dec(x_38);
x_40 = l_Lean_mkConst(x_1, x_39);
x_41 = lean_ctor_get(x_11, 4);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_41, x_41, x_42, x_40);
lean_dec(x_41);
lean_ctor_set(x_35, 0, x_43);
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_ctor_get(x_11, 3);
lean_inc(x_45);
x_46 = l_Array_toList___rarg(x_45);
lean_dec(x_45);
x_47 = l_Lean_mkConst(x_1, x_46);
x_48 = lean_ctor_get(x_11, 4);
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_48, x_48, x_49, x_47);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
return x_35;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_35, 0);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_35);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_16);
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = 1;
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_20);
lean_ctor_set(x_58, 1, x_21);
lean_ctor_set(x_58, 2, x_26);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_addAndCompile___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__1(x_59, x_5, x_6, x_7, x_8, x_56);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_11, 3);
lean_inc(x_63);
x_64 = l_Array_toList___rarg(x_63);
lean_dec(x_63);
x_65 = l_Lean_mkConst(x_1, x_64);
x_66 = lean_ctor_get(x_11, 4);
lean_inc(x_66);
lean_dec(x_11);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_66, x_66, x_67, x_65);
lean_dec(x_66);
lean_ctor_set(x_60, 0, x_68);
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_dec(x_60);
x_70 = lean_ctor_get(x_11, 3);
lean_inc(x_70);
x_71 = l_Array_toList___rarg(x_70);
lean_dec(x_70);
x_72 = l_Lean_mkConst(x_1, x_71);
x_73 = lean_ctor_get(x_11, 4);
lean_inc(x_73);
lean_dec(x_11);
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_73, x_73, x_74, x_72);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_11);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
return x_60;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_60, 0);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_60);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_10);
if (x_81 == 0)
{
return x_10;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_10, 0);
x_83 = lean_ctor_get(x_10, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_10);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_compileDecl___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addAndCompile___at___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_4);
x_7 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4;
x_8 = lean_alloc_closure((void*)(l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_box(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed), 10, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinition___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Meta_mkAuxDefinition___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
x_11 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__4;
x_12 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_11, x_10, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_headBeta(x_3);
x_10 = 0;
x_11 = l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_9, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinitionFor___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_ShareCommon(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Closure(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_ShareCommon(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Closure_ToProcessElement_inhabited___closed__1 = _init_l_Lean_Meta_Closure_ToProcessElement_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_ToProcessElement_inhabited___closed__1);
l_Lean_Meta_Closure_ToProcessElement_inhabited = _init_l_Lean_Meta_Closure_ToProcessElement_inhabited();
lean_mark_persistent(l_Lean_Meta_Closure_ToProcessElement_inhabited);
l_Lean_Meta_Closure_mkNewLevelParam___closed__1 = _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___closed__1);
l_Lean_Meta_Closure_mkNewLevelParam___closed__2 = _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___closed__2);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__1 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__2 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__3 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__1 = _init_l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__1);
l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2 = _init_l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
