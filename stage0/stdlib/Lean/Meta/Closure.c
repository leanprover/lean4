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
lean_object* l_Lean_Meta_Closure_visitLevel_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLocalDecls___default;
lean_object* l_Lean_Meta_Closure_visitExpr_match__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel_match__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
extern lean_object* l_Lean_Level_Inhabited;
lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_ToProcessElement_inhabited___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*);
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_toResult___main___closed__3;
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*);
extern lean_object* l_Lean_Level_updateMax_x21___closed__2;
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedExpr___default___spec__1(lean_object*);
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5;
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___closed__2;
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___closed__1;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_visitedLevel___default;
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkBinding_match__1(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalDecl_Inhabited;
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitExpr___spec__7(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitExpr___spec__5(lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_ToProcessElement_inhabited;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
lean_object* l_Lean_Meta_Closure_State_exprMVarArgs___default;
lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_levelParams___default;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkBinding_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_toProcess___default;
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_visitedExpr___default;
lean_object* l_Lean_Meta_Closure_State_visitedLevel___default___closed__1;
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitExpr___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1(lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateSucc_x21___closed__2;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__2(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLetDecls___default;
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__1(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__2;
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___closed__2;
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
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_visitedLevel___default___closed__1;
return x_1;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedExpr___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedExpr___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedExpr___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_levelParams___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_nextLevelIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_levelArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLocalDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLetDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_nextExprIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_exprMVarArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_exprFVarArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_toProcess___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_Closure_visitLevel_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_Closure_visitLevel_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_visitLevel_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(x_8, x_2, x_7);
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
lean_object* l_Lean_Meta_Closure_visitExpr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_Closure_visitExpr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_visitExpr_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitExpr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitExpr___spec__6(x_8, x_2, x_7);
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
x_13 = l_Lean_Level_LevelToFormat_toResult___main___closed__3;
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
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get_uint64(x_1, 0);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_2(x_7, x_1, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_2, x_1, x_11, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_3, x_1, x_15, x_16, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_4(x_4, x_1, x_20, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_3(x_6, x_1, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_3(x_5, x_1, x_29, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectLevelAux_match__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_24 = l_Lean_Meta_Closure_collectLevelAux(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
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
x_78 = l_Lean_Meta_Closure_collectLevelAux(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_75);
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
x_120 = l_Lean_Meta_Closure_collectLevelAux(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
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
x_174 = l_Lean_Meta_Closure_collectLevelAux(x_158, x_2, x_3, x_4, x_5, x_6, x_7, x_171);
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
x_216 = l_Lean_Meta_Closure_collectLevelAux(x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_213);
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
x_13 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
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
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
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
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Closure_preprocess___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
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
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(x_1);
x_6 = lean_apply_2(x_4, x_5, x_2);
return x_6;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(x_1);
x_8 = lean_apply_2(x_4, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Meta_Closure_collectExprAux_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_2(x_11, x_13, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_2(x_10, x_17, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_2(x_8, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_3(x_9, x_25, x_26, x_28);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_33 = lean_box_uint64(x_32);
x_34 = lean_apply_3(x_6, x_30, x_31, x_33);
return x_34;
}
case 6:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_39 = lean_box_uint64(x_38);
x_40 = lean_apply_4(x_4, x_35, x_36, x_37, x_39);
return x_40;
}
case 7:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_45 = lean_box_uint64(x_44);
x_46 = lean_apply_4(x_3, x_41, x_42, x_43, x_45);
return x_46;
}
case 8:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 3);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_52 = lean_box_uint64(x_51);
x_53 = lean_apply_5(x_5, x_47, x_48, x_49, x_50, x_52);
return x_53;
}
case 10:
{
lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_57 = lean_box_uint64(x_56);
x_58 = lean_apply_3(x_7, x_54, x_55, x_57);
return x_58;
}
case 11:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 2);
lean_inc(x_61);
x_62 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_63 = lean_box_uint64(x_62);
x_64 = lean_apply_4(x_2, x_59, x_60, x_61, x_63);
return x_64;
}
default: 
{
lean_object* x_65; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_apply_1(x_12, x_1);
return x_65;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux_match__2___rarg), 12, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed), 2, 0);
return x_6;
}
}
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_20, x_4, x_5, x_6, x_7, x_12);
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
x_29 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_32, x_4, x_5, x_6, x_7, x_24);
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
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
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
x_28 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
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
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_28 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = lean_unbox(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Meta_Closure_pushToProcess(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = l_Lean_mkFVar(x_32);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_mkFVar(x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
x_45 = l_Lean_LocalDecl_value_x3f(x_43);
lean_dec(x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_free_object(x_28);
x_46 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_7, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_Closure_pushToProcess(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = l_Lean_mkFVar(x_47);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = l_Lean_mkFVar(x_47);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_27);
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
lean_dec(x_45);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Meta_Closure_preprocess(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_105; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_105 = l_Lean_Expr_hasLevelParam(x_59);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_hasFVar(x_59);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasMVar(x_59);
if (x_107 == 0)
{
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_28, 1, x_60);
lean_ctor_set(x_28, 0, x_59);
return x_28;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_28);
x_108 = lean_st_ref_get(x_3, x_60);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_62 = x_109;
x_63 = x_110;
goto block_104;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_28);
x_111 = lean_st_ref_get(x_3, x_60);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_62 = x_112;
x_63 = x_113;
goto block_104;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_free_object(x_28);
x_114 = lean_st_ref_get(x_3, x_60);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_62 = x_115;
x_63 = x_116;
goto block_104;
}
block_104:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_64, x_59);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
lean_dec(x_61);
lean_inc(x_59);
x_66 = l_Lean_Meta_Closure_collectExprAux(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_st_ref_take(x_3, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_67);
x_74 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_73, x_59, x_67);
lean_ctor_set(x_70, 1, x_74);
x_75 = lean_st_ref_set(x_3, x_70, x_71);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_67);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_80 = lean_ctor_get(x_70, 0);
x_81 = lean_ctor_get(x_70, 1);
x_82 = lean_ctor_get(x_70, 2);
x_83 = lean_ctor_get(x_70, 3);
x_84 = lean_ctor_get(x_70, 4);
x_85 = lean_ctor_get(x_70, 5);
x_86 = lean_ctor_get(x_70, 6);
x_87 = lean_ctor_get(x_70, 7);
x_88 = lean_ctor_get(x_70, 8);
x_89 = lean_ctor_get(x_70, 9);
x_90 = lean_ctor_get(x_70, 10);
x_91 = lean_ctor_get(x_70, 11);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_70);
lean_inc(x_67);
x_92 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_81, x_59, x_67);
x_93 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_82);
lean_ctor_set(x_93, 3, x_83);
lean_ctor_set(x_93, 4, x_84);
lean_ctor_set(x_93, 5, x_85);
lean_ctor_set(x_93, 6, x_86);
lean_ctor_set(x_93, 7, x_87);
lean_ctor_set(x_93, 8, x_88);
lean_ctor_set(x_93, 9, x_89);
lean_ctor_set(x_93, 10, x_90);
lean_ctor_set(x_93, 11, x_91);
x_94 = lean_st_ref_set(x_3, x_93, x_71);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_67);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_59);
x_98 = !lean_is_exclusive(x_66);
if (x_98 == 0)
{
return x_66;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_66, 0);
x_100 = lean_ctor_get(x_66, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_66);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = lean_ctor_get(x_65, 0);
lean_inc(x_102);
lean_dec(x_65);
if (lean_is_scalar(x_61)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_61;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_63);
return x_103;
}
}
}
else
{
uint8_t x_117; 
lean_free_object(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_58);
if (x_117 == 0)
{
return x_58;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_58, 0);
x_119 = lean_ctor_get(x_58, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_58);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_28, 0);
x_122 = lean_ctor_get(x_28, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_28);
x_123 = l_Lean_LocalDecl_value_x3f(x_121);
lean_dec(x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_124 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_7, x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_27);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_Meta_Closure_pushToProcess(x_127, x_2, x_3, x_4, x_5, x_6, x_7, x_126);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = l_Lean_mkFVar(x_125);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_27);
x_133 = lean_ctor_get(x_123, 0);
lean_inc(x_133);
lean_dec(x_123);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_134 = l_Lean_Meta_Closure_preprocess(x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_122);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_174; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_174 = l_Lean_Expr_hasLevelParam(x_135);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasFVar(x_135);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_Expr_hasMVar(x_135);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_137);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_135);
lean_ctor_set(x_177, 1, x_136);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_st_ref_get(x_3, x_136);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_138 = x_179;
x_139 = x_180;
goto block_173;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_st_ref_get(x_3, x_136);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_138 = x_182;
x_139 = x_183;
goto block_173;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_st_ref_get(x_3, x_136);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_138 = x_185;
x_139 = x_186;
goto block_173;
}
block_173:
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_140, x_135);
lean_dec(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
lean_dec(x_137);
lean_inc(x_135);
x_142 = l_Lean_Meta_Closure_collectExprAux(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_st_ref_take(x_3, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 5);
lean_inc(x_153);
x_154 = lean_ctor_get(x_146, 6);
lean_inc(x_154);
x_155 = lean_ctor_get(x_146, 7);
lean_inc(x_155);
x_156 = lean_ctor_get(x_146, 8);
lean_inc(x_156);
x_157 = lean_ctor_get(x_146, 9);
lean_inc(x_157);
x_158 = lean_ctor_get(x_146, 10);
lean_inc(x_158);
x_159 = lean_ctor_get(x_146, 11);
lean_inc(x_159);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 lean_ctor_release(x_146, 6);
 lean_ctor_release(x_146, 7);
 lean_ctor_release(x_146, 8);
 lean_ctor_release(x_146, 9);
 lean_ctor_release(x_146, 10);
 lean_ctor_release(x_146, 11);
 x_160 = x_146;
} else {
 lean_dec_ref(x_146);
 x_160 = lean_box(0);
}
lean_inc(x_143);
x_161 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_149, x_135, x_143);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 12, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_148);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_150);
lean_ctor_set(x_162, 3, x_151);
lean_ctor_set(x_162, 4, x_152);
lean_ctor_set(x_162, 5, x_153);
lean_ctor_set(x_162, 6, x_154);
lean_ctor_set(x_162, 7, x_155);
lean_ctor_set(x_162, 8, x_156);
lean_ctor_set(x_162, 9, x_157);
lean_ctor_set(x_162, 10, x_158);
lean_ctor_set(x_162, 11, x_159);
x_163 = lean_st_ref_set(x_3, x_162, x_147);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_143);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_135);
x_167 = lean_ctor_get(x_142, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_142, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_169 = x_142;
} else {
 lean_dec_ref(x_142);
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
lean_object* x_171; lean_object* x_172; 
lean_dec(x_135);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_171 = lean_ctor_get(x_141, 0);
lean_inc(x_171);
lean_dec(x_141);
if (lean_is_scalar(x_137)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_137;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_139);
return x_172;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_187 = lean_ctor_get(x_134, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_134, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_189 = x_134;
} else {
 lean_dec_ref(x_134);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = !lean_is_exclusive(x_28);
if (x_191 == 0)
{
return x_28;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_28, 0);
x_193 = lean_ctor_get(x_28, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_28);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
case 2:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_1, 0);
lean_inc(x_195);
x_196 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3(x_195, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_249; lean_object* x_250; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_249 = lean_ctor_get(x_197, 2);
lean_inc(x_249);
lean_dec(x_197);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_250 = l_Lean_Meta_Closure_preprocess(x_249, x_2, x_3, x_4, x_5, x_6, x_7, x_198);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_290; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_290 = l_Lean_Expr_hasLevelParam(x_251);
if (x_290 == 0)
{
uint8_t x_291; 
x_291 = l_Lean_Expr_hasFVar(x_251);
if (x_291 == 0)
{
uint8_t x_292; 
x_292 = l_Lean_Expr_hasMVar(x_251);
if (x_292 == 0)
{
x_199 = x_251;
x_200 = x_252;
goto block_248;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_st_ref_get(x_3, x_252);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_253 = x_294;
x_254 = x_295;
goto block_289;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_st_ref_get(x_3, x_252);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_253 = x_297;
x_254 = x_298;
goto block_289;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_st_ref_get(x_3, x_252);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_253 = x_300;
x_254 = x_301;
goto block_289;
}
block_289:
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_255, x_251);
lean_dec(x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_251);
x_257 = l_Lean_Meta_Closure_collectExprAux(x_251, x_2, x_3, x_4, x_5, x_6, x_7, x_254);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_st_ref_take(x_3, x_259);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = !lean_is_exclusive(x_261);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_258);
x_265 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_264, x_251, x_258);
lean_ctor_set(x_261, 1, x_265);
x_266 = lean_st_ref_set(x_3, x_261, x_262);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_199 = x_258;
x_200 = x_267;
goto block_248;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_268 = lean_ctor_get(x_261, 0);
x_269 = lean_ctor_get(x_261, 1);
x_270 = lean_ctor_get(x_261, 2);
x_271 = lean_ctor_get(x_261, 3);
x_272 = lean_ctor_get(x_261, 4);
x_273 = lean_ctor_get(x_261, 5);
x_274 = lean_ctor_get(x_261, 6);
x_275 = lean_ctor_get(x_261, 7);
x_276 = lean_ctor_get(x_261, 8);
x_277 = lean_ctor_get(x_261, 9);
x_278 = lean_ctor_get(x_261, 10);
x_279 = lean_ctor_get(x_261, 11);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_261);
lean_inc(x_258);
x_280 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_269, x_251, x_258);
x_281 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_281, 0, x_268);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_281, 2, x_270);
lean_ctor_set(x_281, 3, x_271);
lean_ctor_set(x_281, 4, x_272);
lean_ctor_set(x_281, 5, x_273);
lean_ctor_set(x_281, 6, x_274);
lean_ctor_set(x_281, 7, x_275);
lean_ctor_set(x_281, 8, x_276);
lean_ctor_set(x_281, 9, x_277);
lean_ctor_set(x_281, 10, x_278);
lean_ctor_set(x_281, 11, x_279);
x_282 = lean_st_ref_set(x_3, x_281, x_262);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_199 = x_258;
x_200 = x_283;
goto block_248;
}
}
else
{
uint8_t x_284; 
lean_dec(x_251);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_257);
if (x_284 == 0)
{
return x_257;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_257, 0);
x_286 = lean_ctor_get(x_257, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_257);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
lean_object* x_288; 
lean_dec(x_251);
x_288 = lean_ctor_get(x_256, 0);
lean_inc(x_288);
lean_dec(x_256);
x_199 = x_288;
x_200 = x_254;
goto block_248;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_250);
if (x_302 == 0)
{
return x_250;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_250, 0);
x_304 = lean_ctor_get(x_250, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_250);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
block_248:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_201 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_7, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_203);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_st_ref_take(x_3, x_206);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = !lean_is_exclusive(x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_211 = lean_ctor_get(x_208, 6);
x_212 = lean_ctor_get(x_208, 9);
x_213 = lean_unsigned_to_nat(0u);
x_214 = 0;
lean_inc(x_202);
x_215 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_202);
lean_ctor_set(x_215, 2, x_205);
lean_ctor_set(x_215, 3, x_199);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_array_push(x_211, x_215);
x_217 = lean_array_push(x_212, x_1);
lean_ctor_set(x_208, 9, x_217);
lean_ctor_set(x_208, 6, x_216);
x_218 = lean_st_ref_set(x_3, x_208, x_209);
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_218, 0);
lean_dec(x_220);
x_221 = l_Lean_mkFVar(x_202);
lean_ctor_set(x_218, 0, x_221);
return x_218;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
lean_dec(x_218);
x_223 = l_Lean_mkFVar(x_202);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_225 = lean_ctor_get(x_208, 0);
x_226 = lean_ctor_get(x_208, 1);
x_227 = lean_ctor_get(x_208, 2);
x_228 = lean_ctor_get(x_208, 3);
x_229 = lean_ctor_get(x_208, 4);
x_230 = lean_ctor_get(x_208, 5);
x_231 = lean_ctor_get(x_208, 6);
x_232 = lean_ctor_get(x_208, 7);
x_233 = lean_ctor_get(x_208, 8);
x_234 = lean_ctor_get(x_208, 9);
x_235 = lean_ctor_get(x_208, 10);
x_236 = lean_ctor_get(x_208, 11);
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
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_208);
x_237 = lean_unsigned_to_nat(0u);
x_238 = 0;
lean_inc(x_202);
x_239 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_202);
lean_ctor_set(x_239, 2, x_205);
lean_ctor_set(x_239, 3, x_199);
lean_ctor_set_uint8(x_239, sizeof(void*)*4, x_238);
x_240 = lean_array_push(x_231, x_239);
x_241 = lean_array_push(x_234, x_1);
x_242 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_242, 0, x_225);
lean_ctor_set(x_242, 1, x_226);
lean_ctor_set(x_242, 2, x_227);
lean_ctor_set(x_242, 3, x_228);
lean_ctor_set(x_242, 4, x_229);
lean_ctor_set(x_242, 5, x_230);
lean_ctor_set(x_242, 6, x_240);
lean_ctor_set(x_242, 7, x_232);
lean_ctor_set(x_242, 8, x_233);
lean_ctor_set(x_242, 9, x_241);
lean_ctor_set(x_242, 10, x_235);
lean_ctor_set(x_242, 11, x_236);
x_243 = lean_st_ref_set(x_3, x_242, x_209);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
x_246 = l_Lean_mkFVar(x_202);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_196);
if (x_306 == 0)
{
return x_196;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_196, 0);
x_308 = lean_ctor_get(x_196, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_196);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
case 3:
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_310 = lean_ctor_get(x_1, 0);
lean_inc(x_310);
x_311 = l_Lean_Meta_Closure_collectLevel(x_310, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_311, 0);
x_314 = lean_expr_update_sort(x_1, x_313);
lean_ctor_set(x_311, 0, x_314);
return x_311;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_315 = lean_ctor_get(x_311, 0);
x_316 = lean_ctor_get(x_311, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_311);
x_317 = lean_expr_update_sort(x_1, x_315);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
case 4:
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_319 = lean_ctor_get(x_1, 1);
lean_inc(x_319);
x_320 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4(x_319, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_320, 0);
x_323 = lean_expr_update_const(x_1, x_322);
lean_ctor_set(x_320, 0, x_323);
return x_320;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_320, 0);
x_325 = lean_ctor_get(x_320, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_320);
x_326 = lean_expr_update_const(x_1, x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
case 5:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_391; lean_object* x_392; uint8_t x_428; 
x_328 = lean_ctor_get(x_1, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_1, 1);
lean_inc(x_329);
x_428 = l_Lean_Expr_hasLevelParam(x_328);
if (x_428 == 0)
{
uint8_t x_429; 
x_429 = l_Lean_Expr_hasFVar(x_328);
if (x_429 == 0)
{
uint8_t x_430; 
x_430 = l_Lean_Expr_hasMVar(x_328);
if (x_430 == 0)
{
x_330 = x_328;
x_331 = x_8;
goto block_390;
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
x_391 = x_432;
x_392 = x_433;
goto block_427;
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
x_391 = x_435;
x_392 = x_436;
goto block_427;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_st_ref_get(x_3, x_8);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_391 = x_438;
x_392 = x_439;
goto block_427;
}
block_390:
{
lean_object* x_332; lean_object* x_333; lean_object* x_341; lean_object* x_342; uint8_t x_378; 
x_378 = l_Lean_Expr_hasLevelParam(x_329);
if (x_378 == 0)
{
uint8_t x_379; 
x_379 = l_Lean_Expr_hasFVar(x_329);
if (x_379 == 0)
{
uint8_t x_380; 
x_380 = l_Lean_Expr_hasMVar(x_329);
if (x_380 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_332 = x_329;
x_333 = x_331;
goto block_340;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_st_ref_get(x_3, x_331);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_341 = x_382;
x_342 = x_383;
goto block_377;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_st_ref_get(x_3, x_331);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_341 = x_385;
x_342 = x_386;
goto block_377;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_st_ref_get(x_3, x_331);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_341 = x_388;
x_342 = x_389;
goto block_377;
}
block_340:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_expr_update_app(x_1, x_330, x_332);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_332);
lean_dec(x_330);
lean_dec(x_1);
x_336 = l_Lean_Expr_Inhabited;
x_337 = l_Lean_Expr_updateApp_x21___closed__1;
x_338 = lean_panic_fn(x_336, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_333);
return x_339;
}
}
block_377:
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_343, x_329);
lean_dec(x_343);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
lean_inc(x_329);
x_345 = l_Lean_Meta_Closure_collectExprAux(x_329, x_2, x_3, x_4, x_5, x_6, x_7, x_342);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_st_ref_take(x_3, x_347);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = !lean_is_exclusive(x_349);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_346);
x_353 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_352, x_329, x_346);
lean_ctor_set(x_349, 1, x_353);
x_354 = lean_st_ref_set(x_3, x_349, x_350);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
x_332 = x_346;
x_333 = x_355;
goto block_340;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_356 = lean_ctor_get(x_349, 0);
x_357 = lean_ctor_get(x_349, 1);
x_358 = lean_ctor_get(x_349, 2);
x_359 = lean_ctor_get(x_349, 3);
x_360 = lean_ctor_get(x_349, 4);
x_361 = lean_ctor_get(x_349, 5);
x_362 = lean_ctor_get(x_349, 6);
x_363 = lean_ctor_get(x_349, 7);
x_364 = lean_ctor_get(x_349, 8);
x_365 = lean_ctor_get(x_349, 9);
x_366 = lean_ctor_get(x_349, 10);
x_367 = lean_ctor_get(x_349, 11);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_349);
lean_inc(x_346);
x_368 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_357, x_329, x_346);
x_369 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_369, 0, x_356);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set(x_369, 2, x_358);
lean_ctor_set(x_369, 3, x_359);
lean_ctor_set(x_369, 4, x_360);
lean_ctor_set(x_369, 5, x_361);
lean_ctor_set(x_369, 6, x_362);
lean_ctor_set(x_369, 7, x_363);
lean_ctor_set(x_369, 8, x_364);
lean_ctor_set(x_369, 9, x_365);
lean_ctor_set(x_369, 10, x_366);
lean_ctor_set(x_369, 11, x_367);
x_370 = lean_st_ref_set(x_3, x_369, x_350);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
x_332 = x_346;
x_333 = x_371;
goto block_340;
}
}
else
{
uint8_t x_372; 
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_1);
x_372 = !lean_is_exclusive(x_345);
if (x_372 == 0)
{
return x_345;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_345, 0);
x_374 = lean_ctor_get(x_345, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_345);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
return x_375;
}
}
}
else
{
lean_object* x_376; 
lean_dec(x_329);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_376 = lean_ctor_get(x_344, 0);
lean_inc(x_376);
lean_dec(x_344);
x_332 = x_376;
x_333 = x_342;
goto block_340;
}
}
}
block_427:
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_393, x_328);
lean_dec(x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_328);
x_395 = l_Lean_Meta_Closure_collectExprAux(x_328, x_2, x_3, x_4, x_5, x_6, x_7, x_392);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_st_ref_take(x_3, x_397);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = !lean_is_exclusive(x_399);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_396);
x_403 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_402, x_328, x_396);
lean_ctor_set(x_399, 1, x_403);
x_404 = lean_st_ref_set(x_3, x_399, x_400);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_330 = x_396;
x_331 = x_405;
goto block_390;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_406 = lean_ctor_get(x_399, 0);
x_407 = lean_ctor_get(x_399, 1);
x_408 = lean_ctor_get(x_399, 2);
x_409 = lean_ctor_get(x_399, 3);
x_410 = lean_ctor_get(x_399, 4);
x_411 = lean_ctor_get(x_399, 5);
x_412 = lean_ctor_get(x_399, 6);
x_413 = lean_ctor_get(x_399, 7);
x_414 = lean_ctor_get(x_399, 8);
x_415 = lean_ctor_get(x_399, 9);
x_416 = lean_ctor_get(x_399, 10);
x_417 = lean_ctor_get(x_399, 11);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_inc(x_408);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_399);
lean_inc(x_396);
x_418 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_407, x_328, x_396);
x_419 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_419, 0, x_406);
lean_ctor_set(x_419, 1, x_418);
lean_ctor_set(x_419, 2, x_408);
lean_ctor_set(x_419, 3, x_409);
lean_ctor_set(x_419, 4, x_410);
lean_ctor_set(x_419, 5, x_411);
lean_ctor_set(x_419, 6, x_412);
lean_ctor_set(x_419, 7, x_413);
lean_ctor_set(x_419, 8, x_414);
lean_ctor_set(x_419, 9, x_415);
lean_ctor_set(x_419, 10, x_416);
lean_ctor_set(x_419, 11, x_417);
x_420 = lean_st_ref_set(x_3, x_419, x_400);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_330 = x_396;
x_331 = x_421;
goto block_390;
}
}
else
{
uint8_t x_422; 
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_422 = !lean_is_exclusive(x_395);
if (x_422 == 0)
{
return x_395;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_395, 0);
x_424 = lean_ctor_get(x_395, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_395);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
lean_object* x_426; 
lean_dec(x_328);
x_426 = lean_ctor_get(x_394, 0);
lean_inc(x_426);
lean_dec(x_394);
x_330 = x_426;
x_331 = x_392;
goto block_390;
}
}
}
case 6:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_505; lean_object* x_506; uint8_t x_542; 
x_440 = lean_ctor_get(x_1, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_1, 2);
lean_inc(x_441);
x_542 = l_Lean_Expr_hasLevelParam(x_440);
if (x_542 == 0)
{
uint8_t x_543; 
x_543 = l_Lean_Expr_hasFVar(x_440);
if (x_543 == 0)
{
uint8_t x_544; 
x_544 = l_Lean_Expr_hasMVar(x_440);
if (x_544 == 0)
{
x_442 = x_440;
x_443 = x_8;
goto block_504;
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
x_505 = x_546;
x_506 = x_547;
goto block_541;
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
x_505 = x_549;
x_506 = x_550;
goto block_541;
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_st_ref_get(x_3, x_8);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_505 = x_552;
x_506 = x_553;
goto block_541;
}
block_504:
{
lean_object* x_444; lean_object* x_445; lean_object* x_455; lean_object* x_456; uint8_t x_492; 
x_492 = l_Lean_Expr_hasLevelParam(x_441);
if (x_492 == 0)
{
uint8_t x_493; 
x_493 = l_Lean_Expr_hasFVar(x_441);
if (x_493 == 0)
{
uint8_t x_494; 
x_494 = l_Lean_Expr_hasMVar(x_441);
if (x_494 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_444 = x_441;
x_445 = x_443;
goto block_454;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_st_ref_get(x_3, x_443);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_455 = x_496;
x_456 = x_497;
goto block_491;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_st_ref_get(x_3, x_443);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_455 = x_499;
x_456 = x_500;
goto block_491;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_st_ref_get(x_3, x_443);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_455 = x_502;
x_456 = x_503;
goto block_491;
}
block_454:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; 
x_446 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_447 = (uint8_t)((x_446 << 24) >> 61);
x_448 = lean_expr_update_lambda(x_1, x_447, x_442, x_444);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_445);
return x_449;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_444);
lean_dec(x_442);
lean_dec(x_1);
x_450 = l_Lean_Expr_Inhabited;
x_451 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_452 = lean_panic_fn(x_450, x_451);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_445);
return x_453;
}
}
block_491:
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_457, x_441);
lean_dec(x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; 
lean_inc(x_441);
x_459 = l_Lean_Meta_Closure_collectExprAux(x_441, x_2, x_3, x_4, x_5, x_6, x_7, x_456);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = lean_st_ref_take(x_3, x_461);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = !lean_is_exclusive(x_463);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_460);
x_467 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_466, x_441, x_460);
lean_ctor_set(x_463, 1, x_467);
x_468 = lean_st_ref_set(x_3, x_463, x_464);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
x_444 = x_460;
x_445 = x_469;
goto block_454;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_470 = lean_ctor_get(x_463, 0);
x_471 = lean_ctor_get(x_463, 1);
x_472 = lean_ctor_get(x_463, 2);
x_473 = lean_ctor_get(x_463, 3);
x_474 = lean_ctor_get(x_463, 4);
x_475 = lean_ctor_get(x_463, 5);
x_476 = lean_ctor_get(x_463, 6);
x_477 = lean_ctor_get(x_463, 7);
x_478 = lean_ctor_get(x_463, 8);
x_479 = lean_ctor_get(x_463, 9);
x_480 = lean_ctor_get(x_463, 10);
x_481 = lean_ctor_get(x_463, 11);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_inc(x_472);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_463);
lean_inc(x_460);
x_482 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_471, x_441, x_460);
x_483 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_483, 0, x_470);
lean_ctor_set(x_483, 1, x_482);
lean_ctor_set(x_483, 2, x_472);
lean_ctor_set(x_483, 3, x_473);
lean_ctor_set(x_483, 4, x_474);
lean_ctor_set(x_483, 5, x_475);
lean_ctor_set(x_483, 6, x_476);
lean_ctor_set(x_483, 7, x_477);
lean_ctor_set(x_483, 8, x_478);
lean_ctor_set(x_483, 9, x_479);
lean_ctor_set(x_483, 10, x_480);
lean_ctor_set(x_483, 11, x_481);
x_484 = lean_st_ref_set(x_3, x_483, x_464);
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec(x_484);
x_444 = x_460;
x_445 = x_485;
goto block_454;
}
}
else
{
uint8_t x_486; 
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_1);
x_486 = !lean_is_exclusive(x_459);
if (x_486 == 0)
{
return x_459;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_459, 0);
x_488 = lean_ctor_get(x_459, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_459);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
return x_489;
}
}
}
else
{
lean_object* x_490; 
lean_dec(x_441);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_490 = lean_ctor_get(x_458, 0);
lean_inc(x_490);
lean_dec(x_458);
x_444 = x_490;
x_445 = x_456;
goto block_454;
}
}
}
block_541:
{
lean_object* x_507; lean_object* x_508; 
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_507, x_440);
lean_dec(x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_440);
x_509 = l_Lean_Meta_Closure_collectExprAux(x_440, x_2, x_3, x_4, x_5, x_6, x_7, x_506);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec(x_509);
x_512 = lean_st_ref_take(x_3, x_511);
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = !lean_is_exclusive(x_513);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_516 = lean_ctor_get(x_513, 1);
lean_inc(x_510);
x_517 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_516, x_440, x_510);
lean_ctor_set(x_513, 1, x_517);
x_518 = lean_st_ref_set(x_3, x_513, x_514);
x_519 = lean_ctor_get(x_518, 1);
lean_inc(x_519);
lean_dec(x_518);
x_442 = x_510;
x_443 = x_519;
goto block_504;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_520 = lean_ctor_get(x_513, 0);
x_521 = lean_ctor_get(x_513, 1);
x_522 = lean_ctor_get(x_513, 2);
x_523 = lean_ctor_get(x_513, 3);
x_524 = lean_ctor_get(x_513, 4);
x_525 = lean_ctor_get(x_513, 5);
x_526 = lean_ctor_get(x_513, 6);
x_527 = lean_ctor_get(x_513, 7);
x_528 = lean_ctor_get(x_513, 8);
x_529 = lean_ctor_get(x_513, 9);
x_530 = lean_ctor_get(x_513, 10);
x_531 = lean_ctor_get(x_513, 11);
lean_inc(x_531);
lean_inc(x_530);
lean_inc(x_529);
lean_inc(x_528);
lean_inc(x_527);
lean_inc(x_526);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
lean_inc(x_522);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_513);
lean_inc(x_510);
x_532 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_521, x_440, x_510);
x_533 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_533, 0, x_520);
lean_ctor_set(x_533, 1, x_532);
lean_ctor_set(x_533, 2, x_522);
lean_ctor_set(x_533, 3, x_523);
lean_ctor_set(x_533, 4, x_524);
lean_ctor_set(x_533, 5, x_525);
lean_ctor_set(x_533, 6, x_526);
lean_ctor_set(x_533, 7, x_527);
lean_ctor_set(x_533, 8, x_528);
lean_ctor_set(x_533, 9, x_529);
lean_ctor_set(x_533, 10, x_530);
lean_ctor_set(x_533, 11, x_531);
x_534 = lean_st_ref_set(x_3, x_533, x_514);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
x_442 = x_510;
x_443 = x_535;
goto block_504;
}
}
else
{
uint8_t x_536; 
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_536 = !lean_is_exclusive(x_509);
if (x_536 == 0)
{
return x_509;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_537 = lean_ctor_get(x_509, 0);
x_538 = lean_ctor_get(x_509, 1);
lean_inc(x_538);
lean_inc(x_537);
lean_dec(x_509);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
return x_539;
}
}
}
else
{
lean_object* x_540; 
lean_dec(x_440);
x_540 = lean_ctor_get(x_508, 0);
lean_inc(x_540);
lean_dec(x_508);
x_442 = x_540;
x_443 = x_506;
goto block_504;
}
}
}
case 7:
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_619; lean_object* x_620; uint8_t x_656; 
x_554 = lean_ctor_get(x_1, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_1, 2);
lean_inc(x_555);
x_656 = l_Lean_Expr_hasLevelParam(x_554);
if (x_656 == 0)
{
uint8_t x_657; 
x_657 = l_Lean_Expr_hasFVar(x_554);
if (x_657 == 0)
{
uint8_t x_658; 
x_658 = l_Lean_Expr_hasMVar(x_554);
if (x_658 == 0)
{
x_556 = x_554;
x_557 = x_8;
goto block_618;
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
x_619 = x_660;
x_620 = x_661;
goto block_655;
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
x_619 = x_663;
x_620 = x_664;
goto block_655;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_st_ref_get(x_3, x_8);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
x_619 = x_666;
x_620 = x_667;
goto block_655;
}
block_618:
{
lean_object* x_558; lean_object* x_559; lean_object* x_569; lean_object* x_570; uint8_t x_606; 
x_606 = l_Lean_Expr_hasLevelParam(x_555);
if (x_606 == 0)
{
uint8_t x_607; 
x_607 = l_Lean_Expr_hasFVar(x_555);
if (x_607 == 0)
{
uint8_t x_608; 
x_608 = l_Lean_Expr_hasMVar(x_555);
if (x_608 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_558 = x_555;
x_559 = x_557;
goto block_568;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_st_ref_get(x_3, x_557);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_569 = x_610;
x_570 = x_611;
goto block_605;
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = lean_st_ref_get(x_3, x_557);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_569 = x_613;
x_570 = x_614;
goto block_605;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_st_ref_get(x_3, x_557);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
x_569 = x_616;
x_570 = x_617;
goto block_605;
}
block_568:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_560; uint8_t x_561; lean_object* x_562; lean_object* x_563; 
x_560 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_561 = (uint8_t)((x_560 << 24) >> 61);
x_562 = lean_expr_update_forall(x_1, x_561, x_556, x_558);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_559);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_1);
x_564 = l_Lean_Expr_Inhabited;
x_565 = l_Lean_Expr_updateForallE_x21___closed__1;
x_566 = lean_panic_fn(x_564, x_565);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_559);
return x_567;
}
}
block_605:
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_572 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_571, x_555);
lean_dec(x_571);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; 
lean_inc(x_555);
x_573 = l_Lean_Meta_Closure_collectExprAux(x_555, x_2, x_3, x_4, x_5, x_6, x_7, x_570);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_st_ref_take(x_3, x_575);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = !lean_is_exclusive(x_577);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_577, 1);
lean_inc(x_574);
x_581 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_580, x_555, x_574);
lean_ctor_set(x_577, 1, x_581);
x_582 = lean_st_ref_set(x_3, x_577, x_578);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
lean_dec(x_582);
x_558 = x_574;
x_559 = x_583;
goto block_568;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_584 = lean_ctor_get(x_577, 0);
x_585 = lean_ctor_get(x_577, 1);
x_586 = lean_ctor_get(x_577, 2);
x_587 = lean_ctor_get(x_577, 3);
x_588 = lean_ctor_get(x_577, 4);
x_589 = lean_ctor_get(x_577, 5);
x_590 = lean_ctor_get(x_577, 6);
x_591 = lean_ctor_get(x_577, 7);
x_592 = lean_ctor_get(x_577, 8);
x_593 = lean_ctor_get(x_577, 9);
x_594 = lean_ctor_get(x_577, 10);
x_595 = lean_ctor_get(x_577, 11);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
lean_inc(x_592);
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_587);
lean_inc(x_586);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_577);
lean_inc(x_574);
x_596 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_585, x_555, x_574);
x_597 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_597, 0, x_584);
lean_ctor_set(x_597, 1, x_596);
lean_ctor_set(x_597, 2, x_586);
lean_ctor_set(x_597, 3, x_587);
lean_ctor_set(x_597, 4, x_588);
lean_ctor_set(x_597, 5, x_589);
lean_ctor_set(x_597, 6, x_590);
lean_ctor_set(x_597, 7, x_591);
lean_ctor_set(x_597, 8, x_592);
lean_ctor_set(x_597, 9, x_593);
lean_ctor_set(x_597, 10, x_594);
lean_ctor_set(x_597, 11, x_595);
x_598 = lean_st_ref_set(x_3, x_597, x_578);
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
lean_dec(x_598);
x_558 = x_574;
x_559 = x_599;
goto block_568;
}
}
else
{
uint8_t x_600; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_1);
x_600 = !lean_is_exclusive(x_573);
if (x_600 == 0)
{
return x_573;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_573, 0);
x_602 = lean_ctor_get(x_573, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_573);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
return x_603;
}
}
}
else
{
lean_object* x_604; 
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_604 = lean_ctor_get(x_572, 0);
lean_inc(x_604);
lean_dec(x_572);
x_558 = x_604;
x_559 = x_570;
goto block_568;
}
}
}
block_655:
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_621, x_554);
lean_dec(x_621);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_554);
x_623 = l_Lean_Meta_Closure_collectExprAux(x_554, x_2, x_3, x_4, x_5, x_6, x_7, x_620);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
x_626 = lean_st_ref_take(x_3, x_625);
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
lean_dec(x_626);
x_629 = !lean_is_exclusive(x_627);
if (x_629 == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_630 = lean_ctor_get(x_627, 1);
lean_inc(x_624);
x_631 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_630, x_554, x_624);
lean_ctor_set(x_627, 1, x_631);
x_632 = lean_st_ref_set(x_3, x_627, x_628);
x_633 = lean_ctor_get(x_632, 1);
lean_inc(x_633);
lean_dec(x_632);
x_556 = x_624;
x_557 = x_633;
goto block_618;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_634 = lean_ctor_get(x_627, 0);
x_635 = lean_ctor_get(x_627, 1);
x_636 = lean_ctor_get(x_627, 2);
x_637 = lean_ctor_get(x_627, 3);
x_638 = lean_ctor_get(x_627, 4);
x_639 = lean_ctor_get(x_627, 5);
x_640 = lean_ctor_get(x_627, 6);
x_641 = lean_ctor_get(x_627, 7);
x_642 = lean_ctor_get(x_627, 8);
x_643 = lean_ctor_get(x_627, 9);
x_644 = lean_ctor_get(x_627, 10);
x_645 = lean_ctor_get(x_627, 11);
lean_inc(x_645);
lean_inc(x_644);
lean_inc(x_643);
lean_inc(x_642);
lean_inc(x_641);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_627);
lean_inc(x_624);
x_646 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_635, x_554, x_624);
x_647 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_647, 0, x_634);
lean_ctor_set(x_647, 1, x_646);
lean_ctor_set(x_647, 2, x_636);
lean_ctor_set(x_647, 3, x_637);
lean_ctor_set(x_647, 4, x_638);
lean_ctor_set(x_647, 5, x_639);
lean_ctor_set(x_647, 6, x_640);
lean_ctor_set(x_647, 7, x_641);
lean_ctor_set(x_647, 8, x_642);
lean_ctor_set(x_647, 9, x_643);
lean_ctor_set(x_647, 10, x_644);
lean_ctor_set(x_647, 11, x_645);
x_648 = lean_st_ref_set(x_3, x_647, x_628);
x_649 = lean_ctor_get(x_648, 1);
lean_inc(x_649);
lean_dec(x_648);
x_556 = x_624;
x_557 = x_649;
goto block_618;
}
}
else
{
uint8_t x_650; 
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_650 = !lean_is_exclusive(x_623);
if (x_650 == 0)
{
return x_623;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_623, 0);
x_652 = lean_ctor_get(x_623, 1);
lean_inc(x_652);
lean_inc(x_651);
lean_dec(x_623);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
return x_653;
}
}
}
else
{
lean_object* x_654; 
lean_dec(x_554);
x_654 = lean_ctor_get(x_622, 0);
lean_inc(x_654);
lean_dec(x_622);
x_556 = x_654;
x_557 = x_620;
goto block_618;
}
}
}
case 8:
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_784; lean_object* x_785; uint8_t x_821; 
x_668 = lean_ctor_get(x_1, 1);
lean_inc(x_668);
x_669 = lean_ctor_get(x_1, 2);
lean_inc(x_669);
x_670 = lean_ctor_get(x_1, 3);
lean_inc(x_670);
x_821 = l_Lean_Expr_hasLevelParam(x_668);
if (x_821 == 0)
{
uint8_t x_822; 
x_822 = l_Lean_Expr_hasFVar(x_668);
if (x_822 == 0)
{
uint8_t x_823; 
x_823 = l_Lean_Expr_hasMVar(x_668);
if (x_823 == 0)
{
x_671 = x_668;
x_672 = x_8;
goto block_783;
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
x_784 = x_825;
x_785 = x_826;
goto block_820;
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
x_784 = x_828;
x_785 = x_829;
goto block_820;
}
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_830 = lean_st_ref_get(x_3, x_8);
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_830, 1);
lean_inc(x_832);
lean_dec(x_830);
x_784 = x_831;
x_785 = x_832;
goto block_820;
}
block_783:
{
lean_object* x_673; lean_object* x_674; lean_object* x_734; lean_object* x_735; uint8_t x_771; 
x_771 = l_Lean_Expr_hasLevelParam(x_669);
if (x_771 == 0)
{
uint8_t x_772; 
x_772 = l_Lean_Expr_hasFVar(x_669);
if (x_772 == 0)
{
uint8_t x_773; 
x_773 = l_Lean_Expr_hasMVar(x_669);
if (x_773 == 0)
{
x_673 = x_669;
x_674 = x_672;
goto block_733;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_st_ref_get(x_3, x_672);
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
x_734 = x_775;
x_735 = x_776;
goto block_770;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_st_ref_get(x_3, x_672);
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_734 = x_778;
x_735 = x_779;
goto block_770;
}
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_st_ref_get(x_3, x_672);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_734 = x_781;
x_735 = x_782;
goto block_770;
}
block_733:
{
lean_object* x_675; lean_object* x_676; lean_object* x_684; lean_object* x_685; uint8_t x_721; 
x_721 = l_Lean_Expr_hasLevelParam(x_670);
if (x_721 == 0)
{
uint8_t x_722; 
x_722 = l_Lean_Expr_hasFVar(x_670);
if (x_722 == 0)
{
uint8_t x_723; 
x_723 = l_Lean_Expr_hasMVar(x_670);
if (x_723 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_675 = x_670;
x_676 = x_674;
goto block_683;
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_724 = lean_st_ref_get(x_3, x_674);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_684 = x_725;
x_685 = x_726;
goto block_720;
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_st_ref_get(x_3, x_674);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_684 = x_728;
x_685 = x_729;
goto block_720;
}
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_st_ref_get(x_3, x_674);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_684 = x_731;
x_685 = x_732;
goto block_720;
}
block_683:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_expr_update_let(x_1, x_671, x_673, x_675);
x_678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_676);
return x_678;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_671);
lean_dec(x_1);
x_679 = l_Lean_Expr_Inhabited;
x_680 = l_Lean_Expr_updateLet_x21___closed__1;
x_681 = lean_panic_fn(x_679, x_680);
x_682 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_676);
return x_682;
}
}
block_720:
{
lean_object* x_686; lean_object* x_687; 
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
x_687 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_686, x_670);
lean_dec(x_686);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; 
lean_inc(x_670);
x_688 = l_Lean_Meta_Closure_collectExprAux(x_670, x_2, x_3, x_4, x_5, x_6, x_7, x_685);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_691 = lean_st_ref_take(x_3, x_690);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = !lean_is_exclusive(x_692);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_695 = lean_ctor_get(x_692, 1);
lean_inc(x_689);
x_696 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_695, x_670, x_689);
lean_ctor_set(x_692, 1, x_696);
x_697 = lean_st_ref_set(x_3, x_692, x_693);
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
lean_dec(x_697);
x_675 = x_689;
x_676 = x_698;
goto block_683;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_699 = lean_ctor_get(x_692, 0);
x_700 = lean_ctor_get(x_692, 1);
x_701 = lean_ctor_get(x_692, 2);
x_702 = lean_ctor_get(x_692, 3);
x_703 = lean_ctor_get(x_692, 4);
x_704 = lean_ctor_get(x_692, 5);
x_705 = lean_ctor_get(x_692, 6);
x_706 = lean_ctor_get(x_692, 7);
x_707 = lean_ctor_get(x_692, 8);
x_708 = lean_ctor_get(x_692, 9);
x_709 = lean_ctor_get(x_692, 10);
x_710 = lean_ctor_get(x_692, 11);
lean_inc(x_710);
lean_inc(x_709);
lean_inc(x_708);
lean_inc(x_707);
lean_inc(x_706);
lean_inc(x_705);
lean_inc(x_704);
lean_inc(x_703);
lean_inc(x_702);
lean_inc(x_701);
lean_inc(x_700);
lean_inc(x_699);
lean_dec(x_692);
lean_inc(x_689);
x_711 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_700, x_670, x_689);
x_712 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_712, 0, x_699);
lean_ctor_set(x_712, 1, x_711);
lean_ctor_set(x_712, 2, x_701);
lean_ctor_set(x_712, 3, x_702);
lean_ctor_set(x_712, 4, x_703);
lean_ctor_set(x_712, 5, x_704);
lean_ctor_set(x_712, 6, x_705);
lean_ctor_set(x_712, 7, x_706);
lean_ctor_set(x_712, 8, x_707);
lean_ctor_set(x_712, 9, x_708);
lean_ctor_set(x_712, 10, x_709);
lean_ctor_set(x_712, 11, x_710);
x_713 = lean_st_ref_set(x_3, x_712, x_693);
x_714 = lean_ctor_get(x_713, 1);
lean_inc(x_714);
lean_dec(x_713);
x_675 = x_689;
x_676 = x_714;
goto block_683;
}
}
else
{
uint8_t x_715; 
lean_dec(x_673);
lean_dec(x_671);
lean_dec(x_670);
lean_dec(x_1);
x_715 = !lean_is_exclusive(x_688);
if (x_715 == 0)
{
return x_688;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_688, 0);
x_717 = lean_ctor_get(x_688, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_688);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
}
else
{
lean_object* x_719; 
lean_dec(x_670);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_719 = lean_ctor_get(x_687, 0);
lean_inc(x_719);
lean_dec(x_687);
x_675 = x_719;
x_676 = x_685;
goto block_683;
}
}
}
block_770:
{
lean_object* x_736; lean_object* x_737; 
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_736, x_669);
lean_dec(x_736);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_669);
x_738 = l_Lean_Meta_Closure_collectExprAux(x_669, x_2, x_3, x_4, x_5, x_6, x_7, x_735);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint8_t x_744; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
lean_dec(x_738);
x_741 = lean_st_ref_take(x_3, x_740);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = !lean_is_exclusive(x_742);
if (x_744 == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_745 = lean_ctor_get(x_742, 1);
lean_inc(x_739);
x_746 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_745, x_669, x_739);
lean_ctor_set(x_742, 1, x_746);
x_747 = lean_st_ref_set(x_3, x_742, x_743);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
lean_dec(x_747);
x_673 = x_739;
x_674 = x_748;
goto block_733;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_749 = lean_ctor_get(x_742, 0);
x_750 = lean_ctor_get(x_742, 1);
x_751 = lean_ctor_get(x_742, 2);
x_752 = lean_ctor_get(x_742, 3);
x_753 = lean_ctor_get(x_742, 4);
x_754 = lean_ctor_get(x_742, 5);
x_755 = lean_ctor_get(x_742, 6);
x_756 = lean_ctor_get(x_742, 7);
x_757 = lean_ctor_get(x_742, 8);
x_758 = lean_ctor_get(x_742, 9);
x_759 = lean_ctor_get(x_742, 10);
x_760 = lean_ctor_get(x_742, 11);
lean_inc(x_760);
lean_inc(x_759);
lean_inc(x_758);
lean_inc(x_757);
lean_inc(x_756);
lean_inc(x_755);
lean_inc(x_754);
lean_inc(x_753);
lean_inc(x_752);
lean_inc(x_751);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_742);
lean_inc(x_739);
x_761 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_750, x_669, x_739);
x_762 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_762, 0, x_749);
lean_ctor_set(x_762, 1, x_761);
lean_ctor_set(x_762, 2, x_751);
lean_ctor_set(x_762, 3, x_752);
lean_ctor_set(x_762, 4, x_753);
lean_ctor_set(x_762, 5, x_754);
lean_ctor_set(x_762, 6, x_755);
lean_ctor_set(x_762, 7, x_756);
lean_ctor_set(x_762, 8, x_757);
lean_ctor_set(x_762, 9, x_758);
lean_ctor_set(x_762, 10, x_759);
lean_ctor_set(x_762, 11, x_760);
x_763 = lean_st_ref_set(x_3, x_762, x_743);
x_764 = lean_ctor_get(x_763, 1);
lean_inc(x_764);
lean_dec(x_763);
x_673 = x_739;
x_674 = x_764;
goto block_733;
}
}
else
{
uint8_t x_765; 
lean_dec(x_671);
lean_dec(x_670);
lean_dec(x_669);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_765 = !lean_is_exclusive(x_738);
if (x_765 == 0)
{
return x_738;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_738, 0);
x_767 = lean_ctor_get(x_738, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_738);
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
return x_768;
}
}
}
else
{
lean_object* x_769; 
lean_dec(x_669);
x_769 = lean_ctor_get(x_737, 0);
lean_inc(x_769);
lean_dec(x_737);
x_673 = x_769;
x_674 = x_735;
goto block_733;
}
}
}
block_820:
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
x_787 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_786, x_668);
lean_dec(x_786);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_668);
x_788 = l_Lean_Meta_Closure_collectExprAux(x_668, x_2, x_3, x_4, x_5, x_6, x_7, x_785);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; uint8_t x_794; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec(x_788);
x_791 = lean_st_ref_take(x_3, x_790);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
x_794 = !lean_is_exclusive(x_792);
if (x_794 == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_795 = lean_ctor_get(x_792, 1);
lean_inc(x_789);
x_796 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_795, x_668, x_789);
lean_ctor_set(x_792, 1, x_796);
x_797 = lean_st_ref_set(x_3, x_792, x_793);
x_798 = lean_ctor_get(x_797, 1);
lean_inc(x_798);
lean_dec(x_797);
x_671 = x_789;
x_672 = x_798;
goto block_783;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_799 = lean_ctor_get(x_792, 0);
x_800 = lean_ctor_get(x_792, 1);
x_801 = lean_ctor_get(x_792, 2);
x_802 = lean_ctor_get(x_792, 3);
x_803 = lean_ctor_get(x_792, 4);
x_804 = lean_ctor_get(x_792, 5);
x_805 = lean_ctor_get(x_792, 6);
x_806 = lean_ctor_get(x_792, 7);
x_807 = lean_ctor_get(x_792, 8);
x_808 = lean_ctor_get(x_792, 9);
x_809 = lean_ctor_get(x_792, 10);
x_810 = lean_ctor_get(x_792, 11);
lean_inc(x_810);
lean_inc(x_809);
lean_inc(x_808);
lean_inc(x_807);
lean_inc(x_806);
lean_inc(x_805);
lean_inc(x_804);
lean_inc(x_803);
lean_inc(x_802);
lean_inc(x_801);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_792);
lean_inc(x_789);
x_811 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_800, x_668, x_789);
x_812 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_812, 0, x_799);
lean_ctor_set(x_812, 1, x_811);
lean_ctor_set(x_812, 2, x_801);
lean_ctor_set(x_812, 3, x_802);
lean_ctor_set(x_812, 4, x_803);
lean_ctor_set(x_812, 5, x_804);
lean_ctor_set(x_812, 6, x_805);
lean_ctor_set(x_812, 7, x_806);
lean_ctor_set(x_812, 8, x_807);
lean_ctor_set(x_812, 9, x_808);
lean_ctor_set(x_812, 10, x_809);
lean_ctor_set(x_812, 11, x_810);
x_813 = lean_st_ref_set(x_3, x_812, x_793);
x_814 = lean_ctor_get(x_813, 1);
lean_inc(x_814);
lean_dec(x_813);
x_671 = x_789;
x_672 = x_814;
goto block_783;
}
}
else
{
uint8_t x_815; 
lean_dec(x_670);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_815 = !lean_is_exclusive(x_788);
if (x_815 == 0)
{
return x_788;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = lean_ctor_get(x_788, 0);
x_817 = lean_ctor_get(x_788, 1);
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_788);
x_818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set(x_818, 1, x_817);
return x_818;
}
}
}
else
{
lean_object* x_819; 
lean_dec(x_668);
x_819 = lean_ctor_get(x_787, 0);
lean_inc(x_819);
lean_dec(x_787);
x_671 = x_819;
x_672 = x_785;
goto block_783;
}
}
}
case 10:
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_871; 
x_833 = lean_ctor_get(x_1, 1);
lean_inc(x_833);
x_871 = l_Lean_Expr_hasLevelParam(x_833);
if (x_871 == 0)
{
uint8_t x_872; 
x_872 = l_Lean_Expr_hasFVar(x_833);
if (x_872 == 0)
{
uint8_t x_873; 
x_873 = l_Lean_Expr_hasMVar(x_833);
if (x_873 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_833;
x_10 = x_8;
goto block_17;
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
x_834 = x_875;
x_835 = x_876;
goto block_870;
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
x_834 = x_878;
x_835 = x_879;
goto block_870;
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_880 = lean_st_ref_get(x_3, x_8);
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
x_834 = x_881;
x_835 = x_882;
goto block_870;
}
block_870:
{
lean_object* x_836; lean_object* x_837; 
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
lean_dec(x_834);
x_837 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_836, x_833);
lean_dec(x_836);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; 
lean_inc(x_833);
x_838 = l_Lean_Meta_Closure_collectExprAux(x_833, x_2, x_3, x_4, x_5, x_6, x_7, x_835);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; 
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
lean_dec(x_838);
x_841 = lean_st_ref_take(x_3, x_840);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
x_844 = !lean_is_exclusive(x_842);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_845 = lean_ctor_get(x_842, 1);
lean_inc(x_839);
x_846 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_845, x_833, x_839);
lean_ctor_set(x_842, 1, x_846);
x_847 = lean_st_ref_set(x_3, x_842, x_843);
x_848 = lean_ctor_get(x_847, 1);
lean_inc(x_848);
lean_dec(x_847);
x_9 = x_839;
x_10 = x_848;
goto block_17;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_849 = lean_ctor_get(x_842, 0);
x_850 = lean_ctor_get(x_842, 1);
x_851 = lean_ctor_get(x_842, 2);
x_852 = lean_ctor_get(x_842, 3);
x_853 = lean_ctor_get(x_842, 4);
x_854 = lean_ctor_get(x_842, 5);
x_855 = lean_ctor_get(x_842, 6);
x_856 = lean_ctor_get(x_842, 7);
x_857 = lean_ctor_get(x_842, 8);
x_858 = lean_ctor_get(x_842, 9);
x_859 = lean_ctor_get(x_842, 10);
x_860 = lean_ctor_get(x_842, 11);
lean_inc(x_860);
lean_inc(x_859);
lean_inc(x_858);
lean_inc(x_857);
lean_inc(x_856);
lean_inc(x_855);
lean_inc(x_854);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_842);
lean_inc(x_839);
x_861 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_850, x_833, x_839);
x_862 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_862, 0, x_849);
lean_ctor_set(x_862, 1, x_861);
lean_ctor_set(x_862, 2, x_851);
lean_ctor_set(x_862, 3, x_852);
lean_ctor_set(x_862, 4, x_853);
lean_ctor_set(x_862, 5, x_854);
lean_ctor_set(x_862, 6, x_855);
lean_ctor_set(x_862, 7, x_856);
lean_ctor_set(x_862, 8, x_857);
lean_ctor_set(x_862, 9, x_858);
lean_ctor_set(x_862, 10, x_859);
lean_ctor_set(x_862, 11, x_860);
x_863 = lean_st_ref_set(x_3, x_862, x_843);
x_864 = lean_ctor_get(x_863, 1);
lean_inc(x_864);
lean_dec(x_863);
x_9 = x_839;
x_10 = x_864;
goto block_17;
}
}
else
{
uint8_t x_865; 
lean_dec(x_833);
lean_dec(x_1);
x_865 = !lean_is_exclusive(x_838);
if (x_865 == 0)
{
return x_838;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_866 = lean_ctor_get(x_838, 0);
x_867 = lean_ctor_get(x_838, 1);
lean_inc(x_867);
lean_inc(x_866);
lean_dec(x_838);
x_868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_868, 0, x_866);
lean_ctor_set(x_868, 1, x_867);
return x_868;
}
}
}
else
{
lean_object* x_869; 
lean_dec(x_833);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_869 = lean_ctor_get(x_837, 0);
lean_inc(x_869);
lean_dec(x_837);
x_9 = x_869;
x_10 = x_835;
goto block_17;
}
}
}
case 11:
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_921; 
x_883 = lean_ctor_get(x_1, 2);
lean_inc(x_883);
x_921 = l_Lean_Expr_hasLevelParam(x_883);
if (x_921 == 0)
{
uint8_t x_922; 
x_922 = l_Lean_Expr_hasFVar(x_883);
if (x_922 == 0)
{
uint8_t x_923; 
x_923 = l_Lean_Expr_hasMVar(x_883);
if (x_923 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = x_883;
x_19 = x_8;
goto block_26;
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
x_884 = x_925;
x_885 = x_926;
goto block_920;
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
x_884 = x_928;
x_885 = x_929;
goto block_920;
}
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_st_ref_get(x_3, x_8);
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
x_884 = x_931;
x_885 = x_932;
goto block_920;
}
block_920:
{
lean_object* x_886; lean_object* x_887; 
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_886, x_883);
lean_dec(x_886);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; 
lean_inc(x_883);
x_888 = l_Lean_Meta_Closure_collectExprAux(x_883, x_2, x_3, x_4, x_5, x_6, x_7, x_885);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; uint8_t x_894; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
lean_dec(x_888);
x_891 = lean_st_ref_take(x_3, x_890);
x_892 = lean_ctor_get(x_891, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_891, 1);
lean_inc(x_893);
lean_dec(x_891);
x_894 = !lean_is_exclusive(x_892);
if (x_894 == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_895 = lean_ctor_get(x_892, 1);
lean_inc(x_889);
x_896 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_895, x_883, x_889);
lean_ctor_set(x_892, 1, x_896);
x_897 = lean_st_ref_set(x_3, x_892, x_893);
x_898 = lean_ctor_get(x_897, 1);
lean_inc(x_898);
lean_dec(x_897);
x_18 = x_889;
x_19 = x_898;
goto block_26;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_899 = lean_ctor_get(x_892, 0);
x_900 = lean_ctor_get(x_892, 1);
x_901 = lean_ctor_get(x_892, 2);
x_902 = lean_ctor_get(x_892, 3);
x_903 = lean_ctor_get(x_892, 4);
x_904 = lean_ctor_get(x_892, 5);
x_905 = lean_ctor_get(x_892, 6);
x_906 = lean_ctor_get(x_892, 7);
x_907 = lean_ctor_get(x_892, 8);
x_908 = lean_ctor_get(x_892, 9);
x_909 = lean_ctor_get(x_892, 10);
x_910 = lean_ctor_get(x_892, 11);
lean_inc(x_910);
lean_inc(x_909);
lean_inc(x_908);
lean_inc(x_907);
lean_inc(x_906);
lean_inc(x_905);
lean_inc(x_904);
lean_inc(x_903);
lean_inc(x_902);
lean_inc(x_901);
lean_inc(x_900);
lean_inc(x_899);
lean_dec(x_892);
lean_inc(x_889);
x_911 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_900, x_883, x_889);
x_912 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_912, 0, x_899);
lean_ctor_set(x_912, 1, x_911);
lean_ctor_set(x_912, 2, x_901);
lean_ctor_set(x_912, 3, x_902);
lean_ctor_set(x_912, 4, x_903);
lean_ctor_set(x_912, 5, x_904);
lean_ctor_set(x_912, 6, x_905);
lean_ctor_set(x_912, 7, x_906);
lean_ctor_set(x_912, 8, x_907);
lean_ctor_set(x_912, 9, x_908);
lean_ctor_set(x_912, 10, x_909);
lean_ctor_set(x_912, 11, x_910);
x_913 = lean_st_ref_set(x_3, x_912, x_893);
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
lean_dec(x_913);
x_18 = x_889;
x_19 = x_914;
goto block_26;
}
}
else
{
uint8_t x_915; 
lean_dec(x_883);
lean_dec(x_1);
x_915 = !lean_is_exclusive(x_888);
if (x_915 == 0)
{
return x_888;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_888, 0);
x_917 = lean_ctor_get(x_888, 1);
lean_inc(x_917);
lean_inc(x_916);
lean_dec(x_888);
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
return x_918;
}
}
}
else
{
lean_object* x_919; 
lean_dec(x_883);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_919 = lean_ctor_get(x_887, 0);
lean_inc(x_919);
lean_dec(x_887);
x_18 = x_919;
x_19 = x_885;
goto block_26;
}
}
}
default: 
{
lean_object* x_933; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_933 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_933, 0, x_1);
lean_ctor_set(x_933, 1, x_8);
return x_933;
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
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___main___at_Lean_Meta_Closure_collectExprAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_17 = l_Lean_Meta_Closure_collectExprAux(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
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
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1___rarg), 2, 0);
return x_2;
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
x_22 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_21, x_20, x_19);
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
x_46 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_45, x_44, x_43);
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
x_79 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_78, x_77, x_76);
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
lean_object* l_Lean_Meta_Closure_process_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_17 = lean_box(x_16);
x_18 = lean_apply_6(x_3, x_11, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Meta_Closure_process_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_process_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Closure_process_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_Closure_process_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_process_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Meta_Closure_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_20 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_17);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_154; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_ctor_get(x_21, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_21, 4);
lean_inc(x_39);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 x_40 = x_21;
} else {
 lean_dec_ref(x_21);
 x_40 = lean_box(0);
}
x_41 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg(x_4, x_5, x_6, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_154 = l_Lean_NameSet_contains(x_42, x_18);
lean_dec(x_42);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = 1;
x_44 = x_155;
goto block_153;
}
else
{
uint8_t x_156; 
x_156 = 0;
x_44 = x_156;
goto block_153;
}
block_153:
{
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = l_Lean_Meta_Closure_collectExpr(x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Meta_Closure_collectExpr(x_39, x_1, x_2, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_take(x_2, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_55 = lean_ctor_get(x_52, 7);
x_56 = lean_unsigned_to_nat(0u);
x_57 = 0;
lean_inc(x_49);
lean_inc(x_19);
if (lean_is_scalar(x_40)) {
 x_58 = lean_alloc_ctor(1, 5, 1);
} else {
 x_58 = x_40;
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_19);
lean_ctor_set(x_58, 2, x_37);
lean_ctor_set(x_58, 3, x_46);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_57);
x_59 = lean_array_push(x_55, x_58);
lean_ctor_set(x_52, 7, x_59);
x_60 = lean_st_ref_set(x_2, x_52, x_53);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_st_ref_take(x_2, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_63, 5);
x_67 = x_66;
x_68 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2(x_19, x_49, x_56, x_67);
lean_dec(x_49);
x_69 = x_68;
lean_ctor_set(x_63, 5, x_69);
x_70 = lean_st_ref_set(x_2, x_63, x_64);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_7 = x_71;
goto _start;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_73 = lean_ctor_get(x_63, 0);
x_74 = lean_ctor_get(x_63, 1);
x_75 = lean_ctor_get(x_63, 2);
x_76 = lean_ctor_get(x_63, 3);
x_77 = lean_ctor_get(x_63, 4);
x_78 = lean_ctor_get(x_63, 5);
x_79 = lean_ctor_get(x_63, 6);
x_80 = lean_ctor_get(x_63, 7);
x_81 = lean_ctor_get(x_63, 8);
x_82 = lean_ctor_get(x_63, 9);
x_83 = lean_ctor_get(x_63, 10);
x_84 = lean_ctor_get(x_63, 11);
lean_inc(x_84);
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
lean_dec(x_63);
x_85 = x_78;
x_86 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2(x_19, x_49, x_56, x_85);
lean_dec(x_49);
x_87 = x_86;
x_88 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_74);
lean_ctor_set(x_88, 2, x_75);
lean_ctor_set(x_88, 3, x_76);
lean_ctor_set(x_88, 4, x_77);
lean_ctor_set(x_88, 5, x_87);
lean_ctor_set(x_88, 6, x_79);
lean_ctor_set(x_88, 7, x_80);
lean_ctor_set(x_88, 8, x_81);
lean_ctor_set(x_88, 9, x_82);
lean_ctor_set(x_88, 10, x_83);
lean_ctor_set(x_88, 11, x_84);
x_89 = lean_st_ref_set(x_2, x_88, x_64);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_7 = x_90;
goto _start;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_92 = lean_ctor_get(x_52, 0);
x_93 = lean_ctor_get(x_52, 1);
x_94 = lean_ctor_get(x_52, 2);
x_95 = lean_ctor_get(x_52, 3);
x_96 = lean_ctor_get(x_52, 4);
x_97 = lean_ctor_get(x_52, 5);
x_98 = lean_ctor_get(x_52, 6);
x_99 = lean_ctor_get(x_52, 7);
x_100 = lean_ctor_get(x_52, 8);
x_101 = lean_ctor_get(x_52, 9);
x_102 = lean_ctor_get(x_52, 10);
x_103 = lean_ctor_get(x_52, 11);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_52);
x_104 = lean_unsigned_to_nat(0u);
x_105 = 0;
lean_inc(x_49);
lean_inc(x_19);
if (lean_is_scalar(x_40)) {
 x_106 = lean_alloc_ctor(1, 5, 1);
} else {
 x_106 = x_40;
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_19);
lean_ctor_set(x_106, 2, x_37);
lean_ctor_set(x_106, 3, x_46);
lean_ctor_set(x_106, 4, x_49);
lean_ctor_set_uint8(x_106, sizeof(void*)*5, x_105);
x_107 = lean_array_push(x_99, x_106);
x_108 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_108, 0, x_92);
lean_ctor_set(x_108, 1, x_93);
lean_ctor_set(x_108, 2, x_94);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
lean_ctor_set(x_108, 5, x_97);
lean_ctor_set(x_108, 6, x_98);
lean_ctor_set(x_108, 7, x_107);
lean_ctor_set(x_108, 8, x_100);
lean_ctor_set(x_108, 9, x_101);
lean_ctor_set(x_108, 10, x_102);
lean_ctor_set(x_108, 11, x_103);
x_109 = lean_st_ref_set(x_2, x_108, x_53);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_take(x_2, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 5);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 6);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 7);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 8);
lean_inc(x_122);
x_123 = lean_ctor_get(x_112, 9);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 10);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 11);
lean_inc(x_125);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 lean_ctor_release(x_112, 6);
 lean_ctor_release(x_112, 7);
 lean_ctor_release(x_112, 8);
 lean_ctor_release(x_112, 9);
 lean_ctor_release(x_112, 10);
 lean_ctor_release(x_112, 11);
 x_126 = x_112;
} else {
 lean_dec_ref(x_112);
 x_126 = lean_box(0);
}
x_127 = x_119;
x_128 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2(x_19, x_49, x_104, x_127);
lean_dec(x_49);
x_129 = x_128;
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 12, 0);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_114);
lean_ctor_set(x_130, 1, x_115);
lean_ctor_set(x_130, 2, x_116);
lean_ctor_set(x_130, 3, x_117);
lean_ctor_set(x_130, 4, x_118);
lean_ctor_set(x_130, 5, x_129);
lean_ctor_set(x_130, 6, x_120);
lean_ctor_set(x_130, 7, x_121);
lean_ctor_set(x_130, 8, x_122);
lean_ctor_set(x_130, 9, x_123);
lean_ctor_set(x_130, 10, x_124);
lean_ctor_set(x_130, 11, x_125);
x_131 = lean_st_ref_set(x_2, x_130, x_113);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_7 = x_132;
goto _start;
}
}
else
{
uint8_t x_134; 
lean_dec(x_46);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = !lean_is_exclusive(x_48);
if (x_134 == 0)
{
return x_48;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_48, 0);
x_136 = lean_ctor_get(x_48, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_48);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = !lean_is_exclusive(x_45);
if (x_138 == 0)
{
return x_45;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_45, 0);
x_140 = lean_ctor_get(x_45, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_45);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; lean_object* x_143; 
lean_dec(x_40);
lean_dec(x_39);
x_142 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_37, x_38, x_142, x_1, x_2, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = l_Lean_mkFVar(x_18);
x_146 = l_Lean_Meta_Closure_pushFVarArg(x_145, x_1, x_2, x_3, x_4, x_5, x_6, x_144);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_7 = x_147;
goto _start;
}
else
{
uint8_t x_149; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_143);
if (x_149 == 0)
{
return x_143;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_143, 0);
x_151 = lean_ctor_get(x_143, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_143);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_20);
if (x_157 == 0)
{
return x_20;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_20, 0);
x_159 = lean_ctor_get(x_20, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_20);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_Meta_Closure_process___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_process(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_Closure_mkBinding_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_17 = lean_box(x_16);
x_18 = lean_apply_6(x_3, x_11, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Meta_Closure_mkBinding_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding_match__1___rarg), 3, 0);
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
x_23 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_22);
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
x_57 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_56);
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
x_93 = l_Lean_Meta_Closure_process(x_3, x_4, x_86, x_6, x_7, x_8, x_92);
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
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkValueTypeClosure_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_HashMap_inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_2);
lean_ctor_set(x_4, 8, x_3);
lean_ctor_set(x_4, 9, x_2);
lean_ctor_set(x_4, 10, x_2);
lean_ctor_set(x_4, 11, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
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
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Lean_KernelException_toMessageData(x_1, x_7);
x_9 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(x_12, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(x_13, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__4(x_1, x_2, x_3, x_4, x_5, x_8);
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
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatEntry___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint32_t x_24; uint32_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
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
x_28 = lean_st_ref_get(x_8, x_15);
if (x_27 == 0)
{
uint8_t x_85; 
lean_inc(x_21);
x_85 = l_Lean_Environment_hasUnsafe(x_16, x_21);
x_29 = x_85;
goto block_84;
}
else
{
uint8_t x_86; 
lean_dec(x_16);
x_86 = 1;
x_29 = x_86;
goto block_84;
}
block_84:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_55; lean_object* x_56; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_inc(x_21);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_73 = lean_ctor_get(x_28, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 3);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get_uint8(x_74, sizeof(void*)*1);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_28, 1);
lean_inc(x_76);
lean_dec(x_28);
x_77 = 0;
x_55 = x_77;
x_56 = x_76;
goto block_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_28, 1);
lean_inc(x_78);
lean_dec(x_28);
x_79 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_80 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_79, x_5, x_6, x_7, x_8, x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_55 = x_83;
x_56 = x_82;
goto block_72;
}
block_54:
{
lean_object* x_33; 
x_33 = l_Lean_addAndCompile___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(x_31, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_11, 3);
lean_inc(x_36);
x_37 = l_Array_toList___rarg(x_36);
lean_dec(x_36);
x_38 = l_Lean_mkConst(x_1, x_37);
x_39 = lean_ctor_get(x_11, 4);
lean_inc(x_39);
lean_dec(x_11);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_39, x_39, x_40, x_38);
lean_dec(x_39);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_ctor_get(x_11, 3);
lean_inc(x_43);
x_44 = l_Array_toList___rarg(x_43);
lean_dec(x_43);
x_45 = l_Lean_mkConst(x_1, x_44);
x_46 = lean_ctor_get(x_11, 4);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_46, x_46, x_47, x_45);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
return x_33;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_33, 0);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_33);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
block_72:
{
if (x_55 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
x_32 = x_56;
goto block_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_1);
x_57 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_57, 0, x_1);
x_58 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_19);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_21);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_58);
x_69 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_70 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_69, x_68, x_5, x_6, x_7, x_8, x_56);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_32 = x_71;
goto block_54;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_10);
if (x_87 == 0)
{
return x_10;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_10, 0);
x_89 = lean_ctor_get(x_10, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_10);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_addAndCompile___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addAndCompile___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_5 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
x_25 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_4, x_24, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEq___rarg___lambda__2___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_isLevelDefEq___rarg___closed__2;
x_2 = l_Lean_Meta_mkAuxDefinition___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed), 10, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_6);
x_8 = l_Lean_Meta_mkAuxDefinition___rarg___closed__2;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_box(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinition___rarg___lambda__2___boxed), 10, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
return x_13;
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
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkAuxDefinition___rarg___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
uint8_t x_10; lean_object* x_11; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_st_ref_get(x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = 0;
x_10 = x_35;
x_11 = x_34;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_38 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_37, x_5, x_6, x_7, x_8, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_10 = x_41;
x_11 = x_40;
goto block_29;
}
block_29:
{
if (x_10 == 0)
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_2);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_3);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
x_25 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_26 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_25, x_24, x_5, x_6, x_7, x_8, x_11);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_28;
}
}
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
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
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
l_Lean_Meta_Closure_State_visitedLevel___default___closed__1 = _init_l_Lean_Meta_Closure_State_visitedLevel___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedLevel___default___closed__1);
l_Lean_Meta_Closure_State_visitedLevel___default = _init_l_Lean_Meta_Closure_State_visitedLevel___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedLevel___default);
l_Lean_Meta_Closure_State_visitedExpr___default___closed__1 = _init_l_Lean_Meta_Closure_State_visitedExpr___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedExpr___default___closed__1);
l_Lean_Meta_Closure_State_visitedExpr___default = _init_l_Lean_Meta_Closure_State_visitedExpr___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_visitedExpr___default);
l_Lean_Meta_Closure_State_levelParams___default = _init_l_Lean_Meta_Closure_State_levelParams___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_levelParams___default);
l_Lean_Meta_Closure_State_nextLevelIdx___default = _init_l_Lean_Meta_Closure_State_nextLevelIdx___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_nextLevelIdx___default);
l_Lean_Meta_Closure_State_levelArgs___default = _init_l_Lean_Meta_Closure_State_levelArgs___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_levelArgs___default);
l_Lean_Meta_Closure_State_newLocalDecls___default = _init_l_Lean_Meta_Closure_State_newLocalDecls___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_newLocalDecls___default);
l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default = _init_l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default);
l_Lean_Meta_Closure_State_newLetDecls___default = _init_l_Lean_Meta_Closure_State_newLetDecls___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_newLetDecls___default);
l_Lean_Meta_Closure_State_nextExprIdx___default = _init_l_Lean_Meta_Closure_State_nextExprIdx___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_nextExprIdx___default);
l_Lean_Meta_Closure_State_exprMVarArgs___default = _init_l_Lean_Meta_Closure_State_exprMVarArgs___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_exprMVarArgs___default);
l_Lean_Meta_Closure_State_exprFVarArgs___default = _init_l_Lean_Meta_Closure_State_exprFVarArgs___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_exprFVarArgs___default);
l_Lean_Meta_Closure_State_toProcess___default = _init_l_Lean_Meta_Closure_State_toProcess___default();
lean_mark_persistent(l_Lean_Meta_Closure_State_toProcess___default);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__1 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1 = _init_l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1);
l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2 = _init_l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2);
l_Lean_Meta_mkAuxDefinition___rarg___closed__1 = _init_l_Lean_Meta_mkAuxDefinition___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___rarg___closed__1);
l_Lean_Meta_mkAuxDefinition___rarg___closed__2 = _init_l_Lean_Meta_mkAuxDefinition___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
