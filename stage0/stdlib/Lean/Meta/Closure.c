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
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Level_LevelToFormat_toResult___closed__3;
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLocalDecls___default;
lean_object* l_Lean_Meta_Closure_visitExpr_match__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateApp_x21___closed__2;
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel_match__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedExpr___default___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_visitedLevel___default;
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateSucc_x21___closed__3;
lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkBinding_match__1(lean_object*);
extern lean_object* l_Lean_Level_updateMax_x21___closed__3;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitExpr___spec__7(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitExpr___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Expr_updateProj_x21___closed__3;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_exprMVarArgs___default;
lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__4;
lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_levelParams___default;
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_Meta_Closure_mkBinding_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__3;
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_toProcess___default;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Expr_updateMData_x21___closed__3;
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2(lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__2(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___closed__1;
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__2;
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLetDecls___default;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__1(lean_object*);
extern lean_object* l_termIf_____x3a__Then__Else_____closed__7;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__2;
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_termIfLet___x3a_x3d__Then__Else_____closed__9;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLevel;
lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___closed__2;
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1() {
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
static lean_object* _init_l_Lean_Meta_Closure_instInhabitedToProcessElement() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
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
lean_object* x_10; lean_object* x_11; uint8_t x_55; 
x_55 = l_Lean_Level_hasMVar(x_2);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Level_hasParam(x_2);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_9);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_st_ref_get(x_8, x_9);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_st_ref_get(x_4, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_10 = x_61;
x_11 = x_62;
goto block_54;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_st_ref_get(x_8, x_9);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_4, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_10 = x_66;
x_11 = x_67;
goto block_54;
}
block_54:
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
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_14 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
lean_dec(x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_15);
x_24 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_23, x_2, x_15);
lean_ctor_set(x_20, 0, x_24);
x_25 = lean_st_ref_set(x_4, x_20, x_21);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_15);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
x_32 = lean_ctor_get(x_20, 2);
x_33 = lean_ctor_get(x_20, 3);
x_34 = lean_ctor_get(x_20, 4);
x_35 = lean_ctor_get(x_20, 5);
x_36 = lean_ctor_get(x_20, 6);
x_37 = lean_ctor_get(x_20, 7);
x_38 = lean_ctor_get(x_20, 8);
x_39 = lean_ctor_get(x_20, 9);
x_40 = lean_ctor_get(x_20, 10);
x_41 = lean_ctor_get(x_20, 11);
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
lean_dec(x_20);
lean_inc(x_15);
x_42 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_30, x_2, x_15);
x_43 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_35);
lean_ctor_set(x_43, 6, x_36);
lean_ctor_set(x_43, 7, x_37);
lean_ctor_set(x_43, 8, x_38);
lean_ctor_set(x_43, 9, x_39);
lean_ctor_set(x_43, 10, x_40);
lean_ctor_set(x_43, 11, x_41);
x_44 = lean_st_ref_set(x_4, x_43, x_21);
lean_dec(x_4);
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
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
lean_dec(x_13);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_11);
return x_53;
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
lean_object* x_10; lean_object* x_11; uint8_t x_55; 
x_55 = l_Lean_Expr_hasLevelParam(x_2);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_hasFVar(x_2);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Expr_hasMVar(x_2);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_9);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_st_ref_get(x_8, x_9);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_4, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_10 = x_62;
x_11 = x_63;
goto block_54;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_st_ref_get(x_8, x_9);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_get(x_4, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_10 = x_67;
x_11 = x_68;
goto block_54;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_st_ref_get(x_8, x_9);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_st_ref_get(x_4, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_10 = x_72;
x_11 = x_73;
goto block_54;
}
block_54:
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
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_14 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
lean_dec(x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_15);
x_24 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_23, x_2, x_15);
lean_ctor_set(x_20, 1, x_24);
x_25 = lean_st_ref_set(x_4, x_20, x_21);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_15);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
x_32 = lean_ctor_get(x_20, 2);
x_33 = lean_ctor_get(x_20, 3);
x_34 = lean_ctor_get(x_20, 4);
x_35 = lean_ctor_get(x_20, 5);
x_36 = lean_ctor_get(x_20, 6);
x_37 = lean_ctor_get(x_20, 7);
x_38 = lean_ctor_get(x_20, 8);
x_39 = lean_ctor_get(x_20, 9);
x_40 = lean_ctor_get(x_20, 10);
x_41 = lean_ctor_get(x_20, 11);
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
lean_dec(x_20);
lean_inc(x_15);
x_42 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_31, x_2, x_15);
x_43 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_35);
lean_ctor_set(x_43, 6, x_36);
lean_ctor_set(x_43, 7, x_37);
lean_ctor_set(x_43, 8, x_38);
lean_ctor_set(x_43, 9, x_39);
lean_ctor_set(x_43, 10, x_40);
lean_ctor_set(x_43, 11, x_41);
x_44 = lean_st_ref_set(x_4, x_43, x_21);
lean_dec(x_4);
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
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
lean_dec(x_13);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_11);
return x_53;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Level_LevelToFormat_toResult___closed__3;
x_16 = l_Lean_Name_appendIndexAfter(x_15, x_14);
x_17 = lean_st_ref_get(x_7, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_20, 2);
x_24 = lean_ctor_get(x_20, 3);
x_25 = lean_ctor_get(x_20, 4);
lean_inc(x_16);
x_26 = lean_array_push(x_23, x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_24, x_27);
lean_dec(x_24);
x_29 = lean_array_push(x_25, x_1);
lean_ctor_set(x_20, 4, x_29);
lean_ctor_set(x_20, 3, x_28);
lean_ctor_set(x_20, 2, x_26);
x_30 = lean_st_ref_set(x_3, x_20, x_21);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_mkLevelParam(x_16);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_mkLevelParam(x_16);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
x_39 = lean_ctor_get(x_20, 2);
x_40 = lean_ctor_get(x_20, 3);
x_41 = lean_ctor_get(x_20, 4);
x_42 = lean_ctor_get(x_20, 5);
x_43 = lean_ctor_get(x_20, 6);
x_44 = lean_ctor_get(x_20, 7);
x_45 = lean_ctor_get(x_20, 8);
x_46 = lean_ctor_get(x_20, 9);
x_47 = lean_ctor_get(x_20, 10);
x_48 = lean_ctor_get(x_20, 11);
lean_inc(x_48);
lean_inc(x_47);
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
lean_dec(x_20);
lean_inc(x_16);
x_49 = lean_array_push(x_39, x_16);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_40, x_50);
lean_dec(x_40);
x_52 = lean_array_push(x_41, x_1);
x_53 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_42);
lean_ctor_set(x_53, 6, x_43);
lean_ctor_set(x_53, 7, x_44);
lean_ctor_set(x_53, 8, x_45);
lean_ctor_set(x_53, 9, x_46);
lean_ctor_set(x_53, 10, x_47);
lean_ctor_set(x_53, 11, x_48);
x_54 = lean_st_ref_set(x_3, x_53, x_21);
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
x_57 = l_Lean_mkLevelParam(x_16);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
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
lean_object* x_9; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_81; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_81 = l_Lean_Level_hasMVar(x_39);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Level_hasParam(x_39);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_8);
x_9 = x_83;
goto block_37;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_st_ref_get(x_7, x_8);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_st_ref_get(x_3, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_40 = x_87;
x_41 = x_88;
goto block_80;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_st_ref_get(x_7, x_8);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_st_ref_get(x_3, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_40 = x_92;
x_41 = x_93;
goto block_80;
}
block_80:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_42, x_39);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_inc(x_39);
x_44 = l_Lean_Meta_Closure_collectLevelAux(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_7, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_take(x_3, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_45);
x_54 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_53, x_39, x_45);
lean_ctor_set(x_50, 0, x_54);
x_55 = lean_st_ref_set(x_3, x_50, x_51);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_45);
x_9 = x_55;
goto block_37;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_45);
lean_ctor_set(x_59, 1, x_58);
x_9 = x_59;
goto block_37;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_60 = lean_ctor_get(x_50, 0);
x_61 = lean_ctor_get(x_50, 1);
x_62 = lean_ctor_get(x_50, 2);
x_63 = lean_ctor_get(x_50, 3);
x_64 = lean_ctor_get(x_50, 4);
x_65 = lean_ctor_get(x_50, 5);
x_66 = lean_ctor_get(x_50, 6);
x_67 = lean_ctor_get(x_50, 7);
x_68 = lean_ctor_get(x_50, 8);
x_69 = lean_ctor_get(x_50, 9);
x_70 = lean_ctor_get(x_50, 10);
x_71 = lean_ctor_get(x_50, 11);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_50);
lean_inc(x_45);
x_72 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_60, x_39, x_45);
x_73 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set(x_73, 2, x_62);
lean_ctor_set(x_73, 3, x_63);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_66);
lean_ctor_set(x_73, 7, x_67);
lean_ctor_set(x_73, 8, x_68);
lean_ctor_set(x_73, 9, x_69);
lean_ctor_set(x_73, 10, x_70);
lean_ctor_set(x_73, 11, x_71);
x_74 = lean_st_ref_set(x_3, x_73, x_51);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_45);
lean_ctor_set(x_77, 1, x_75);
x_9 = x_77;
goto block_37;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_39);
x_78 = lean_ctor_get(x_43, 0);
lean_inc(x_78);
lean_dec(x_43);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_41);
x_9 = x_79;
goto block_37;
}
}
}
case 2:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_186; lean_object* x_187; uint8_t x_227; 
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
x_227 = l_Lean_Level_hasMVar(x_94);
if (x_227 == 0)
{
uint8_t x_228; 
x_228 = l_Lean_Level_hasParam(x_94);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_94);
lean_ctor_set(x_229, 1, x_8);
x_96 = x_229;
goto block_185;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_st_ref_get(x_7, x_8);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_st_ref_get(x_3, x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_186 = x_233;
x_187 = x_234;
goto block_226;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_st_ref_get(x_7, x_8);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_st_ref_get(x_3, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_186 = x_238;
x_187 = x_239;
goto block_226;
}
block_185:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_131; lean_object* x_132; uint8_t x_172; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_172 = l_Lean_Level_hasMVar(x_95);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Level_hasParam(x_95);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_99);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_95);
lean_ctor_set(x_174, 1, x_98);
x_100 = x_174;
goto block_130;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_st_ref_get(x_7, x_98);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_st_ref_get(x_3, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_131 = x_178;
x_132 = x_179;
goto block_171;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_st_ref_get(x_7, x_98);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_st_ref_get(x_3, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_131 = x_183;
x_132 = x_184;
goto block_171;
}
block_130:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_1);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 0);
x_104 = lean_level_update_max(x_1, x_97, x_103);
lean_ctor_set(x_100, 0, x_104);
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint64_t x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_100, 0);
x_106 = lean_ctor_get(x_1, 0);
x_107 = lean_ctor_get(x_1, 1);
x_108 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_1);
x_109 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set_uint64(x_109, sizeof(void*)*2, x_108);
x_110 = lean_level_update_max(x_109, x_97, x_105);
lean_ctor_set(x_100, 0, x_110);
return x_100;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_111 = lean_ctor_get(x_100, 0);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_100);
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_116 = x_1;
} else {
 lean_dec_ref(x_1);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(2, 2, 8);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set_uint64(x_117, sizeof(void*)*2, x_115);
x_118 = lean_level_update_max(x_117, x_97, x_111);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_112);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_97);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_100);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_100, 0);
lean_dec(x_121);
x_122 = l_Lean_instInhabitedLevel;
x_123 = l_Lean_Level_updateMax_x21___closed__3;
x_124 = lean_panic_fn(x_122, x_123);
lean_ctor_set(x_100, 0, x_124);
return x_100;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_100, 1);
lean_inc(x_125);
lean_dec(x_100);
x_126 = l_Lean_instInhabitedLevel;
x_127 = l_Lean_Level_updateMax_x21___closed__3;
x_128 = lean_panic_fn(x_126, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
return x_129;
}
}
}
block_171:
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_133, x_95);
lean_dec(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_99);
lean_inc(x_95);
x_135 = l_Lean_Meta_Closure_collectLevelAux(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_132);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_st_ref_get(x_7, x_137);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_st_ref_take(x_3, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = !lean_is_exclusive(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_136);
x_145 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_144, x_95, x_136);
lean_ctor_set(x_141, 0, x_145);
x_146 = lean_st_ref_set(x_3, x_141, x_142);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_146, 0);
lean_dec(x_148);
lean_ctor_set(x_146, 0, x_136);
x_100 = x_146;
goto block_130;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_149);
x_100 = x_150;
goto block_130;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_151 = lean_ctor_get(x_141, 0);
x_152 = lean_ctor_get(x_141, 1);
x_153 = lean_ctor_get(x_141, 2);
x_154 = lean_ctor_get(x_141, 3);
x_155 = lean_ctor_get(x_141, 4);
x_156 = lean_ctor_get(x_141, 5);
x_157 = lean_ctor_get(x_141, 6);
x_158 = lean_ctor_get(x_141, 7);
x_159 = lean_ctor_get(x_141, 8);
x_160 = lean_ctor_get(x_141, 9);
x_161 = lean_ctor_get(x_141, 10);
x_162 = lean_ctor_get(x_141, 11);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_141);
lean_inc(x_136);
x_163 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_151, x_95, x_136);
x_164 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_152);
lean_ctor_set(x_164, 2, x_153);
lean_ctor_set(x_164, 3, x_154);
lean_ctor_set(x_164, 4, x_155);
lean_ctor_set(x_164, 5, x_156);
lean_ctor_set(x_164, 6, x_157);
lean_ctor_set(x_164, 7, x_158);
lean_ctor_set(x_164, 8, x_159);
lean_ctor_set(x_164, 9, x_160);
lean_ctor_set(x_164, 10, x_161);
lean_ctor_set(x_164, 11, x_162);
x_165 = lean_st_ref_set(x_3, x_164, x_142);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_136);
lean_ctor_set(x_168, 1, x_166);
x_100 = x_168;
goto block_130;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_95);
x_169 = lean_ctor_get(x_134, 0);
lean_inc(x_169);
lean_dec(x_134);
if (lean_is_scalar(x_99)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_99;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_132);
x_100 = x_170;
goto block_130;
}
}
}
block_226:
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_188, x_94);
lean_dec(x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
lean_inc(x_94);
x_190 = l_Lean_Meta_Closure_collectLevelAux(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_187);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_st_ref_get(x_7, x_192);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_st_ref_take(x_3, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = !lean_is_exclusive(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_191);
x_200 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_199, x_94, x_191);
lean_ctor_set(x_196, 0, x_200);
x_201 = lean_st_ref_set(x_3, x_196, x_197);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_201, 0);
lean_dec(x_203);
lean_ctor_set(x_201, 0, x_191);
x_96 = x_201;
goto block_185;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_191);
lean_ctor_set(x_205, 1, x_204);
x_96 = x_205;
goto block_185;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_206 = lean_ctor_get(x_196, 0);
x_207 = lean_ctor_get(x_196, 1);
x_208 = lean_ctor_get(x_196, 2);
x_209 = lean_ctor_get(x_196, 3);
x_210 = lean_ctor_get(x_196, 4);
x_211 = lean_ctor_get(x_196, 5);
x_212 = lean_ctor_get(x_196, 6);
x_213 = lean_ctor_get(x_196, 7);
x_214 = lean_ctor_get(x_196, 8);
x_215 = lean_ctor_get(x_196, 9);
x_216 = lean_ctor_get(x_196, 10);
x_217 = lean_ctor_get(x_196, 11);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_196);
lean_inc(x_191);
x_218 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_206, x_94, x_191);
x_219 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_207);
lean_ctor_set(x_219, 2, x_208);
lean_ctor_set(x_219, 3, x_209);
lean_ctor_set(x_219, 4, x_210);
lean_ctor_set(x_219, 5, x_211);
lean_ctor_set(x_219, 6, x_212);
lean_ctor_set(x_219, 7, x_213);
lean_ctor_set(x_219, 8, x_214);
lean_ctor_set(x_219, 9, x_215);
lean_ctor_set(x_219, 10, x_216);
lean_ctor_set(x_219, 11, x_217);
x_220 = lean_st_ref_set(x_3, x_219, x_197);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_222 = x_220;
} else {
 lean_dec_ref(x_220);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_191);
lean_ctor_set(x_223, 1, x_221);
x_96 = x_223;
goto block_185;
}
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_94);
x_224 = lean_ctor_get(x_189, 0);
lean_inc(x_224);
lean_dec(x_189);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_187);
x_96 = x_225;
goto block_185;
}
}
}
case 3:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_332; lean_object* x_333; uint8_t x_373; 
x_240 = lean_ctor_get(x_1, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_1, 1);
lean_inc(x_241);
x_373 = l_Lean_Level_hasMVar(x_240);
if (x_373 == 0)
{
uint8_t x_374; 
x_374 = l_Lean_Level_hasParam(x_240);
if (x_374 == 0)
{
lean_object* x_375; 
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_240);
lean_ctor_set(x_375, 1, x_8);
x_242 = x_375;
goto block_331;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_376 = lean_st_ref_get(x_7, x_8);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
x_378 = lean_st_ref_get(x_3, x_377);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_332 = x_379;
x_333 = x_380;
goto block_372;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_st_ref_get(x_7, x_8);
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
lean_dec(x_381);
x_383 = lean_st_ref_get(x_3, x_382);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_332 = x_384;
x_333 = x_385;
goto block_372;
}
block_331:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_277; lean_object* x_278; uint8_t x_318; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_318 = l_Lean_Level_hasMVar(x_241);
if (x_318 == 0)
{
uint8_t x_319; 
x_319 = l_Lean_Level_hasParam(x_241);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_245);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_241);
lean_ctor_set(x_320, 1, x_244);
x_246 = x_320;
goto block_276;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_321 = lean_st_ref_get(x_7, x_244);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_323 = lean_st_ref_get(x_3, x_322);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_277 = x_324;
x_278 = x_325;
goto block_317;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_326 = lean_st_ref_get(x_7, x_244);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
lean_dec(x_326);
x_328 = lean_st_ref_get(x_3, x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_277 = x_329;
x_278 = x_330;
goto block_317;
}
block_276:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_1);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_246, 0);
x_250 = lean_level_update_imax(x_1, x_243, x_249);
lean_ctor_set(x_246, 0, x_250);
return x_246;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint64_t x_254; lean_object* x_255; lean_object* x_256; 
x_251 = lean_ctor_get(x_246, 0);
x_252 = lean_ctor_get(x_1, 0);
x_253 = lean_ctor_get(x_1, 1);
x_254 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_1);
x_255 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
lean_ctor_set_uint64(x_255, sizeof(void*)*2, x_254);
x_256 = lean_level_update_imax(x_255, x_243, x_251);
lean_ctor_set(x_246, 0, x_256);
return x_246;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint64_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_257 = lean_ctor_get(x_246, 0);
x_258 = lean_ctor_get(x_246, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_246);
x_259 = lean_ctor_get(x_1, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_1, 1);
lean_inc(x_260);
x_261 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_262 = x_1;
} else {
 lean_dec_ref(x_1);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(3, 2, 8);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_259);
lean_ctor_set(x_263, 1, x_260);
lean_ctor_set_uint64(x_263, sizeof(void*)*2, x_261);
x_264 = lean_level_update_imax(x_263, x_243, x_257);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_258);
return x_265;
}
}
else
{
uint8_t x_266; 
lean_dec(x_243);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_246);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_246, 0);
lean_dec(x_267);
x_268 = l_Lean_instInhabitedLevel;
x_269 = l_Lean_Level_updateIMax_x21___closed__3;
x_270 = lean_panic_fn(x_268, x_269);
lean_ctor_set(x_246, 0, x_270);
return x_246;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_271 = lean_ctor_get(x_246, 1);
lean_inc(x_271);
lean_dec(x_246);
x_272 = l_Lean_instInhabitedLevel;
x_273 = l_Lean_Level_updateIMax_x21___closed__3;
x_274 = lean_panic_fn(x_272, x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_271);
return x_275;
}
}
}
block_317:
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_279, x_241);
lean_dec(x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_245);
lean_inc(x_241);
x_281 = l_Lean_Meta_Closure_collectLevelAux(x_241, x_2, x_3, x_4, x_5, x_6, x_7, x_278);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_st_ref_get(x_7, x_283);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
lean_dec(x_284);
x_286 = lean_st_ref_take(x_3, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = !lean_is_exclusive(x_287);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_287, 0);
lean_inc(x_282);
x_291 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_290, x_241, x_282);
lean_ctor_set(x_287, 0, x_291);
x_292 = lean_st_ref_set(x_3, x_287, x_288);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_292, 0);
lean_dec(x_294);
lean_ctor_set(x_292, 0, x_282);
x_246 = x_292;
goto block_276;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_292, 1);
lean_inc(x_295);
lean_dec(x_292);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_282);
lean_ctor_set(x_296, 1, x_295);
x_246 = x_296;
goto block_276;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_297 = lean_ctor_get(x_287, 0);
x_298 = lean_ctor_get(x_287, 1);
x_299 = lean_ctor_get(x_287, 2);
x_300 = lean_ctor_get(x_287, 3);
x_301 = lean_ctor_get(x_287, 4);
x_302 = lean_ctor_get(x_287, 5);
x_303 = lean_ctor_get(x_287, 6);
x_304 = lean_ctor_get(x_287, 7);
x_305 = lean_ctor_get(x_287, 8);
x_306 = lean_ctor_get(x_287, 9);
x_307 = lean_ctor_get(x_287, 10);
x_308 = lean_ctor_get(x_287, 11);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_287);
lean_inc(x_282);
x_309 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_297, x_241, x_282);
x_310 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_298);
lean_ctor_set(x_310, 2, x_299);
lean_ctor_set(x_310, 3, x_300);
lean_ctor_set(x_310, 4, x_301);
lean_ctor_set(x_310, 5, x_302);
lean_ctor_set(x_310, 6, x_303);
lean_ctor_set(x_310, 7, x_304);
lean_ctor_set(x_310, 8, x_305);
lean_ctor_set(x_310, 9, x_306);
lean_ctor_set(x_310, 10, x_307);
lean_ctor_set(x_310, 11, x_308);
x_311 = lean_st_ref_set(x_3, x_310, x_288);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_282);
lean_ctor_set(x_314, 1, x_312);
x_246 = x_314;
goto block_276;
}
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_241);
x_315 = lean_ctor_get(x_280, 0);
lean_inc(x_315);
lean_dec(x_280);
if (lean_is_scalar(x_245)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_245;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_278);
x_246 = x_316;
goto block_276;
}
}
}
block_372:
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
lean_dec(x_332);
x_335 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_334, x_240);
lean_dec(x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
lean_inc(x_240);
x_336 = l_Lean_Meta_Closure_collectLevelAux(x_240, x_2, x_3, x_4, x_5, x_6, x_7, x_333);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_st_ref_get(x_7, x_338);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_341 = lean_st_ref_take(x_3, x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = !lean_is_exclusive(x_342);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_337);
x_346 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_345, x_240, x_337);
lean_ctor_set(x_342, 0, x_346);
x_347 = lean_st_ref_set(x_3, x_342, x_343);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_dec(x_349);
lean_ctor_set(x_347, 0, x_337);
x_242 = x_347;
goto block_331;
}
else
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_337);
lean_ctor_set(x_351, 1, x_350);
x_242 = x_351;
goto block_331;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_352 = lean_ctor_get(x_342, 0);
x_353 = lean_ctor_get(x_342, 1);
x_354 = lean_ctor_get(x_342, 2);
x_355 = lean_ctor_get(x_342, 3);
x_356 = lean_ctor_get(x_342, 4);
x_357 = lean_ctor_get(x_342, 5);
x_358 = lean_ctor_get(x_342, 6);
x_359 = lean_ctor_get(x_342, 7);
x_360 = lean_ctor_get(x_342, 8);
x_361 = lean_ctor_get(x_342, 9);
x_362 = lean_ctor_get(x_342, 10);
x_363 = lean_ctor_get(x_342, 11);
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
lean_inc(x_352);
lean_dec(x_342);
lean_inc(x_337);
x_364 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_352, x_240, x_337);
x_365 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_353);
lean_ctor_set(x_365, 2, x_354);
lean_ctor_set(x_365, 3, x_355);
lean_ctor_set(x_365, 4, x_356);
lean_ctor_set(x_365, 5, x_357);
lean_ctor_set(x_365, 6, x_358);
lean_ctor_set(x_365, 7, x_359);
lean_ctor_set(x_365, 8, x_360);
lean_ctor_set(x_365, 9, x_361);
lean_ctor_set(x_365, 10, x_362);
lean_ctor_set(x_365, 11, x_363);
x_366 = lean_st_ref_set(x_3, x_365, x_343);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_368 = x_366;
} else {
 lean_dec_ref(x_366);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_337);
lean_ctor_set(x_369, 1, x_367);
x_242 = x_369;
goto block_331;
}
}
else
{
lean_object* x_370; lean_object* x_371; 
lean_dec(x_240);
x_370 = lean_ctor_get(x_335, 0);
lean_inc(x_370);
lean_dec(x_335);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_333);
x_242 = x_371;
goto block_331;
}
}
}
default: 
{
lean_object* x_386; 
x_386 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_386;
}
}
block_37:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_level_update_succ(x_1, x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint64(x_17, sizeof(void*)*1, x_16);
x_18 = lean_level_update_succ(x_17, x_14);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_23 = x_1;
} else {
 lean_dec_ref(x_1);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 8);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set_uint64(x_24, sizeof(void*)*1, x_22);
x_25 = lean_level_update_succ(x_24, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_9, 0);
lean_dec(x_28);
x_29 = l_Lean_instInhabitedLevel;
x_30 = l_Lean_Level_updateSucc_x21___closed__3;
x_31 = lean_panic_fn(x_29, x_30);
lean_ctor_set(x_9, 0, x_31);
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_dec(x_9);
x_33 = l_Lean_instInhabitedLevel;
x_34 = l_Lean_Level_updateSucc_x21___closed__3;
x_35 = lean_panic_fn(x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
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
lean_object* x_9; lean_object* x_10; uint8_t x_50; 
x_50 = l_Lean_Level_hasMVar(x_1);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Level_hasParam(x_1);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_8);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_st_ref_get(x_7, x_8);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_3, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_9 = x_56;
x_10 = x_57;
goto block_49;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_st_ref_get(x_7, x_8);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_st_ref_get(x_3, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_9 = x_61;
x_10 = x_62;
goto block_49;
}
block_49:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_7, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_14);
x_23 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_22, x_1, x_14);
lean_ctor_set(x_19, 0, x_23);
x_24 = lean_st_ref_set(x_3, x_19, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_14);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
x_31 = lean_ctor_get(x_19, 2);
x_32 = lean_ctor_get(x_19, 3);
x_33 = lean_ctor_get(x_19, 4);
x_34 = lean_ctor_get(x_19, 5);
x_35 = lean_ctor_get(x_19, 6);
x_36 = lean_ctor_get(x_19, 7);
x_37 = lean_ctor_get(x_19, 8);
x_38 = lean_ctor_get(x_19, 9);
x_39 = lean_ctor_get(x_19, 10);
x_40 = lean_ctor_get(x_19, 11);
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
lean_inc(x_29);
lean_dec(x_19);
lean_inc(x_14);
x_41 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_29, x_1, x_14);
x_42 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set(x_42, 3, x_32);
lean_ctor_set(x_42, 4, x_33);
lean_ctor_set(x_42, 5, x_34);
lean_ctor_set(x_42, 6, x_35);
lean_ctor_set(x_42, 7, x_36);
lean_ctor_set(x_42, 8, x_37);
lean_ctor_set(x_42, 9, x_38);
lean_ctor_set(x_42, 10, x_39);
lean_ctor_set(x_42, 11, x_40);
x_43 = lean_st_ref_set(x_3, x_42, x_20);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
return x_48;
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
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 8);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
x_14 = l_Lean_Name_appendIndexAfter(x_13, x_12);
x_15 = lean_st_ref_get(x_5, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_18, 8);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
lean_ctor_set(x_18, 8, x_23);
x_24 = lean_st_ref_set(x_1, x_18, x_19);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_14);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 3);
x_33 = lean_ctor_get(x_18, 4);
x_34 = lean_ctor_get(x_18, 5);
x_35 = lean_ctor_get(x_18, 6);
x_36 = lean_ctor_get(x_18, 7);
x_37 = lean_ctor_get(x_18, 8);
x_38 = lean_ctor_get(x_18, 9);
x_39 = lean_ctor_get(x_18, 10);
x_40 = lean_ctor_get(x_18, 11);
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
lean_inc(x_29);
lean_dec(x_18);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_37, x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_30);
lean_ctor_set(x_43, 2, x_31);
lean_ctor_set(x_43, 3, x_32);
lean_ctor_set(x_43, 4, x_33);
lean_ctor_set(x_43, 5, x_34);
lean_ctor_set(x_43, 6, x_35);
lean_ctor_set(x_43, 7, x_36);
lean_ctor_set(x_43, 8, x_42);
lean_ctor_set(x_43, 9, x_38);
lean_ctor_set(x_43, 10, x_39);
lean_ctor_set(x_43, 11, x_40);
x_44 = lean_st_ref_set(x_1, x_43, x_19);
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
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_14);
lean_ctor_set(x_47, 1, x_45);
return x_47;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 11);
x_16 = lean_array_push(x_15, x_1);
lean_ctor_set(x_12, 11, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
x_30 = lean_ctor_get(x_12, 6);
x_31 = lean_ctor_get(x_12, 7);
x_32 = lean_ctor_get(x_12, 8);
x_33 = lean_ctor_get(x_12, 9);
x_34 = lean_ctor_get(x_12, 10);
x_35 = lean_ctor_get(x_12, 11);
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
lean_inc(x_24);
lean_dec(x_12);
x_36 = lean_array_push(x_35, x_1);
x_37 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set(x_37, 7, x_31);
lean_ctor_set(x_37, 8, x_32);
lean_ctor_set(x_37, 9, x_33);
lean_ctor_set(x_37, 10, x_34);
lean_ctor_set(x_37, 11, x_36);
x_38 = lean_st_ref_set(x_3, x_37, x_13);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
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
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg___boxed), 2, 0);
return x_6;
}
}
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
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
x_28 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
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
lean_object* x_9; lean_object* x_44; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_81);
x_82 = l_Lean_Meta_getLocalDecl(x_81, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = lean_unbox(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Lean_Meta_Closure_pushToProcess(x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_87);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
x_92 = l_Lean_mkFVar(x_86);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_94 = l_Lean_mkFVar(x_86);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_82);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_82, 0);
x_98 = lean_ctor_get(x_82, 1);
x_99 = l_Lean_LocalDecl_value_x3f(x_97);
lean_dec(x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_free_object(x_82);
x_100 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_81);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Meta_Closure_pushToProcess(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_102);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_dec(x_106);
x_107 = l_Lean_mkFVar(x_101);
lean_ctor_set(x_104, 0, x_107);
return x_104;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_dec(x_104);
x_109 = l_Lean_mkFVar(x_101);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_81);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec(x_99);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_112 = l_Lean_Meta_Closure_preprocess(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_161; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_161 = l_Lean_Expr_hasLevelParam(x_113);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Expr_hasFVar(x_113);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = l_Lean_Expr_hasMVar(x_113);
if (x_163 == 0)
{
lean_dec(x_115);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_82, 1, x_114);
lean_ctor_set(x_82, 0, x_113);
return x_82;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_free_object(x_82);
x_164 = lean_st_ref_get(x_7, x_114);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_st_ref_get(x_3, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_116 = x_167;
x_117 = x_168;
goto block_160;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_82);
x_169 = lean_st_ref_get(x_7, x_114);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_st_ref_get(x_3, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_116 = x_172;
x_117 = x_173;
goto block_160;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_free_object(x_82);
x_174 = lean_st_ref_get(x_7, x_114);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_st_ref_get(x_3, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_116 = x_177;
x_117 = x_178;
goto block_160;
}
block_160:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_118, x_113);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
lean_dec(x_115);
lean_inc(x_7);
lean_inc(x_113);
x_120 = l_Lean_Meta_Closure_collectExprAux(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_st_ref_get(x_7, x_122);
lean_dec(x_7);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_st_ref_take(x_3, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = !lean_is_exclusive(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_121);
x_130 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_129, x_113, x_121);
lean_ctor_set(x_126, 1, x_130);
x_131 = lean_st_ref_set(x_3, x_126, x_127);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 0);
lean_dec(x_133);
lean_ctor_set(x_131, 0, x_121);
return x_131;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_121);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_136 = lean_ctor_get(x_126, 0);
x_137 = lean_ctor_get(x_126, 1);
x_138 = lean_ctor_get(x_126, 2);
x_139 = lean_ctor_get(x_126, 3);
x_140 = lean_ctor_get(x_126, 4);
x_141 = lean_ctor_get(x_126, 5);
x_142 = lean_ctor_get(x_126, 6);
x_143 = lean_ctor_get(x_126, 7);
x_144 = lean_ctor_get(x_126, 8);
x_145 = lean_ctor_get(x_126, 9);
x_146 = lean_ctor_get(x_126, 10);
x_147 = lean_ctor_get(x_126, 11);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_126);
lean_inc(x_121);
x_148 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_137, x_113, x_121);
x_149 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set(x_149, 4, x_140);
lean_ctor_set(x_149, 5, x_141);
lean_ctor_set(x_149, 6, x_142);
lean_ctor_set(x_149, 7, x_143);
lean_ctor_set(x_149, 8, x_144);
lean_ctor_set(x_149, 9, x_145);
lean_ctor_set(x_149, 10, x_146);
lean_ctor_set(x_149, 11, x_147);
x_150 = lean_st_ref_set(x_3, x_149, x_127);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_121);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_dec(x_113);
lean_dec(x_7);
x_154 = !lean_is_exclusive(x_120);
if (x_154 == 0)
{
return x_120;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_120, 0);
x_156 = lean_ctor_get(x_120, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_120);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_113);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_158 = lean_ctor_get(x_119, 0);
lean_inc(x_158);
lean_dec(x_119);
if (lean_is_scalar(x_115)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_115;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_117);
return x_159;
}
}
}
else
{
uint8_t x_179; 
lean_free_object(x_82);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_179 = !lean_is_exclusive(x_112);
if (x_179 == 0)
{
return x_112;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_112, 0);
x_181 = lean_ctor_get(x_112, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_112);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_82, 0);
x_184 = lean_ctor_get(x_82, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_82);
x_185 = l_Lean_LocalDecl_value_x3f(x_183);
lean_dec(x_183);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_186 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_81);
lean_ctor_set(x_189, 1, x_187);
x_190 = l_Lean_Meta_Closure_pushToProcess(x_189, x_2, x_3, x_4, x_5, x_6, x_7, x_188);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
x_193 = l_Lean_mkFVar(x_187);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_81);
x_195 = lean_ctor_get(x_185, 0);
lean_inc(x_195);
lean_dec(x_185);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_196 = l_Lean_Meta_Closure_preprocess(x_195, x_2, x_3, x_4, x_5, x_6, x_7, x_184);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_238; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_238 = l_Lean_Expr_hasLevelParam(x_197);
if (x_238 == 0)
{
uint8_t x_239; 
x_239 = l_Lean_Expr_hasFVar(x_197);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = l_Lean_Expr_hasMVar(x_197);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_199);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_197);
lean_ctor_set(x_241, 1, x_198);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_st_ref_get(x_7, x_198);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_st_ref_get(x_3, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_200 = x_245;
x_201 = x_246;
goto block_237;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_st_ref_get(x_7, x_198);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_st_ref_get(x_3, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_200 = x_250;
x_201 = x_251;
goto block_237;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_st_ref_get(x_7, x_198);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_st_ref_get(x_3, x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_200 = x_255;
x_201 = x_256;
goto block_237;
}
block_237:
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_202, x_197);
lean_dec(x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
lean_dec(x_199);
lean_inc(x_7);
lean_inc(x_197);
x_204 = l_Lean_Meta_Closure_collectExprAux(x_197, x_2, x_3, x_4, x_5, x_6, x_7, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_st_ref_get(x_7, x_206);
lean_dec(x_7);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_st_ref_take(x_3, x_208);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 3);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 4);
lean_inc(x_216);
x_217 = lean_ctor_get(x_210, 5);
lean_inc(x_217);
x_218 = lean_ctor_get(x_210, 6);
lean_inc(x_218);
x_219 = lean_ctor_get(x_210, 7);
lean_inc(x_219);
x_220 = lean_ctor_get(x_210, 8);
lean_inc(x_220);
x_221 = lean_ctor_get(x_210, 9);
lean_inc(x_221);
x_222 = lean_ctor_get(x_210, 10);
lean_inc(x_222);
x_223 = lean_ctor_get(x_210, 11);
lean_inc(x_223);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 lean_ctor_release(x_210, 5);
 lean_ctor_release(x_210, 6);
 lean_ctor_release(x_210, 7);
 lean_ctor_release(x_210, 8);
 lean_ctor_release(x_210, 9);
 lean_ctor_release(x_210, 10);
 lean_ctor_release(x_210, 11);
 x_224 = x_210;
} else {
 lean_dec_ref(x_210);
 x_224 = lean_box(0);
}
lean_inc(x_205);
x_225 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_213, x_197, x_205);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 12, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_212);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_226, 2, x_214);
lean_ctor_set(x_226, 3, x_215);
lean_ctor_set(x_226, 4, x_216);
lean_ctor_set(x_226, 5, x_217);
lean_ctor_set(x_226, 6, x_218);
lean_ctor_set(x_226, 7, x_219);
lean_ctor_set(x_226, 8, x_220);
lean_ctor_set(x_226, 9, x_221);
lean_ctor_set(x_226, 10, x_222);
lean_ctor_set(x_226, 11, x_223);
x_227 = lean_st_ref_set(x_3, x_226, x_211);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_205);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_197);
lean_dec(x_7);
x_231 = lean_ctor_get(x_204, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_204, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_233 = x_204;
} else {
 lean_dec_ref(x_204);
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
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_197);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_235 = lean_ctor_get(x_203, 0);
lean_inc(x_235);
lean_dec(x_203);
if (lean_is_scalar(x_199)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_199;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_201);
return x_236;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_257 = lean_ctor_get(x_196, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_196, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_259 = x_196;
} else {
 lean_dec_ref(x_196);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_81);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_261 = !lean_is_exclusive(x_82);
if (x_261 == 0)
{
return x_82;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_82, 0);
x_263 = lean_ctor_get(x_82, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_82);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
case 2:
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_1, 0);
lean_inc(x_265);
x_266 = l_Lean_Meta_getMVarDecl(x_265, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_266) == 0)
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_327; lean_object* x_328; 
x_268 = lean_ctor_get(x_266, 0);
x_269 = lean_ctor_get(x_266, 1);
x_327 = lean_ctor_get(x_268, 2);
lean_inc(x_327);
lean_dec(x_268);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_328 = l_Lean_Meta_Closure_preprocess(x_327, x_2, x_3, x_4, x_5, x_6, x_7, x_269);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_377; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
 x_331 = lean_box(0);
}
x_377 = l_Lean_Expr_hasLevelParam(x_329);
if (x_377 == 0)
{
uint8_t x_378; 
x_378 = l_Lean_Expr_hasFVar(x_329);
if (x_378 == 0)
{
uint8_t x_379; 
x_379 = l_Lean_Expr_hasMVar(x_329);
if (x_379 == 0)
{
lean_dec(x_331);
lean_ctor_set(x_266, 1, x_330);
lean_ctor_set(x_266, 0, x_329);
x_270 = x_266;
goto block_326;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_free_object(x_266);
x_380 = lean_st_ref_get(x_7, x_330);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_382 = lean_st_ref_get(x_3, x_381);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_332 = x_383;
x_333 = x_384;
goto block_376;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_free_object(x_266);
x_385 = lean_st_ref_get(x_7, x_330);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_st_ref_get(x_3, x_386);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_332 = x_388;
x_333 = x_389;
goto block_376;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_free_object(x_266);
x_390 = lean_st_ref_get(x_7, x_330);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_392 = lean_st_ref_get(x_3, x_391);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_332 = x_393;
x_333 = x_394;
goto block_376;
}
block_376:
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_334, x_329);
lean_dec(x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
lean_dec(x_331);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_329);
x_336 = l_Lean_Meta_Closure_collectExprAux(x_329, x_2, x_3, x_4, x_5, x_6, x_7, x_333);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_st_ref_get(x_7, x_338);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_341 = lean_st_ref_take(x_3, x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = !lean_is_exclusive(x_342);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_337);
x_346 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_345, x_329, x_337);
lean_ctor_set(x_342, 1, x_346);
x_347 = lean_st_ref_set(x_3, x_342, x_343);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_dec(x_349);
lean_ctor_set(x_347, 0, x_337);
x_270 = x_347;
goto block_326;
}
else
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_337);
lean_ctor_set(x_351, 1, x_350);
x_270 = x_351;
goto block_326;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_352 = lean_ctor_get(x_342, 0);
x_353 = lean_ctor_get(x_342, 1);
x_354 = lean_ctor_get(x_342, 2);
x_355 = lean_ctor_get(x_342, 3);
x_356 = lean_ctor_get(x_342, 4);
x_357 = lean_ctor_get(x_342, 5);
x_358 = lean_ctor_get(x_342, 6);
x_359 = lean_ctor_get(x_342, 7);
x_360 = lean_ctor_get(x_342, 8);
x_361 = lean_ctor_get(x_342, 9);
x_362 = lean_ctor_get(x_342, 10);
x_363 = lean_ctor_get(x_342, 11);
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
lean_inc(x_352);
lean_dec(x_342);
lean_inc(x_337);
x_364 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_353, x_329, x_337);
x_365 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_365, 0, x_352);
lean_ctor_set(x_365, 1, x_364);
lean_ctor_set(x_365, 2, x_354);
lean_ctor_set(x_365, 3, x_355);
lean_ctor_set(x_365, 4, x_356);
lean_ctor_set(x_365, 5, x_357);
lean_ctor_set(x_365, 6, x_358);
lean_ctor_set(x_365, 7, x_359);
lean_ctor_set(x_365, 8, x_360);
lean_ctor_set(x_365, 9, x_361);
lean_ctor_set(x_365, 10, x_362);
lean_ctor_set(x_365, 11, x_363);
x_366 = lean_st_ref_set(x_3, x_365, x_343);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_368 = x_366;
} else {
 lean_dec_ref(x_366);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_337);
lean_ctor_set(x_369, 1, x_367);
x_270 = x_369;
goto block_326;
}
}
else
{
uint8_t x_370; 
lean_dec(x_329);
x_370 = !lean_is_exclusive(x_336);
if (x_370 == 0)
{
x_270 = x_336;
goto block_326;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_336, 0);
x_372 = lean_ctor_get(x_336, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_336);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_270 = x_373;
goto block_326;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_329);
x_374 = lean_ctor_get(x_335, 0);
lean_inc(x_374);
lean_dec(x_335);
if (lean_is_scalar(x_331)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_331;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_333);
x_270 = x_375;
goto block_326;
}
}
}
else
{
uint8_t x_395; 
lean_free_object(x_266);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_395 = !lean_is_exclusive(x_328);
if (x_395 == 0)
{
return x_328;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_328, 0);
x_397 = lean_ctor_get(x_328, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_328);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
block_326:
{
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_275);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_st_ref_get(x_7, x_278);
lean_dec(x_7);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_st_ref_take(x_3, x_280);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = !lean_is_exclusive(x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_285 = lean_ctor_get(x_282, 6);
x_286 = lean_ctor_get(x_282, 9);
x_287 = lean_unsigned_to_nat(0u);
x_288 = 0;
lean_inc(x_274);
x_289 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_274);
lean_ctor_set(x_289, 2, x_277);
lean_ctor_set(x_289, 3, x_271);
lean_ctor_set_uint8(x_289, sizeof(void*)*4, x_288);
x_290 = lean_array_push(x_285, x_289);
x_291 = lean_array_push(x_286, x_1);
lean_ctor_set(x_282, 9, x_291);
lean_ctor_set(x_282, 6, x_290);
x_292 = lean_st_ref_set(x_3, x_282, x_283);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_292, 0);
lean_dec(x_294);
x_295 = l_Lean_mkFVar(x_274);
lean_ctor_set(x_292, 0, x_295);
return x_292;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_292, 1);
lean_inc(x_296);
lean_dec(x_292);
x_297 = l_Lean_mkFVar(x_274);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_299 = lean_ctor_get(x_282, 0);
x_300 = lean_ctor_get(x_282, 1);
x_301 = lean_ctor_get(x_282, 2);
x_302 = lean_ctor_get(x_282, 3);
x_303 = lean_ctor_get(x_282, 4);
x_304 = lean_ctor_get(x_282, 5);
x_305 = lean_ctor_get(x_282, 6);
x_306 = lean_ctor_get(x_282, 7);
x_307 = lean_ctor_get(x_282, 8);
x_308 = lean_ctor_get(x_282, 9);
x_309 = lean_ctor_get(x_282, 10);
x_310 = lean_ctor_get(x_282, 11);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_282);
x_311 = lean_unsigned_to_nat(0u);
x_312 = 0;
lean_inc(x_274);
x_313 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_274);
lean_ctor_set(x_313, 2, x_277);
lean_ctor_set(x_313, 3, x_271);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_312);
x_314 = lean_array_push(x_305, x_313);
x_315 = lean_array_push(x_308, x_1);
x_316 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_316, 0, x_299);
lean_ctor_set(x_316, 1, x_300);
lean_ctor_set(x_316, 2, x_301);
lean_ctor_set(x_316, 3, x_302);
lean_ctor_set(x_316, 4, x_303);
lean_ctor_set(x_316, 5, x_304);
lean_ctor_set(x_316, 6, x_314);
lean_ctor_set(x_316, 7, x_306);
lean_ctor_set(x_316, 8, x_307);
lean_ctor_set(x_316, 9, x_315);
lean_ctor_set(x_316, 10, x_309);
lean_ctor_set(x_316, 11, x_310);
x_317 = lean_st_ref_set(x_3, x_316, x_283);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
x_320 = l_Lean_mkFVar(x_274);
if (lean_is_scalar(x_319)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_319;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_318);
return x_321;
}
}
else
{
uint8_t x_322; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_270);
if (x_322 == 0)
{
return x_270;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_270, 0);
x_324 = lean_ctor_get(x_270, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_270);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_444; lean_object* x_445; 
x_399 = lean_ctor_get(x_266, 0);
x_400 = lean_ctor_get(x_266, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_266);
x_444 = lean_ctor_get(x_399, 2);
lean_inc(x_444);
lean_dec(x_399);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_445 = l_Lean_Meta_Closure_preprocess(x_444, x_2, x_3, x_4, x_5, x_6, x_7, x_400);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_487; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
x_487 = l_Lean_Expr_hasLevelParam(x_446);
if (x_487 == 0)
{
uint8_t x_488; 
x_488 = l_Lean_Expr_hasFVar(x_446);
if (x_488 == 0)
{
uint8_t x_489; 
x_489 = l_Lean_Expr_hasMVar(x_446);
if (x_489 == 0)
{
lean_object* x_490; 
lean_dec(x_448);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_446);
lean_ctor_set(x_490, 1, x_447);
x_401 = x_490;
goto block_443;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_491 = lean_st_ref_get(x_7, x_447);
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
lean_dec(x_491);
x_493 = lean_st_ref_get(x_3, x_492);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_449 = x_494;
x_450 = x_495;
goto block_486;
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_496 = lean_st_ref_get(x_7, x_447);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
x_498 = lean_st_ref_get(x_3, x_497);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_449 = x_499;
x_450 = x_500;
goto block_486;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_501 = lean_st_ref_get(x_7, x_447);
x_502 = lean_ctor_get(x_501, 1);
lean_inc(x_502);
lean_dec(x_501);
x_503 = lean_st_ref_get(x_3, x_502);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_449 = x_504;
x_450 = x_505;
goto block_486;
}
block_486:
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_451, x_446);
lean_dec(x_451);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; 
lean_dec(x_448);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_446);
x_453 = l_Lean_Meta_Closure_collectExprAux(x_446, x_2, x_3, x_4, x_5, x_6, x_7, x_450);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = lean_st_ref_get(x_7, x_455);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
lean_dec(x_456);
x_458 = lean_st_ref_take(x_3, x_457);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_459, 3);
lean_inc(x_464);
x_465 = lean_ctor_get(x_459, 4);
lean_inc(x_465);
x_466 = lean_ctor_get(x_459, 5);
lean_inc(x_466);
x_467 = lean_ctor_get(x_459, 6);
lean_inc(x_467);
x_468 = lean_ctor_get(x_459, 7);
lean_inc(x_468);
x_469 = lean_ctor_get(x_459, 8);
lean_inc(x_469);
x_470 = lean_ctor_get(x_459, 9);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 10);
lean_inc(x_471);
x_472 = lean_ctor_get(x_459, 11);
lean_inc(x_472);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 lean_ctor_release(x_459, 4);
 lean_ctor_release(x_459, 5);
 lean_ctor_release(x_459, 6);
 lean_ctor_release(x_459, 7);
 lean_ctor_release(x_459, 8);
 lean_ctor_release(x_459, 9);
 lean_ctor_release(x_459, 10);
 lean_ctor_release(x_459, 11);
 x_473 = x_459;
} else {
 lean_dec_ref(x_459);
 x_473 = lean_box(0);
}
lean_inc(x_454);
x_474 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_462, x_446, x_454);
if (lean_is_scalar(x_473)) {
 x_475 = lean_alloc_ctor(0, 12, 0);
} else {
 x_475 = x_473;
}
lean_ctor_set(x_475, 0, x_461);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set(x_475, 2, x_463);
lean_ctor_set(x_475, 3, x_464);
lean_ctor_set(x_475, 4, x_465);
lean_ctor_set(x_475, 5, x_466);
lean_ctor_set(x_475, 6, x_467);
lean_ctor_set(x_475, 7, x_468);
lean_ctor_set(x_475, 8, x_469);
lean_ctor_set(x_475, 9, x_470);
lean_ctor_set(x_475, 10, x_471);
lean_ctor_set(x_475, 11, x_472);
x_476 = lean_st_ref_set(x_3, x_475, x_460);
x_477 = lean_ctor_get(x_476, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_478 = x_476;
} else {
 lean_dec_ref(x_476);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_454);
lean_ctor_set(x_479, 1, x_477);
x_401 = x_479;
goto block_443;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_446);
x_480 = lean_ctor_get(x_453, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_453, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_482 = x_453;
} else {
 lean_dec_ref(x_453);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_481);
x_401 = x_483;
goto block_443;
}
}
else
{
lean_object* x_484; lean_object* x_485; 
lean_dec(x_446);
x_484 = lean_ctor_get(x_452, 0);
lean_inc(x_484);
lean_dec(x_452);
if (lean_is_scalar(x_448)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_448;
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_450);
x_401 = x_485;
goto block_443;
}
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_506 = lean_ctor_get(x_445, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_445, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_508 = x_445;
} else {
 lean_dec_ref(x_445);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
block_443:
{
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_403);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_406);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_st_ref_get(x_7, x_409);
lean_dec(x_7);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_412 = lean_st_ref_take(x_3, x_411);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_413, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_413, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_413, 3);
lean_inc(x_418);
x_419 = lean_ctor_get(x_413, 4);
lean_inc(x_419);
x_420 = lean_ctor_get(x_413, 5);
lean_inc(x_420);
x_421 = lean_ctor_get(x_413, 6);
lean_inc(x_421);
x_422 = lean_ctor_get(x_413, 7);
lean_inc(x_422);
x_423 = lean_ctor_get(x_413, 8);
lean_inc(x_423);
x_424 = lean_ctor_get(x_413, 9);
lean_inc(x_424);
x_425 = lean_ctor_get(x_413, 10);
lean_inc(x_425);
x_426 = lean_ctor_get(x_413, 11);
lean_inc(x_426);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 lean_ctor_release(x_413, 2);
 lean_ctor_release(x_413, 3);
 lean_ctor_release(x_413, 4);
 lean_ctor_release(x_413, 5);
 lean_ctor_release(x_413, 6);
 lean_ctor_release(x_413, 7);
 lean_ctor_release(x_413, 8);
 lean_ctor_release(x_413, 9);
 lean_ctor_release(x_413, 10);
 lean_ctor_release(x_413, 11);
 x_427 = x_413;
} else {
 lean_dec_ref(x_413);
 x_427 = lean_box(0);
}
x_428 = lean_unsigned_to_nat(0u);
x_429 = 0;
lean_inc(x_405);
x_430 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_405);
lean_ctor_set(x_430, 2, x_408);
lean_ctor_set(x_430, 3, x_402);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean_array_push(x_421, x_430);
x_432 = lean_array_push(x_424, x_1);
if (lean_is_scalar(x_427)) {
 x_433 = lean_alloc_ctor(0, 12, 0);
} else {
 x_433 = x_427;
}
lean_ctor_set(x_433, 0, x_415);
lean_ctor_set(x_433, 1, x_416);
lean_ctor_set(x_433, 2, x_417);
lean_ctor_set(x_433, 3, x_418);
lean_ctor_set(x_433, 4, x_419);
lean_ctor_set(x_433, 5, x_420);
lean_ctor_set(x_433, 6, x_431);
lean_ctor_set(x_433, 7, x_422);
lean_ctor_set(x_433, 8, x_423);
lean_ctor_set(x_433, 9, x_432);
lean_ctor_set(x_433, 10, x_425);
lean_ctor_set(x_433, 11, x_426);
x_434 = lean_st_ref_set(x_3, x_433, x_414);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_436 = x_434;
} else {
 lean_dec_ref(x_434);
 x_436 = lean_box(0);
}
x_437 = l_Lean_mkFVar(x_405);
if (lean_is_scalar(x_436)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_436;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_435);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_439 = lean_ctor_get(x_401, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_401, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_441 = x_401;
} else {
 lean_dec_ref(x_401);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
}
}
else
{
uint8_t x_510; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_510 = !lean_is_exclusive(x_266);
if (x_510 == 0)
{
return x_266;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_266, 0);
x_512 = lean_ctor_get(x_266, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_266);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
case 3:
{
uint8_t x_514; 
x_514 = !lean_is_exclusive(x_1);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_515 = lean_ctor_get(x_1, 0);
lean_inc(x_515);
x_516 = l_Lean_Meta_Closure_collectLevel(x_515, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_517 = !lean_is_exclusive(x_516);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; 
x_518 = lean_ctor_get(x_516, 0);
x_519 = lean_expr_update_sort(x_1, x_518);
lean_ctor_set(x_516, 0, x_519);
return x_516;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_520 = lean_ctor_get(x_516, 0);
x_521 = lean_ctor_get(x_516, 1);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_516);
x_522 = lean_expr_update_sort(x_1, x_520);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
else
{
lean_object* x_524; uint64_t x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_524 = lean_ctor_get(x_1, 0);
x_525 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_524);
lean_dec(x_1);
lean_inc(x_524);
x_526 = l_Lean_Meta_Closure_collectLevel(x_524, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_529 = x_526;
} else {
 lean_dec_ref(x_526);
 x_529 = lean_box(0);
}
x_530 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_530, 0, x_524);
lean_ctor_set_uint64(x_530, sizeof(void*)*1, x_525);
x_531 = lean_expr_update_sort(x_530, x_527);
if (lean_is_scalar(x_529)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_529;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_528);
return x_532;
}
}
case 4:
{
uint8_t x_533; 
x_533 = !lean_is_exclusive(x_1);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; uint8_t x_536; 
x_534 = lean_ctor_get(x_1, 1);
lean_inc(x_534);
x_535 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_534, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_536 = !lean_is_exclusive(x_535);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; 
x_537 = lean_ctor_get(x_535, 0);
x_538 = lean_expr_update_const(x_1, x_537);
lean_ctor_set(x_535, 0, x_538);
return x_535;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_539 = lean_ctor_get(x_535, 0);
x_540 = lean_ctor_get(x_535, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_535);
x_541 = lean_expr_update_const(x_1, x_539);
x_542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; uint64_t x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_543 = lean_ctor_get(x_1, 0);
x_544 = lean_ctor_get(x_1, 1);
x_545 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_1);
lean_inc(x_544);
x_546 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_544, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_549 = x_546;
} else {
 lean_dec_ref(x_546);
 x_549 = lean_box(0);
}
x_550 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_550, 0, x_543);
lean_ctor_set(x_550, 1, x_544);
lean_ctor_set_uint64(x_550, sizeof(void*)*2, x_545);
x_551 = lean_expr_update_const(x_550, x_547);
if (lean_is_scalar(x_549)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_549;
}
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_548);
return x_552;
}
}
case 5:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_663; lean_object* x_664; uint8_t x_708; 
x_553 = lean_ctor_get(x_1, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_1, 1);
lean_inc(x_554);
x_708 = l_Lean_Expr_hasLevelParam(x_553);
if (x_708 == 0)
{
uint8_t x_709; 
x_709 = l_Lean_Expr_hasFVar(x_553);
if (x_709 == 0)
{
uint8_t x_710; 
x_710 = l_Lean_Expr_hasMVar(x_553);
if (x_710 == 0)
{
lean_object* x_711; 
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_553);
lean_ctor_set(x_711, 1, x_8);
x_555 = x_711;
goto block_662;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_712 = lean_st_ref_get(x_7, x_8);
x_713 = lean_ctor_get(x_712, 1);
lean_inc(x_713);
lean_dec(x_712);
x_714 = lean_st_ref_get(x_3, x_713);
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
x_663 = x_715;
x_664 = x_716;
goto block_707;
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_717 = lean_st_ref_get(x_7, x_8);
x_718 = lean_ctor_get(x_717, 1);
lean_inc(x_718);
lean_dec(x_717);
x_719 = lean_st_ref_get(x_3, x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_663 = x_720;
x_664 = x_721;
goto block_707;
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_722 = lean_st_ref_get(x_7, x_8);
x_723 = lean_ctor_get(x_722, 1);
lean_inc(x_723);
lean_dec(x_722);
x_724 = lean_st_ref_get(x_3, x_723);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_663 = x_725;
x_664 = x_726;
goto block_707;
}
block_662:
{
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_594; lean_object* x_595; uint8_t x_639; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_558 = x_555;
} else {
 lean_dec_ref(x_555);
 x_558 = lean_box(0);
}
x_639 = l_Lean_Expr_hasLevelParam(x_554);
if (x_639 == 0)
{
uint8_t x_640; 
x_640 = l_Lean_Expr_hasFVar(x_554);
if (x_640 == 0)
{
uint8_t x_641; 
x_641 = l_Lean_Expr_hasMVar(x_554);
if (x_641 == 0)
{
lean_object* x_642; 
lean_dec(x_558);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_554);
lean_ctor_set(x_642, 1, x_557);
x_559 = x_642;
goto block_593;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_643 = lean_st_ref_get(x_7, x_557);
x_644 = lean_ctor_get(x_643, 1);
lean_inc(x_644);
lean_dec(x_643);
x_645 = lean_st_ref_get(x_3, x_644);
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_594 = x_646;
x_595 = x_647;
goto block_638;
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_648 = lean_st_ref_get(x_7, x_557);
x_649 = lean_ctor_get(x_648, 1);
lean_inc(x_649);
lean_dec(x_648);
x_650 = lean_st_ref_get(x_3, x_649);
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
lean_dec(x_650);
x_594 = x_651;
x_595 = x_652;
goto block_638;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_653 = lean_st_ref_get(x_7, x_557);
x_654 = lean_ctor_get(x_653, 1);
lean_inc(x_654);
lean_dec(x_653);
x_655 = lean_st_ref_get(x_3, x_654);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_594 = x_656;
x_595 = x_657;
goto block_638;
}
block_593:
{
if (lean_obj_tag(x_559) == 0)
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_560; 
x_560 = !lean_is_exclusive(x_559);
if (x_560 == 0)
{
uint8_t x_561; 
x_561 = !lean_is_exclusive(x_1);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_ctor_get(x_559, 0);
x_563 = lean_expr_update_app(x_1, x_556, x_562);
lean_ctor_set(x_559, 0, x_563);
return x_559;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; uint64_t x_567; lean_object* x_568; lean_object* x_569; 
x_564 = lean_ctor_get(x_559, 0);
x_565 = lean_ctor_get(x_1, 0);
x_566 = lean_ctor_get(x_1, 1);
x_567 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_1);
x_568 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_566);
lean_ctor_set_uint64(x_568, sizeof(void*)*2, x_567);
x_569 = lean_expr_update_app(x_568, x_556, x_564);
lean_ctor_set(x_559, 0, x_569);
return x_559;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint64_t x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_570 = lean_ctor_get(x_559, 0);
x_571 = lean_ctor_get(x_559, 1);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_559);
x_572 = lean_ctor_get(x_1, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_1, 1);
lean_inc(x_573);
x_574 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_575 = x_1;
} else {
 lean_dec_ref(x_1);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(5, 2, 8);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_572);
lean_ctor_set(x_576, 1, x_573);
lean_ctor_set_uint64(x_576, sizeof(void*)*2, x_574);
x_577 = lean_expr_update_app(x_576, x_556, x_570);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_571);
return x_578;
}
}
else
{
uint8_t x_579; 
lean_dec(x_556);
lean_dec(x_1);
x_579 = !lean_is_exclusive(x_559);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_559, 0);
lean_dec(x_580);
x_581 = l_Lean_instInhabitedExpr;
x_582 = l_Lean_Expr_updateApp_x21___closed__2;
x_583 = lean_panic_fn(x_581, x_582);
lean_ctor_set(x_559, 0, x_583);
return x_559;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_584 = lean_ctor_get(x_559, 1);
lean_inc(x_584);
lean_dec(x_559);
x_585 = l_Lean_instInhabitedExpr;
x_586 = l_Lean_Expr_updateApp_x21___closed__2;
x_587 = lean_panic_fn(x_585, x_586);
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_584);
return x_588;
}
}
}
else
{
uint8_t x_589; 
lean_dec(x_556);
lean_dec(x_1);
x_589 = !lean_is_exclusive(x_559);
if (x_589 == 0)
{
return x_559;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_559, 0);
x_591 = lean_ctor_get(x_559, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_559);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
block_638:
{
lean_object* x_596; lean_object* x_597; 
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
lean_dec(x_594);
x_597 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_596, x_554);
lean_dec(x_596);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; 
lean_dec(x_558);
lean_inc(x_7);
lean_inc(x_554);
x_598 = l_Lean_Meta_Closure_collectExprAux(x_554, x_2, x_3, x_4, x_5, x_6, x_7, x_595);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_601 = lean_st_ref_get(x_7, x_600);
lean_dec(x_7);
x_602 = lean_ctor_get(x_601, 1);
lean_inc(x_602);
lean_dec(x_601);
x_603 = lean_st_ref_take(x_3, x_602);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
x_606 = !lean_is_exclusive(x_604);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_607 = lean_ctor_get(x_604, 1);
lean_inc(x_599);
x_608 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_607, x_554, x_599);
lean_ctor_set(x_604, 1, x_608);
x_609 = lean_st_ref_set(x_3, x_604, x_605);
x_610 = !lean_is_exclusive(x_609);
if (x_610 == 0)
{
lean_object* x_611; 
x_611 = lean_ctor_get(x_609, 0);
lean_dec(x_611);
lean_ctor_set(x_609, 0, x_599);
x_559 = x_609;
goto block_593;
}
else
{
lean_object* x_612; lean_object* x_613; 
x_612 = lean_ctor_get(x_609, 1);
lean_inc(x_612);
lean_dec(x_609);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_599);
lean_ctor_set(x_613, 1, x_612);
x_559 = x_613;
goto block_593;
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_614 = lean_ctor_get(x_604, 0);
x_615 = lean_ctor_get(x_604, 1);
x_616 = lean_ctor_get(x_604, 2);
x_617 = lean_ctor_get(x_604, 3);
x_618 = lean_ctor_get(x_604, 4);
x_619 = lean_ctor_get(x_604, 5);
x_620 = lean_ctor_get(x_604, 6);
x_621 = lean_ctor_get(x_604, 7);
x_622 = lean_ctor_get(x_604, 8);
x_623 = lean_ctor_get(x_604, 9);
x_624 = lean_ctor_get(x_604, 10);
x_625 = lean_ctor_get(x_604, 11);
lean_inc(x_625);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_inc(x_621);
lean_inc(x_620);
lean_inc(x_619);
lean_inc(x_618);
lean_inc(x_617);
lean_inc(x_616);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_604);
lean_inc(x_599);
x_626 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_615, x_554, x_599);
x_627 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_627, 0, x_614);
lean_ctor_set(x_627, 1, x_626);
lean_ctor_set(x_627, 2, x_616);
lean_ctor_set(x_627, 3, x_617);
lean_ctor_set(x_627, 4, x_618);
lean_ctor_set(x_627, 5, x_619);
lean_ctor_set(x_627, 6, x_620);
lean_ctor_set(x_627, 7, x_621);
lean_ctor_set(x_627, 8, x_622);
lean_ctor_set(x_627, 9, x_623);
lean_ctor_set(x_627, 10, x_624);
lean_ctor_set(x_627, 11, x_625);
x_628 = lean_st_ref_set(x_3, x_627, x_605);
x_629 = lean_ctor_get(x_628, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 x_630 = x_628;
} else {
 lean_dec_ref(x_628);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_599);
lean_ctor_set(x_631, 1, x_629);
x_559 = x_631;
goto block_593;
}
}
else
{
uint8_t x_632; 
lean_dec(x_554);
lean_dec(x_7);
x_632 = !lean_is_exclusive(x_598);
if (x_632 == 0)
{
x_559 = x_598;
goto block_593;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_598, 0);
x_634 = lean_ctor_get(x_598, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_598);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
x_559 = x_635;
goto block_593;
}
}
}
else
{
lean_object* x_636; lean_object* x_637; 
lean_dec(x_554);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_636 = lean_ctor_get(x_597, 0);
lean_inc(x_636);
lean_dec(x_597);
if (lean_is_scalar(x_558)) {
 x_637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_637 = x_558;
}
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_595);
x_559 = x_637;
goto block_593;
}
}
}
else
{
uint8_t x_658; 
lean_dec(x_554);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_658 = !lean_is_exclusive(x_555);
if (x_658 == 0)
{
return x_555;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_555, 0);
x_660 = lean_ctor_get(x_555, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_555);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
block_707:
{
lean_object* x_665; lean_object* x_666; 
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
x_666 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_665, x_553);
lean_dec(x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_553);
x_667 = l_Lean_Meta_Closure_collectExprAux(x_553, x_2, x_3, x_4, x_5, x_6, x_7, x_664);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
lean_dec(x_667);
x_670 = lean_st_ref_get(x_7, x_669);
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec(x_670);
x_672 = lean_st_ref_take(x_3, x_671);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = !lean_is_exclusive(x_673);
if (x_675 == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; 
x_676 = lean_ctor_get(x_673, 1);
lean_inc(x_668);
x_677 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_676, x_553, x_668);
lean_ctor_set(x_673, 1, x_677);
x_678 = lean_st_ref_set(x_3, x_673, x_674);
x_679 = !lean_is_exclusive(x_678);
if (x_679 == 0)
{
lean_object* x_680; 
x_680 = lean_ctor_get(x_678, 0);
lean_dec(x_680);
lean_ctor_set(x_678, 0, x_668);
x_555 = x_678;
goto block_662;
}
else
{
lean_object* x_681; lean_object* x_682; 
x_681 = lean_ctor_get(x_678, 1);
lean_inc(x_681);
lean_dec(x_678);
x_682 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_682, 0, x_668);
lean_ctor_set(x_682, 1, x_681);
x_555 = x_682;
goto block_662;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_683 = lean_ctor_get(x_673, 0);
x_684 = lean_ctor_get(x_673, 1);
x_685 = lean_ctor_get(x_673, 2);
x_686 = lean_ctor_get(x_673, 3);
x_687 = lean_ctor_get(x_673, 4);
x_688 = lean_ctor_get(x_673, 5);
x_689 = lean_ctor_get(x_673, 6);
x_690 = lean_ctor_get(x_673, 7);
x_691 = lean_ctor_get(x_673, 8);
x_692 = lean_ctor_get(x_673, 9);
x_693 = lean_ctor_get(x_673, 10);
x_694 = lean_ctor_get(x_673, 11);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
lean_inc(x_691);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
lean_inc(x_687);
lean_inc(x_686);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_dec(x_673);
lean_inc(x_668);
x_695 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_684, x_553, x_668);
x_696 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_696, 0, x_683);
lean_ctor_set(x_696, 1, x_695);
lean_ctor_set(x_696, 2, x_685);
lean_ctor_set(x_696, 3, x_686);
lean_ctor_set(x_696, 4, x_687);
lean_ctor_set(x_696, 5, x_688);
lean_ctor_set(x_696, 6, x_689);
lean_ctor_set(x_696, 7, x_690);
lean_ctor_set(x_696, 8, x_691);
lean_ctor_set(x_696, 9, x_692);
lean_ctor_set(x_696, 10, x_693);
lean_ctor_set(x_696, 11, x_694);
x_697 = lean_st_ref_set(x_3, x_696, x_674);
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_699 = x_697;
} else {
 lean_dec_ref(x_697);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_668);
lean_ctor_set(x_700, 1, x_698);
x_555 = x_700;
goto block_662;
}
}
else
{
uint8_t x_701; 
lean_dec(x_553);
x_701 = !lean_is_exclusive(x_667);
if (x_701 == 0)
{
x_555 = x_667;
goto block_662;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_667, 0);
x_703 = lean_ctor_get(x_667, 1);
lean_inc(x_703);
lean_inc(x_702);
lean_dec(x_667);
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
x_555 = x_704;
goto block_662;
}
}
}
else
{
lean_object* x_705; lean_object* x_706; 
lean_dec(x_553);
x_705 = lean_ctor_get(x_666, 0);
lean_inc(x_705);
lean_dec(x_666);
x_706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_664);
x_555 = x_706;
goto block_662;
}
}
}
case 6:
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_843; lean_object* x_844; uint8_t x_888; 
x_727 = lean_ctor_get(x_1, 1);
lean_inc(x_727);
x_728 = lean_ctor_get(x_1, 2);
lean_inc(x_728);
x_888 = l_Lean_Expr_hasLevelParam(x_727);
if (x_888 == 0)
{
uint8_t x_889; 
x_889 = l_Lean_Expr_hasFVar(x_727);
if (x_889 == 0)
{
uint8_t x_890; 
x_890 = l_Lean_Expr_hasMVar(x_727);
if (x_890 == 0)
{
lean_object* x_891; 
x_891 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_891, 0, x_727);
lean_ctor_set(x_891, 1, x_8);
x_729 = x_891;
goto block_842;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_892 = lean_st_ref_get(x_7, x_8);
x_893 = lean_ctor_get(x_892, 1);
lean_inc(x_893);
lean_dec(x_892);
x_894 = lean_st_ref_get(x_3, x_893);
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
lean_dec(x_894);
x_843 = x_895;
x_844 = x_896;
goto block_887;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_897 = lean_st_ref_get(x_7, x_8);
x_898 = lean_ctor_get(x_897, 1);
lean_inc(x_898);
lean_dec(x_897);
x_899 = lean_st_ref_get(x_3, x_898);
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
lean_dec(x_899);
x_843 = x_900;
x_844 = x_901;
goto block_887;
}
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_902 = lean_st_ref_get(x_7, x_8);
x_903 = lean_ctor_get(x_902, 1);
lean_inc(x_903);
lean_dec(x_902);
x_904 = lean_st_ref_get(x_3, x_903);
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
lean_dec(x_904);
x_843 = x_905;
x_844 = x_906;
goto block_887;
}
block_842:
{
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_774; lean_object* x_775; uint8_t x_819; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_732 = x_729;
} else {
 lean_dec_ref(x_729);
 x_732 = lean_box(0);
}
x_819 = l_Lean_Expr_hasLevelParam(x_728);
if (x_819 == 0)
{
uint8_t x_820; 
x_820 = l_Lean_Expr_hasFVar(x_728);
if (x_820 == 0)
{
uint8_t x_821; 
x_821 = l_Lean_Expr_hasMVar(x_728);
if (x_821 == 0)
{
lean_object* x_822; 
lean_dec(x_732);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_728);
lean_ctor_set(x_822, 1, x_731);
x_733 = x_822;
goto block_773;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_823 = lean_st_ref_get(x_7, x_731);
x_824 = lean_ctor_get(x_823, 1);
lean_inc(x_824);
lean_dec(x_823);
x_825 = lean_st_ref_get(x_3, x_824);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_774 = x_826;
x_775 = x_827;
goto block_818;
}
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_828 = lean_st_ref_get(x_7, x_731);
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
lean_dec(x_828);
x_830 = lean_st_ref_get(x_3, x_829);
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_830, 1);
lean_inc(x_832);
lean_dec(x_830);
x_774 = x_831;
x_775 = x_832;
goto block_818;
}
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_833 = lean_st_ref_get(x_7, x_731);
x_834 = lean_ctor_get(x_833, 1);
lean_inc(x_834);
lean_dec(x_833);
x_835 = lean_st_ref_get(x_3, x_834);
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
lean_dec(x_835);
x_774 = x_836;
x_775 = x_837;
goto block_818;
}
block_773:
{
if (lean_obj_tag(x_733) == 0)
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_734; 
x_734 = !lean_is_exclusive(x_733);
if (x_734 == 0)
{
uint8_t x_735; 
x_735 = !lean_is_exclusive(x_1);
if (x_735 == 0)
{
lean_object* x_736; uint64_t x_737; uint8_t x_738; lean_object* x_739; 
x_736 = lean_ctor_get(x_733, 0);
x_737 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_738 = (uint8_t)((x_737 << 24) >> 61);
x_739 = lean_expr_update_lambda(x_1, x_738, x_730, x_736);
lean_ctor_set(x_733, 0, x_739);
return x_733;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint64_t x_744; lean_object* x_745; uint8_t x_746; lean_object* x_747; 
x_740 = lean_ctor_get(x_733, 0);
x_741 = lean_ctor_get(x_1, 0);
x_742 = lean_ctor_get(x_1, 1);
x_743 = lean_ctor_get(x_1, 2);
x_744 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_741);
lean_dec(x_1);
x_745 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_745, 0, x_741);
lean_ctor_set(x_745, 1, x_742);
lean_ctor_set(x_745, 2, x_743);
lean_ctor_set_uint64(x_745, sizeof(void*)*3, x_744);
x_746 = (uint8_t)((x_744 << 24) >> 61);
x_747 = lean_expr_update_lambda(x_745, x_746, x_730, x_740);
lean_ctor_set(x_733, 0, x_747);
return x_733;
}
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint64_t x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; lean_object* x_757; lean_object* x_758; 
x_748 = lean_ctor_get(x_733, 0);
x_749 = lean_ctor_get(x_733, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_733);
x_750 = lean_ctor_get(x_1, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_1, 1);
lean_inc(x_751);
x_752 = lean_ctor_get(x_1, 2);
lean_inc(x_752);
x_753 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_754 = x_1;
} else {
 lean_dec_ref(x_1);
 x_754 = lean_box(0);
}
if (lean_is_scalar(x_754)) {
 x_755 = lean_alloc_ctor(6, 3, 8);
} else {
 x_755 = x_754;
}
lean_ctor_set(x_755, 0, x_750);
lean_ctor_set(x_755, 1, x_751);
lean_ctor_set(x_755, 2, x_752);
lean_ctor_set_uint64(x_755, sizeof(void*)*3, x_753);
x_756 = (uint8_t)((x_753 << 24) >> 61);
x_757 = lean_expr_update_lambda(x_755, x_756, x_730, x_748);
x_758 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_749);
return x_758;
}
}
else
{
uint8_t x_759; 
lean_dec(x_730);
lean_dec(x_1);
x_759 = !lean_is_exclusive(x_733);
if (x_759 == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_760 = lean_ctor_get(x_733, 0);
lean_dec(x_760);
x_761 = l_Lean_instInhabitedExpr;
x_762 = l_Lean_Expr_updateLambdaE_x21___closed__2;
x_763 = lean_panic_fn(x_761, x_762);
lean_ctor_set(x_733, 0, x_763);
return x_733;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_764 = lean_ctor_get(x_733, 1);
lean_inc(x_764);
lean_dec(x_733);
x_765 = l_Lean_instInhabitedExpr;
x_766 = l_Lean_Expr_updateLambdaE_x21___closed__2;
x_767 = lean_panic_fn(x_765, x_766);
x_768 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_764);
return x_768;
}
}
}
else
{
uint8_t x_769; 
lean_dec(x_730);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_733);
if (x_769 == 0)
{
return x_733;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_733, 0);
x_771 = lean_ctor_get(x_733, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_733);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
block_818:
{
lean_object* x_776; lean_object* x_777; 
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
x_777 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_776, x_728);
lean_dec(x_776);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; 
lean_dec(x_732);
lean_inc(x_7);
lean_inc(x_728);
x_778 = l_Lean_Meta_Closure_collectExprAux(x_728, x_2, x_3, x_4, x_5, x_6, x_7, x_775);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; 
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
lean_dec(x_778);
x_781 = lean_st_ref_get(x_7, x_780);
lean_dec(x_7);
x_782 = lean_ctor_get(x_781, 1);
lean_inc(x_782);
lean_dec(x_781);
x_783 = lean_st_ref_take(x_3, x_782);
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
x_786 = !lean_is_exclusive(x_784);
if (x_786 == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; uint8_t x_790; 
x_787 = lean_ctor_get(x_784, 1);
lean_inc(x_779);
x_788 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_787, x_728, x_779);
lean_ctor_set(x_784, 1, x_788);
x_789 = lean_st_ref_set(x_3, x_784, x_785);
x_790 = !lean_is_exclusive(x_789);
if (x_790 == 0)
{
lean_object* x_791; 
x_791 = lean_ctor_get(x_789, 0);
lean_dec(x_791);
lean_ctor_set(x_789, 0, x_779);
x_733 = x_789;
goto block_773;
}
else
{
lean_object* x_792; lean_object* x_793; 
x_792 = lean_ctor_get(x_789, 1);
lean_inc(x_792);
lean_dec(x_789);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_779);
lean_ctor_set(x_793, 1, x_792);
x_733 = x_793;
goto block_773;
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_794 = lean_ctor_get(x_784, 0);
x_795 = lean_ctor_get(x_784, 1);
x_796 = lean_ctor_get(x_784, 2);
x_797 = lean_ctor_get(x_784, 3);
x_798 = lean_ctor_get(x_784, 4);
x_799 = lean_ctor_get(x_784, 5);
x_800 = lean_ctor_get(x_784, 6);
x_801 = lean_ctor_get(x_784, 7);
x_802 = lean_ctor_get(x_784, 8);
x_803 = lean_ctor_get(x_784, 9);
x_804 = lean_ctor_get(x_784, 10);
x_805 = lean_ctor_get(x_784, 11);
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
lean_inc(x_795);
lean_inc(x_794);
lean_dec(x_784);
lean_inc(x_779);
x_806 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_795, x_728, x_779);
x_807 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_807, 0, x_794);
lean_ctor_set(x_807, 1, x_806);
lean_ctor_set(x_807, 2, x_796);
lean_ctor_set(x_807, 3, x_797);
lean_ctor_set(x_807, 4, x_798);
lean_ctor_set(x_807, 5, x_799);
lean_ctor_set(x_807, 6, x_800);
lean_ctor_set(x_807, 7, x_801);
lean_ctor_set(x_807, 8, x_802);
lean_ctor_set(x_807, 9, x_803);
lean_ctor_set(x_807, 10, x_804);
lean_ctor_set(x_807, 11, x_805);
x_808 = lean_st_ref_set(x_3, x_807, x_785);
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 x_810 = x_808;
} else {
 lean_dec_ref(x_808);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(0, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_779);
lean_ctor_set(x_811, 1, x_809);
x_733 = x_811;
goto block_773;
}
}
else
{
uint8_t x_812; 
lean_dec(x_728);
lean_dec(x_7);
x_812 = !lean_is_exclusive(x_778);
if (x_812 == 0)
{
x_733 = x_778;
goto block_773;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_778, 0);
x_814 = lean_ctor_get(x_778, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_778);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
x_733 = x_815;
goto block_773;
}
}
}
else
{
lean_object* x_816; lean_object* x_817; 
lean_dec(x_728);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_816 = lean_ctor_get(x_777, 0);
lean_inc(x_816);
lean_dec(x_777);
if (lean_is_scalar(x_732)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_732;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_775);
x_733 = x_817;
goto block_773;
}
}
}
else
{
uint8_t x_838; 
lean_dec(x_728);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_838 = !lean_is_exclusive(x_729);
if (x_838 == 0)
{
return x_729;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_729, 0);
x_840 = lean_ctor_get(x_729, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_729);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
block_887:
{
lean_object* x_845; lean_object* x_846; 
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
lean_dec(x_843);
x_846 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_845, x_727);
lean_dec(x_845);
if (lean_obj_tag(x_846) == 0)
{
lean_object* x_847; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_727);
x_847 = l_Lean_Meta_Closure_collectExprAux(x_727, x_2, x_3, x_4, x_5, x_6, x_7, x_844);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_847, 1);
lean_inc(x_849);
lean_dec(x_847);
x_850 = lean_st_ref_get(x_7, x_849);
x_851 = lean_ctor_get(x_850, 1);
lean_inc(x_851);
lean_dec(x_850);
x_852 = lean_st_ref_take(x_3, x_851);
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_852, 1);
lean_inc(x_854);
lean_dec(x_852);
x_855 = !lean_is_exclusive(x_853);
if (x_855 == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; uint8_t x_859; 
x_856 = lean_ctor_get(x_853, 1);
lean_inc(x_848);
x_857 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_856, x_727, x_848);
lean_ctor_set(x_853, 1, x_857);
x_858 = lean_st_ref_set(x_3, x_853, x_854);
x_859 = !lean_is_exclusive(x_858);
if (x_859 == 0)
{
lean_object* x_860; 
x_860 = lean_ctor_get(x_858, 0);
lean_dec(x_860);
lean_ctor_set(x_858, 0, x_848);
x_729 = x_858;
goto block_842;
}
else
{
lean_object* x_861; lean_object* x_862; 
x_861 = lean_ctor_get(x_858, 1);
lean_inc(x_861);
lean_dec(x_858);
x_862 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_862, 0, x_848);
lean_ctor_set(x_862, 1, x_861);
x_729 = x_862;
goto block_842;
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_863 = lean_ctor_get(x_853, 0);
x_864 = lean_ctor_get(x_853, 1);
x_865 = lean_ctor_get(x_853, 2);
x_866 = lean_ctor_get(x_853, 3);
x_867 = lean_ctor_get(x_853, 4);
x_868 = lean_ctor_get(x_853, 5);
x_869 = lean_ctor_get(x_853, 6);
x_870 = lean_ctor_get(x_853, 7);
x_871 = lean_ctor_get(x_853, 8);
x_872 = lean_ctor_get(x_853, 9);
x_873 = lean_ctor_get(x_853, 10);
x_874 = lean_ctor_get(x_853, 11);
lean_inc(x_874);
lean_inc(x_873);
lean_inc(x_872);
lean_inc(x_871);
lean_inc(x_870);
lean_inc(x_869);
lean_inc(x_868);
lean_inc(x_867);
lean_inc(x_866);
lean_inc(x_865);
lean_inc(x_864);
lean_inc(x_863);
lean_dec(x_853);
lean_inc(x_848);
x_875 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_864, x_727, x_848);
x_876 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_876, 0, x_863);
lean_ctor_set(x_876, 1, x_875);
lean_ctor_set(x_876, 2, x_865);
lean_ctor_set(x_876, 3, x_866);
lean_ctor_set(x_876, 4, x_867);
lean_ctor_set(x_876, 5, x_868);
lean_ctor_set(x_876, 6, x_869);
lean_ctor_set(x_876, 7, x_870);
lean_ctor_set(x_876, 8, x_871);
lean_ctor_set(x_876, 9, x_872);
lean_ctor_set(x_876, 10, x_873);
lean_ctor_set(x_876, 11, x_874);
x_877 = lean_st_ref_set(x_3, x_876, x_854);
x_878 = lean_ctor_get(x_877, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 lean_ctor_release(x_877, 1);
 x_879 = x_877;
} else {
 lean_dec_ref(x_877);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_848);
lean_ctor_set(x_880, 1, x_878);
x_729 = x_880;
goto block_842;
}
}
else
{
uint8_t x_881; 
lean_dec(x_727);
x_881 = !lean_is_exclusive(x_847);
if (x_881 == 0)
{
x_729 = x_847;
goto block_842;
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_847, 0);
x_883 = lean_ctor_get(x_847, 1);
lean_inc(x_883);
lean_inc(x_882);
lean_dec(x_847);
x_884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_884, 0, x_882);
lean_ctor_set(x_884, 1, x_883);
x_729 = x_884;
goto block_842;
}
}
}
else
{
lean_object* x_885; lean_object* x_886; 
lean_dec(x_727);
x_885 = lean_ctor_get(x_846, 0);
lean_inc(x_885);
lean_dec(x_846);
x_886 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_844);
x_729 = x_886;
goto block_842;
}
}
}
case 7:
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_1023; lean_object* x_1024; uint8_t x_1068; 
x_907 = lean_ctor_get(x_1, 1);
lean_inc(x_907);
x_908 = lean_ctor_get(x_1, 2);
lean_inc(x_908);
x_1068 = l_Lean_Expr_hasLevelParam(x_907);
if (x_1068 == 0)
{
uint8_t x_1069; 
x_1069 = l_Lean_Expr_hasFVar(x_907);
if (x_1069 == 0)
{
uint8_t x_1070; 
x_1070 = l_Lean_Expr_hasMVar(x_907);
if (x_1070 == 0)
{
lean_object* x_1071; 
x_1071 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1071, 0, x_907);
lean_ctor_set(x_1071, 1, x_8);
x_909 = x_1071;
goto block_1022;
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1072 = lean_st_ref_get(x_7, x_8);
x_1073 = lean_ctor_get(x_1072, 1);
lean_inc(x_1073);
lean_dec(x_1072);
x_1074 = lean_st_ref_get(x_3, x_1073);
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
lean_dec(x_1074);
x_1023 = x_1075;
x_1024 = x_1076;
goto block_1067;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1077 = lean_st_ref_get(x_7, x_8);
x_1078 = lean_ctor_get(x_1077, 1);
lean_inc(x_1078);
lean_dec(x_1077);
x_1079 = lean_st_ref_get(x_3, x_1078);
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1079, 1);
lean_inc(x_1081);
lean_dec(x_1079);
x_1023 = x_1080;
x_1024 = x_1081;
goto block_1067;
}
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1082 = lean_st_ref_get(x_7, x_8);
x_1083 = lean_ctor_get(x_1082, 1);
lean_inc(x_1083);
lean_dec(x_1082);
x_1084 = lean_st_ref_get(x_3, x_1083);
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
lean_dec(x_1084);
x_1023 = x_1085;
x_1024 = x_1086;
goto block_1067;
}
block_1022:
{
if (lean_obj_tag(x_909) == 0)
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_954; lean_object* x_955; uint8_t x_999; 
x_910 = lean_ctor_get(x_909, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_909, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_909)) {
 lean_ctor_release(x_909, 0);
 lean_ctor_release(x_909, 1);
 x_912 = x_909;
} else {
 lean_dec_ref(x_909);
 x_912 = lean_box(0);
}
x_999 = l_Lean_Expr_hasLevelParam(x_908);
if (x_999 == 0)
{
uint8_t x_1000; 
x_1000 = l_Lean_Expr_hasFVar(x_908);
if (x_1000 == 0)
{
uint8_t x_1001; 
x_1001 = l_Lean_Expr_hasMVar(x_908);
if (x_1001 == 0)
{
lean_object* x_1002; 
lean_dec(x_912);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_908);
lean_ctor_set(x_1002, 1, x_911);
x_913 = x_1002;
goto block_953;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1003 = lean_st_ref_get(x_7, x_911);
x_1004 = lean_ctor_get(x_1003, 1);
lean_inc(x_1004);
lean_dec(x_1003);
x_1005 = lean_st_ref_get(x_3, x_1004);
x_1006 = lean_ctor_get(x_1005, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1005, 1);
lean_inc(x_1007);
lean_dec(x_1005);
x_954 = x_1006;
x_955 = x_1007;
goto block_998;
}
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1008 = lean_st_ref_get(x_7, x_911);
x_1009 = lean_ctor_get(x_1008, 1);
lean_inc(x_1009);
lean_dec(x_1008);
x_1010 = lean_st_ref_get(x_3, x_1009);
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
lean_dec(x_1010);
x_954 = x_1011;
x_955 = x_1012;
goto block_998;
}
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1013 = lean_st_ref_get(x_7, x_911);
x_1014 = lean_ctor_get(x_1013, 1);
lean_inc(x_1014);
lean_dec(x_1013);
x_1015 = lean_st_ref_get(x_3, x_1014);
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
lean_dec(x_1015);
x_954 = x_1016;
x_955 = x_1017;
goto block_998;
}
block_953:
{
if (lean_obj_tag(x_913) == 0)
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_914; 
x_914 = !lean_is_exclusive(x_913);
if (x_914 == 0)
{
uint8_t x_915; 
x_915 = !lean_is_exclusive(x_1);
if (x_915 == 0)
{
lean_object* x_916; uint64_t x_917; uint8_t x_918; lean_object* x_919; 
x_916 = lean_ctor_get(x_913, 0);
x_917 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_918 = (uint8_t)((x_917 << 24) >> 61);
x_919 = lean_expr_update_forall(x_1, x_918, x_910, x_916);
lean_ctor_set(x_913, 0, x_919);
return x_913;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; uint64_t x_924; lean_object* x_925; uint8_t x_926; lean_object* x_927; 
x_920 = lean_ctor_get(x_913, 0);
x_921 = lean_ctor_get(x_1, 0);
x_922 = lean_ctor_get(x_1, 1);
x_923 = lean_ctor_get(x_1, 2);
x_924 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_923);
lean_inc(x_922);
lean_inc(x_921);
lean_dec(x_1);
x_925 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_925, 0, x_921);
lean_ctor_set(x_925, 1, x_922);
lean_ctor_set(x_925, 2, x_923);
lean_ctor_set_uint64(x_925, sizeof(void*)*3, x_924);
x_926 = (uint8_t)((x_924 << 24) >> 61);
x_927 = lean_expr_update_forall(x_925, x_926, x_910, x_920);
lean_ctor_set(x_913, 0, x_927);
return x_913;
}
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; uint64_t x_933; lean_object* x_934; lean_object* x_935; uint8_t x_936; lean_object* x_937; lean_object* x_938; 
x_928 = lean_ctor_get(x_913, 0);
x_929 = lean_ctor_get(x_913, 1);
lean_inc(x_929);
lean_inc(x_928);
lean_dec(x_913);
x_930 = lean_ctor_get(x_1, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_1, 1);
lean_inc(x_931);
x_932 = lean_ctor_get(x_1, 2);
lean_inc(x_932);
x_933 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_934 = x_1;
} else {
 lean_dec_ref(x_1);
 x_934 = lean_box(0);
}
if (lean_is_scalar(x_934)) {
 x_935 = lean_alloc_ctor(7, 3, 8);
} else {
 x_935 = x_934;
}
lean_ctor_set(x_935, 0, x_930);
lean_ctor_set(x_935, 1, x_931);
lean_ctor_set(x_935, 2, x_932);
lean_ctor_set_uint64(x_935, sizeof(void*)*3, x_933);
x_936 = (uint8_t)((x_933 << 24) >> 61);
x_937 = lean_expr_update_forall(x_935, x_936, x_910, x_928);
x_938 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_929);
return x_938;
}
}
else
{
uint8_t x_939; 
lean_dec(x_910);
lean_dec(x_1);
x_939 = !lean_is_exclusive(x_913);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_940 = lean_ctor_get(x_913, 0);
lean_dec(x_940);
x_941 = l_Lean_instInhabitedExpr;
x_942 = l_Lean_Expr_updateForallE_x21___closed__2;
x_943 = lean_panic_fn(x_941, x_942);
lean_ctor_set(x_913, 0, x_943);
return x_913;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_944 = lean_ctor_get(x_913, 1);
lean_inc(x_944);
lean_dec(x_913);
x_945 = l_Lean_instInhabitedExpr;
x_946 = l_Lean_Expr_updateForallE_x21___closed__2;
x_947 = lean_panic_fn(x_945, x_946);
x_948 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_948, 0, x_947);
lean_ctor_set(x_948, 1, x_944);
return x_948;
}
}
}
else
{
uint8_t x_949; 
lean_dec(x_910);
lean_dec(x_1);
x_949 = !lean_is_exclusive(x_913);
if (x_949 == 0)
{
return x_913;
}
else
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; 
x_950 = lean_ctor_get(x_913, 0);
x_951 = lean_ctor_get(x_913, 1);
lean_inc(x_951);
lean_inc(x_950);
lean_dec(x_913);
x_952 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_952, 0, x_950);
lean_ctor_set(x_952, 1, x_951);
return x_952;
}
}
}
block_998:
{
lean_object* x_956; lean_object* x_957; 
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec(x_954);
x_957 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_956, x_908);
lean_dec(x_956);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; 
lean_dec(x_912);
lean_inc(x_7);
lean_inc(x_908);
x_958 = l_Lean_Meta_Closure_collectExprAux(x_908, x_2, x_3, x_4, x_5, x_6, x_7, x_955);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; uint8_t x_966; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = lean_st_ref_get(x_7, x_960);
lean_dec(x_7);
x_962 = lean_ctor_get(x_961, 1);
lean_inc(x_962);
lean_dec(x_961);
x_963 = lean_st_ref_take(x_3, x_962);
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec(x_963);
x_966 = !lean_is_exclusive(x_964);
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; uint8_t x_970; 
x_967 = lean_ctor_get(x_964, 1);
lean_inc(x_959);
x_968 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_967, x_908, x_959);
lean_ctor_set(x_964, 1, x_968);
x_969 = lean_st_ref_set(x_3, x_964, x_965);
x_970 = !lean_is_exclusive(x_969);
if (x_970 == 0)
{
lean_object* x_971; 
x_971 = lean_ctor_get(x_969, 0);
lean_dec(x_971);
lean_ctor_set(x_969, 0, x_959);
x_913 = x_969;
goto block_953;
}
else
{
lean_object* x_972; lean_object* x_973; 
x_972 = lean_ctor_get(x_969, 1);
lean_inc(x_972);
lean_dec(x_969);
x_973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_973, 0, x_959);
lean_ctor_set(x_973, 1, x_972);
x_913 = x_973;
goto block_953;
}
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_974 = lean_ctor_get(x_964, 0);
x_975 = lean_ctor_get(x_964, 1);
x_976 = lean_ctor_get(x_964, 2);
x_977 = lean_ctor_get(x_964, 3);
x_978 = lean_ctor_get(x_964, 4);
x_979 = lean_ctor_get(x_964, 5);
x_980 = lean_ctor_get(x_964, 6);
x_981 = lean_ctor_get(x_964, 7);
x_982 = lean_ctor_get(x_964, 8);
x_983 = lean_ctor_get(x_964, 9);
x_984 = lean_ctor_get(x_964, 10);
x_985 = lean_ctor_get(x_964, 11);
lean_inc(x_985);
lean_inc(x_984);
lean_inc(x_983);
lean_inc(x_982);
lean_inc(x_981);
lean_inc(x_980);
lean_inc(x_979);
lean_inc(x_978);
lean_inc(x_977);
lean_inc(x_976);
lean_inc(x_975);
lean_inc(x_974);
lean_dec(x_964);
lean_inc(x_959);
x_986 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_975, x_908, x_959);
x_987 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_987, 0, x_974);
lean_ctor_set(x_987, 1, x_986);
lean_ctor_set(x_987, 2, x_976);
lean_ctor_set(x_987, 3, x_977);
lean_ctor_set(x_987, 4, x_978);
lean_ctor_set(x_987, 5, x_979);
lean_ctor_set(x_987, 6, x_980);
lean_ctor_set(x_987, 7, x_981);
lean_ctor_set(x_987, 8, x_982);
lean_ctor_set(x_987, 9, x_983);
lean_ctor_set(x_987, 10, x_984);
lean_ctor_set(x_987, 11, x_985);
x_988 = lean_st_ref_set(x_3, x_987, x_965);
x_989 = lean_ctor_get(x_988, 1);
lean_inc(x_989);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_990 = x_988;
} else {
 lean_dec_ref(x_988);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(0, 2, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_959);
lean_ctor_set(x_991, 1, x_989);
x_913 = x_991;
goto block_953;
}
}
else
{
uint8_t x_992; 
lean_dec(x_908);
lean_dec(x_7);
x_992 = !lean_is_exclusive(x_958);
if (x_992 == 0)
{
x_913 = x_958;
goto block_953;
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_958, 0);
x_994 = lean_ctor_get(x_958, 1);
lean_inc(x_994);
lean_inc(x_993);
lean_dec(x_958);
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_993);
lean_ctor_set(x_995, 1, x_994);
x_913 = x_995;
goto block_953;
}
}
}
else
{
lean_object* x_996; lean_object* x_997; 
lean_dec(x_908);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_996 = lean_ctor_get(x_957, 0);
lean_inc(x_996);
lean_dec(x_957);
if (lean_is_scalar(x_912)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_912;
}
lean_ctor_set(x_997, 0, x_996);
lean_ctor_set(x_997, 1, x_955);
x_913 = x_997;
goto block_953;
}
}
}
else
{
uint8_t x_1018; 
lean_dec(x_908);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1018 = !lean_is_exclusive(x_909);
if (x_1018 == 0)
{
return x_909;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_909, 0);
x_1020 = lean_ctor_get(x_909, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_909);
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
return x_1021;
}
}
}
block_1067:
{
lean_object* x_1025; lean_object* x_1026; 
x_1025 = lean_ctor_get(x_1023, 1);
lean_inc(x_1025);
lean_dec(x_1023);
x_1026 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1025, x_907);
lean_dec(x_1025);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_907);
x_1027 = l_Lean_Meta_Closure_collectExprAux(x_907, x_2, x_3, x_4, x_5, x_6, x_7, x_1024);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; 
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_st_ref_get(x_7, x_1029);
x_1031 = lean_ctor_get(x_1030, 1);
lean_inc(x_1031);
lean_dec(x_1030);
x_1032 = lean_st_ref_take(x_3, x_1031);
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_1035 = !lean_is_exclusive(x_1033);
if (x_1035 == 0)
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; uint8_t x_1039; 
x_1036 = lean_ctor_get(x_1033, 1);
lean_inc(x_1028);
x_1037 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1036, x_907, x_1028);
lean_ctor_set(x_1033, 1, x_1037);
x_1038 = lean_st_ref_set(x_3, x_1033, x_1034);
x_1039 = !lean_is_exclusive(x_1038);
if (x_1039 == 0)
{
lean_object* x_1040; 
x_1040 = lean_ctor_get(x_1038, 0);
lean_dec(x_1040);
lean_ctor_set(x_1038, 0, x_1028);
x_909 = x_1038;
goto block_1022;
}
else
{
lean_object* x_1041; lean_object* x_1042; 
x_1041 = lean_ctor_get(x_1038, 1);
lean_inc(x_1041);
lean_dec(x_1038);
x_1042 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1042, 0, x_1028);
lean_ctor_set(x_1042, 1, x_1041);
x_909 = x_1042;
goto block_1022;
}
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1043 = lean_ctor_get(x_1033, 0);
x_1044 = lean_ctor_get(x_1033, 1);
x_1045 = lean_ctor_get(x_1033, 2);
x_1046 = lean_ctor_get(x_1033, 3);
x_1047 = lean_ctor_get(x_1033, 4);
x_1048 = lean_ctor_get(x_1033, 5);
x_1049 = lean_ctor_get(x_1033, 6);
x_1050 = lean_ctor_get(x_1033, 7);
x_1051 = lean_ctor_get(x_1033, 8);
x_1052 = lean_ctor_get(x_1033, 9);
x_1053 = lean_ctor_get(x_1033, 10);
x_1054 = lean_ctor_get(x_1033, 11);
lean_inc(x_1054);
lean_inc(x_1053);
lean_inc(x_1052);
lean_inc(x_1051);
lean_inc(x_1050);
lean_inc(x_1049);
lean_inc(x_1048);
lean_inc(x_1047);
lean_inc(x_1046);
lean_inc(x_1045);
lean_inc(x_1044);
lean_inc(x_1043);
lean_dec(x_1033);
lean_inc(x_1028);
x_1055 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1044, x_907, x_1028);
x_1056 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1056, 0, x_1043);
lean_ctor_set(x_1056, 1, x_1055);
lean_ctor_set(x_1056, 2, x_1045);
lean_ctor_set(x_1056, 3, x_1046);
lean_ctor_set(x_1056, 4, x_1047);
lean_ctor_set(x_1056, 5, x_1048);
lean_ctor_set(x_1056, 6, x_1049);
lean_ctor_set(x_1056, 7, x_1050);
lean_ctor_set(x_1056, 8, x_1051);
lean_ctor_set(x_1056, 9, x_1052);
lean_ctor_set(x_1056, 10, x_1053);
lean_ctor_set(x_1056, 11, x_1054);
x_1057 = lean_st_ref_set(x_3, x_1056, x_1034);
x_1058 = lean_ctor_get(x_1057, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1057)) {
 lean_ctor_release(x_1057, 0);
 lean_ctor_release(x_1057, 1);
 x_1059 = x_1057;
} else {
 lean_dec_ref(x_1057);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_1028);
lean_ctor_set(x_1060, 1, x_1058);
x_909 = x_1060;
goto block_1022;
}
}
else
{
uint8_t x_1061; 
lean_dec(x_907);
x_1061 = !lean_is_exclusive(x_1027);
if (x_1061 == 0)
{
x_909 = x_1027;
goto block_1022;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1062 = lean_ctor_get(x_1027, 0);
x_1063 = lean_ctor_get(x_1027, 1);
lean_inc(x_1063);
lean_inc(x_1062);
lean_dec(x_1027);
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
x_909 = x_1064;
goto block_1022;
}
}
}
else
{
lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_907);
x_1065 = lean_ctor_get(x_1026, 0);
lean_inc(x_1065);
lean_dec(x_1026);
x_1066 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1066, 0, x_1065);
lean_ctor_set(x_1066, 1, x_1024);
x_909 = x_1066;
goto block_1022;
}
}
}
case 8:
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1275; lean_object* x_1276; uint8_t x_1320; 
x_1087 = lean_ctor_get(x_1, 1);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1, 2);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1, 3);
lean_inc(x_1089);
x_1320 = l_Lean_Expr_hasLevelParam(x_1087);
if (x_1320 == 0)
{
uint8_t x_1321; 
x_1321 = l_Lean_Expr_hasFVar(x_1087);
if (x_1321 == 0)
{
uint8_t x_1322; 
x_1322 = l_Lean_Expr_hasMVar(x_1087);
if (x_1322 == 0)
{
lean_object* x_1323; 
x_1323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1323, 0, x_1087);
lean_ctor_set(x_1323, 1, x_8);
x_1090 = x_1323;
goto block_1274;
}
else
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; 
x_1324 = lean_st_ref_get(x_7, x_8);
x_1325 = lean_ctor_get(x_1324, 1);
lean_inc(x_1325);
lean_dec(x_1324);
x_1326 = lean_st_ref_get(x_3, x_1325);
x_1327 = lean_ctor_get(x_1326, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1326, 1);
lean_inc(x_1328);
lean_dec(x_1326);
x_1275 = x_1327;
x_1276 = x_1328;
goto block_1319;
}
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; 
x_1329 = lean_st_ref_get(x_7, x_8);
x_1330 = lean_ctor_get(x_1329, 1);
lean_inc(x_1330);
lean_dec(x_1329);
x_1331 = lean_st_ref_get(x_3, x_1330);
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1275 = x_1332;
x_1276 = x_1333;
goto block_1319;
}
}
else
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
x_1334 = lean_st_ref_get(x_7, x_8);
x_1335 = lean_ctor_get(x_1334, 1);
lean_inc(x_1335);
lean_dec(x_1334);
x_1336 = lean_st_ref_get(x_3, x_1335);
x_1337 = lean_ctor_get(x_1336, 0);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1336, 1);
lean_inc(x_1338);
lean_dec(x_1336);
x_1275 = x_1337;
x_1276 = x_1338;
goto block_1319;
}
block_1274:
{
if (lean_obj_tag(x_1090) == 0)
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1206; lean_object* x_1207; uint8_t x_1251; 
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
x_1251 = l_Lean_Expr_hasLevelParam(x_1088);
if (x_1251 == 0)
{
uint8_t x_1252; 
x_1252 = l_Lean_Expr_hasFVar(x_1088);
if (x_1252 == 0)
{
uint8_t x_1253; 
x_1253 = l_Lean_Expr_hasMVar(x_1088);
if (x_1253 == 0)
{
lean_object* x_1254; 
x_1254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1254, 0, x_1088);
lean_ctor_set(x_1254, 1, x_1092);
x_1094 = x_1254;
goto block_1205;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1255 = lean_st_ref_get(x_7, x_1092);
x_1256 = lean_ctor_get(x_1255, 1);
lean_inc(x_1256);
lean_dec(x_1255);
x_1257 = lean_st_ref_get(x_3, x_1256);
x_1258 = lean_ctor_get(x_1257, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1257, 1);
lean_inc(x_1259);
lean_dec(x_1257);
x_1206 = x_1258;
x_1207 = x_1259;
goto block_1250;
}
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1260 = lean_st_ref_get(x_7, x_1092);
x_1261 = lean_ctor_get(x_1260, 1);
lean_inc(x_1261);
lean_dec(x_1260);
x_1262 = lean_st_ref_get(x_3, x_1261);
x_1263 = lean_ctor_get(x_1262, 0);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_1262, 1);
lean_inc(x_1264);
lean_dec(x_1262);
x_1206 = x_1263;
x_1207 = x_1264;
goto block_1250;
}
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1265 = lean_st_ref_get(x_7, x_1092);
x_1266 = lean_ctor_get(x_1265, 1);
lean_inc(x_1266);
lean_dec(x_1265);
x_1267 = lean_st_ref_get(x_3, x_1266);
x_1268 = lean_ctor_get(x_1267, 0);
lean_inc(x_1268);
x_1269 = lean_ctor_get(x_1267, 1);
lean_inc(x_1269);
lean_dec(x_1267);
x_1206 = x_1268;
x_1207 = x_1269;
goto block_1250;
}
block_1205:
{
if (lean_obj_tag(x_1094) == 0)
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1137; lean_object* x_1138; uint8_t x_1182; 
x_1095 = lean_ctor_get(x_1094, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1094, 1);
lean_inc(x_1096);
if (lean_is_exclusive(x_1094)) {
 lean_ctor_release(x_1094, 0);
 lean_ctor_release(x_1094, 1);
 x_1097 = x_1094;
} else {
 lean_dec_ref(x_1094);
 x_1097 = lean_box(0);
}
x_1182 = l_Lean_Expr_hasLevelParam(x_1089);
if (x_1182 == 0)
{
uint8_t x_1183; 
x_1183 = l_Lean_Expr_hasFVar(x_1089);
if (x_1183 == 0)
{
uint8_t x_1184; 
x_1184 = l_Lean_Expr_hasMVar(x_1089);
if (x_1184 == 0)
{
lean_object* x_1185; 
lean_dec(x_1097);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_1093)) {
 x_1185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1185 = x_1093;
}
lean_ctor_set(x_1185, 0, x_1089);
lean_ctor_set(x_1185, 1, x_1096);
x_1098 = x_1185;
goto block_1136;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
lean_dec(x_1093);
x_1186 = lean_st_ref_get(x_7, x_1096);
x_1187 = lean_ctor_get(x_1186, 1);
lean_inc(x_1187);
lean_dec(x_1186);
x_1188 = lean_st_ref_get(x_3, x_1187);
x_1189 = lean_ctor_get(x_1188, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1188, 1);
lean_inc(x_1190);
lean_dec(x_1188);
x_1137 = x_1189;
x_1138 = x_1190;
goto block_1181;
}
}
else
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
lean_dec(x_1093);
x_1191 = lean_st_ref_get(x_7, x_1096);
x_1192 = lean_ctor_get(x_1191, 1);
lean_inc(x_1192);
lean_dec(x_1191);
x_1193 = lean_st_ref_get(x_3, x_1192);
x_1194 = lean_ctor_get(x_1193, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1193, 1);
lean_inc(x_1195);
lean_dec(x_1193);
x_1137 = x_1194;
x_1138 = x_1195;
goto block_1181;
}
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_1093);
x_1196 = lean_st_ref_get(x_7, x_1096);
x_1197 = lean_ctor_get(x_1196, 1);
lean_inc(x_1197);
lean_dec(x_1196);
x_1198 = lean_st_ref_get(x_3, x_1197);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
lean_dec(x_1198);
x_1137 = x_1199;
x_1138 = x_1200;
goto block_1181;
}
block_1136:
{
if (lean_obj_tag(x_1098) == 0)
{
if (lean_obj_tag(x_1) == 8)
{
uint8_t x_1099; 
x_1099 = !lean_is_exclusive(x_1098);
if (x_1099 == 0)
{
uint8_t x_1100; 
x_1100 = !lean_is_exclusive(x_1);
if (x_1100 == 0)
{
lean_object* x_1101; lean_object* x_1102; 
x_1101 = lean_ctor_get(x_1098, 0);
x_1102 = lean_expr_update_let(x_1, x_1091, x_1095, x_1101);
lean_ctor_set(x_1098, 0, x_1102);
return x_1098;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; uint64_t x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1103 = lean_ctor_get(x_1098, 0);
x_1104 = lean_ctor_get(x_1, 0);
x_1105 = lean_ctor_get(x_1, 1);
x_1106 = lean_ctor_get(x_1, 2);
x_1107 = lean_ctor_get(x_1, 3);
x_1108 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_1107);
lean_inc(x_1106);
lean_inc(x_1105);
lean_inc(x_1104);
lean_dec(x_1);
x_1109 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_1109, 0, x_1104);
lean_ctor_set(x_1109, 1, x_1105);
lean_ctor_set(x_1109, 2, x_1106);
lean_ctor_set(x_1109, 3, x_1107);
lean_ctor_set_uint64(x_1109, sizeof(void*)*4, x_1108);
x_1110 = lean_expr_update_let(x_1109, x_1091, x_1095, x_1103);
lean_ctor_set(x_1098, 0, x_1110);
return x_1098;
}
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; uint64_t x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1111 = lean_ctor_get(x_1098, 0);
x_1112 = lean_ctor_get(x_1098, 1);
lean_inc(x_1112);
lean_inc(x_1111);
lean_dec(x_1098);
x_1113 = lean_ctor_get(x_1, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1, 1);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1, 2);
lean_inc(x_1115);
x_1116 = lean_ctor_get(x_1, 3);
lean_inc(x_1116);
x_1117 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1118 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1118 = lean_box(0);
}
if (lean_is_scalar(x_1118)) {
 x_1119 = lean_alloc_ctor(8, 4, 8);
} else {
 x_1119 = x_1118;
}
lean_ctor_set(x_1119, 0, x_1113);
lean_ctor_set(x_1119, 1, x_1114);
lean_ctor_set(x_1119, 2, x_1115);
lean_ctor_set(x_1119, 3, x_1116);
lean_ctor_set_uint64(x_1119, sizeof(void*)*4, x_1117);
x_1120 = lean_expr_update_let(x_1119, x_1091, x_1095, x_1111);
x_1121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1121, 0, x_1120);
lean_ctor_set(x_1121, 1, x_1112);
return x_1121;
}
}
else
{
uint8_t x_1122; 
lean_dec(x_1095);
lean_dec(x_1091);
lean_dec(x_1);
x_1122 = !lean_is_exclusive(x_1098);
if (x_1122 == 0)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1123 = lean_ctor_get(x_1098, 0);
lean_dec(x_1123);
x_1124 = l_Lean_instInhabitedExpr;
x_1125 = l_Lean_Expr_updateLet_x21___closed__2;
x_1126 = lean_panic_fn(x_1124, x_1125);
lean_ctor_set(x_1098, 0, x_1126);
return x_1098;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1127 = lean_ctor_get(x_1098, 1);
lean_inc(x_1127);
lean_dec(x_1098);
x_1128 = l_Lean_instInhabitedExpr;
x_1129 = l_Lean_Expr_updateLet_x21___closed__2;
x_1130 = lean_panic_fn(x_1128, x_1129);
x_1131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1131, 0, x_1130);
lean_ctor_set(x_1131, 1, x_1127);
return x_1131;
}
}
}
else
{
uint8_t x_1132; 
lean_dec(x_1095);
lean_dec(x_1091);
lean_dec(x_1);
x_1132 = !lean_is_exclusive(x_1098);
if (x_1132 == 0)
{
return x_1098;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1133 = lean_ctor_get(x_1098, 0);
x_1134 = lean_ctor_get(x_1098, 1);
lean_inc(x_1134);
lean_inc(x_1133);
lean_dec(x_1098);
x_1135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1135, 0, x_1133);
lean_ctor_set(x_1135, 1, x_1134);
return x_1135;
}
}
}
block_1181:
{
lean_object* x_1139; lean_object* x_1140; 
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
x_1140 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1139, x_1089);
lean_dec(x_1139);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; 
lean_dec(x_1097);
lean_inc(x_7);
lean_inc(x_1089);
x_1141 = l_Lean_Meta_Closure_collectExprAux(x_1089, x_2, x_3, x_4, x_5, x_6, x_7, x_1138);
if (lean_obj_tag(x_1141) == 0)
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; uint8_t x_1149; 
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1141, 1);
lean_inc(x_1143);
lean_dec(x_1141);
x_1144 = lean_st_ref_get(x_7, x_1143);
lean_dec(x_7);
x_1145 = lean_ctor_get(x_1144, 1);
lean_inc(x_1145);
lean_dec(x_1144);
x_1146 = lean_st_ref_take(x_3, x_1145);
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1146, 1);
lean_inc(x_1148);
lean_dec(x_1146);
x_1149 = !lean_is_exclusive(x_1147);
if (x_1149 == 0)
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; uint8_t x_1153; 
x_1150 = lean_ctor_get(x_1147, 1);
lean_inc(x_1142);
x_1151 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1150, x_1089, x_1142);
lean_ctor_set(x_1147, 1, x_1151);
x_1152 = lean_st_ref_set(x_3, x_1147, x_1148);
x_1153 = !lean_is_exclusive(x_1152);
if (x_1153 == 0)
{
lean_object* x_1154; 
x_1154 = lean_ctor_get(x_1152, 0);
lean_dec(x_1154);
lean_ctor_set(x_1152, 0, x_1142);
x_1098 = x_1152;
goto block_1136;
}
else
{
lean_object* x_1155; lean_object* x_1156; 
x_1155 = lean_ctor_get(x_1152, 1);
lean_inc(x_1155);
lean_dec(x_1152);
x_1156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1156, 0, x_1142);
lean_ctor_set(x_1156, 1, x_1155);
x_1098 = x_1156;
goto block_1136;
}
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
x_1157 = lean_ctor_get(x_1147, 0);
x_1158 = lean_ctor_get(x_1147, 1);
x_1159 = lean_ctor_get(x_1147, 2);
x_1160 = lean_ctor_get(x_1147, 3);
x_1161 = lean_ctor_get(x_1147, 4);
x_1162 = lean_ctor_get(x_1147, 5);
x_1163 = lean_ctor_get(x_1147, 6);
x_1164 = lean_ctor_get(x_1147, 7);
x_1165 = lean_ctor_get(x_1147, 8);
x_1166 = lean_ctor_get(x_1147, 9);
x_1167 = lean_ctor_get(x_1147, 10);
x_1168 = lean_ctor_get(x_1147, 11);
lean_inc(x_1168);
lean_inc(x_1167);
lean_inc(x_1166);
lean_inc(x_1165);
lean_inc(x_1164);
lean_inc(x_1163);
lean_inc(x_1162);
lean_inc(x_1161);
lean_inc(x_1160);
lean_inc(x_1159);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_1147);
lean_inc(x_1142);
x_1169 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1158, x_1089, x_1142);
x_1170 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1170, 0, x_1157);
lean_ctor_set(x_1170, 1, x_1169);
lean_ctor_set(x_1170, 2, x_1159);
lean_ctor_set(x_1170, 3, x_1160);
lean_ctor_set(x_1170, 4, x_1161);
lean_ctor_set(x_1170, 5, x_1162);
lean_ctor_set(x_1170, 6, x_1163);
lean_ctor_set(x_1170, 7, x_1164);
lean_ctor_set(x_1170, 8, x_1165);
lean_ctor_set(x_1170, 9, x_1166);
lean_ctor_set(x_1170, 10, x_1167);
lean_ctor_set(x_1170, 11, x_1168);
x_1171 = lean_st_ref_set(x_3, x_1170, x_1148);
x_1172 = lean_ctor_get(x_1171, 1);
lean_inc(x_1172);
if (lean_is_exclusive(x_1171)) {
 lean_ctor_release(x_1171, 0);
 lean_ctor_release(x_1171, 1);
 x_1173 = x_1171;
} else {
 lean_dec_ref(x_1171);
 x_1173 = lean_box(0);
}
if (lean_is_scalar(x_1173)) {
 x_1174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1174 = x_1173;
}
lean_ctor_set(x_1174, 0, x_1142);
lean_ctor_set(x_1174, 1, x_1172);
x_1098 = x_1174;
goto block_1136;
}
}
else
{
uint8_t x_1175; 
lean_dec(x_1089);
lean_dec(x_7);
x_1175 = !lean_is_exclusive(x_1141);
if (x_1175 == 0)
{
x_1098 = x_1141;
goto block_1136;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1176 = lean_ctor_get(x_1141, 0);
x_1177 = lean_ctor_get(x_1141, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1141);
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_1177);
x_1098 = x_1178;
goto block_1136;
}
}
}
else
{
lean_object* x_1179; lean_object* x_1180; 
lean_dec(x_1089);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1179 = lean_ctor_get(x_1140, 0);
lean_inc(x_1179);
lean_dec(x_1140);
if (lean_is_scalar(x_1097)) {
 x_1180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1180 = x_1097;
}
lean_ctor_set(x_1180, 0, x_1179);
lean_ctor_set(x_1180, 1, x_1138);
x_1098 = x_1180;
goto block_1136;
}
}
}
else
{
uint8_t x_1201; 
lean_dec(x_1093);
lean_dec(x_1091);
lean_dec(x_1089);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1201 = !lean_is_exclusive(x_1094);
if (x_1201 == 0)
{
return x_1094;
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1202 = lean_ctor_get(x_1094, 0);
x_1203 = lean_ctor_get(x_1094, 1);
lean_inc(x_1203);
lean_inc(x_1202);
lean_dec(x_1094);
x_1204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1204, 0, x_1202);
lean_ctor_set(x_1204, 1, x_1203);
return x_1204;
}
}
}
block_1250:
{
lean_object* x_1208; lean_object* x_1209; 
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1209 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1208, x_1088);
lean_dec(x_1208);
if (lean_obj_tag(x_1209) == 0)
{
lean_object* x_1210; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1088);
x_1210 = l_Lean_Meta_Closure_collectExprAux(x_1088, x_2, x_3, x_4, x_5, x_6, x_7, x_1207);
if (lean_obj_tag(x_1210) == 0)
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; uint8_t x_1218; 
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1210, 1);
lean_inc(x_1212);
lean_dec(x_1210);
x_1213 = lean_st_ref_get(x_7, x_1212);
x_1214 = lean_ctor_get(x_1213, 1);
lean_inc(x_1214);
lean_dec(x_1213);
x_1215 = lean_st_ref_take(x_3, x_1214);
x_1216 = lean_ctor_get(x_1215, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1215, 1);
lean_inc(x_1217);
lean_dec(x_1215);
x_1218 = !lean_is_exclusive(x_1216);
if (x_1218 == 0)
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; 
x_1219 = lean_ctor_get(x_1216, 1);
lean_inc(x_1211);
x_1220 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1219, x_1088, x_1211);
lean_ctor_set(x_1216, 1, x_1220);
x_1221 = lean_st_ref_set(x_3, x_1216, x_1217);
x_1222 = !lean_is_exclusive(x_1221);
if (x_1222 == 0)
{
lean_object* x_1223; 
x_1223 = lean_ctor_get(x_1221, 0);
lean_dec(x_1223);
lean_ctor_set(x_1221, 0, x_1211);
x_1094 = x_1221;
goto block_1205;
}
else
{
lean_object* x_1224; lean_object* x_1225; 
x_1224 = lean_ctor_get(x_1221, 1);
lean_inc(x_1224);
lean_dec(x_1221);
x_1225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1225, 0, x_1211);
lean_ctor_set(x_1225, 1, x_1224);
x_1094 = x_1225;
goto block_1205;
}
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1226 = lean_ctor_get(x_1216, 0);
x_1227 = lean_ctor_get(x_1216, 1);
x_1228 = lean_ctor_get(x_1216, 2);
x_1229 = lean_ctor_get(x_1216, 3);
x_1230 = lean_ctor_get(x_1216, 4);
x_1231 = lean_ctor_get(x_1216, 5);
x_1232 = lean_ctor_get(x_1216, 6);
x_1233 = lean_ctor_get(x_1216, 7);
x_1234 = lean_ctor_get(x_1216, 8);
x_1235 = lean_ctor_get(x_1216, 9);
x_1236 = lean_ctor_get(x_1216, 10);
x_1237 = lean_ctor_get(x_1216, 11);
lean_inc(x_1237);
lean_inc(x_1236);
lean_inc(x_1235);
lean_inc(x_1234);
lean_inc(x_1233);
lean_inc(x_1232);
lean_inc(x_1231);
lean_inc(x_1230);
lean_inc(x_1229);
lean_inc(x_1228);
lean_inc(x_1227);
lean_inc(x_1226);
lean_dec(x_1216);
lean_inc(x_1211);
x_1238 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1227, x_1088, x_1211);
x_1239 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1239, 0, x_1226);
lean_ctor_set(x_1239, 1, x_1238);
lean_ctor_set(x_1239, 2, x_1228);
lean_ctor_set(x_1239, 3, x_1229);
lean_ctor_set(x_1239, 4, x_1230);
lean_ctor_set(x_1239, 5, x_1231);
lean_ctor_set(x_1239, 6, x_1232);
lean_ctor_set(x_1239, 7, x_1233);
lean_ctor_set(x_1239, 8, x_1234);
lean_ctor_set(x_1239, 9, x_1235);
lean_ctor_set(x_1239, 10, x_1236);
lean_ctor_set(x_1239, 11, x_1237);
x_1240 = lean_st_ref_set(x_3, x_1239, x_1217);
x_1241 = lean_ctor_get(x_1240, 1);
lean_inc(x_1241);
if (lean_is_exclusive(x_1240)) {
 lean_ctor_release(x_1240, 0);
 lean_ctor_release(x_1240, 1);
 x_1242 = x_1240;
} else {
 lean_dec_ref(x_1240);
 x_1242 = lean_box(0);
}
if (lean_is_scalar(x_1242)) {
 x_1243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1243 = x_1242;
}
lean_ctor_set(x_1243, 0, x_1211);
lean_ctor_set(x_1243, 1, x_1241);
x_1094 = x_1243;
goto block_1205;
}
}
else
{
uint8_t x_1244; 
lean_dec(x_1088);
x_1244 = !lean_is_exclusive(x_1210);
if (x_1244 == 0)
{
x_1094 = x_1210;
goto block_1205;
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1245 = lean_ctor_get(x_1210, 0);
x_1246 = lean_ctor_get(x_1210, 1);
lean_inc(x_1246);
lean_inc(x_1245);
lean_dec(x_1210);
x_1247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
x_1094 = x_1247;
goto block_1205;
}
}
}
else
{
lean_object* x_1248; lean_object* x_1249; 
lean_dec(x_1088);
x_1248 = lean_ctor_get(x_1209, 0);
lean_inc(x_1248);
lean_dec(x_1209);
x_1249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1249, 0, x_1248);
lean_ctor_set(x_1249, 1, x_1207);
x_1094 = x_1249;
goto block_1205;
}
}
}
else
{
uint8_t x_1270; 
lean_dec(x_1089);
lean_dec(x_1088);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1270 = !lean_is_exclusive(x_1090);
if (x_1270 == 0)
{
return x_1090;
}
else
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1271 = lean_ctor_get(x_1090, 0);
x_1272 = lean_ctor_get(x_1090, 1);
lean_inc(x_1272);
lean_inc(x_1271);
lean_dec(x_1090);
x_1273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1273, 0, x_1271);
lean_ctor_set(x_1273, 1, x_1272);
return x_1273;
}
}
}
block_1319:
{
lean_object* x_1277; lean_object* x_1278; 
x_1277 = lean_ctor_get(x_1275, 1);
lean_inc(x_1277);
lean_dec(x_1275);
x_1278 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1277, x_1087);
lean_dec(x_1277);
if (lean_obj_tag(x_1278) == 0)
{
lean_object* x_1279; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1087);
x_1279 = l_Lean_Meta_Closure_collectExprAux(x_1087, x_2, x_3, x_4, x_5, x_6, x_7, x_1276);
if (lean_obj_tag(x_1279) == 0)
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; uint8_t x_1287; 
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1279, 1);
lean_inc(x_1281);
lean_dec(x_1279);
x_1282 = lean_st_ref_get(x_7, x_1281);
x_1283 = lean_ctor_get(x_1282, 1);
lean_inc(x_1283);
lean_dec(x_1282);
x_1284 = lean_st_ref_take(x_3, x_1283);
x_1285 = lean_ctor_get(x_1284, 0);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1284, 1);
lean_inc(x_1286);
lean_dec(x_1284);
x_1287 = !lean_is_exclusive(x_1285);
if (x_1287 == 0)
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; uint8_t x_1291; 
x_1288 = lean_ctor_get(x_1285, 1);
lean_inc(x_1280);
x_1289 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1288, x_1087, x_1280);
lean_ctor_set(x_1285, 1, x_1289);
x_1290 = lean_st_ref_set(x_3, x_1285, x_1286);
x_1291 = !lean_is_exclusive(x_1290);
if (x_1291 == 0)
{
lean_object* x_1292; 
x_1292 = lean_ctor_get(x_1290, 0);
lean_dec(x_1292);
lean_ctor_set(x_1290, 0, x_1280);
x_1090 = x_1290;
goto block_1274;
}
else
{
lean_object* x_1293; lean_object* x_1294; 
x_1293 = lean_ctor_get(x_1290, 1);
lean_inc(x_1293);
lean_dec(x_1290);
x_1294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1294, 0, x_1280);
lean_ctor_set(x_1294, 1, x_1293);
x_1090 = x_1294;
goto block_1274;
}
}
else
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1295 = lean_ctor_get(x_1285, 0);
x_1296 = lean_ctor_get(x_1285, 1);
x_1297 = lean_ctor_get(x_1285, 2);
x_1298 = lean_ctor_get(x_1285, 3);
x_1299 = lean_ctor_get(x_1285, 4);
x_1300 = lean_ctor_get(x_1285, 5);
x_1301 = lean_ctor_get(x_1285, 6);
x_1302 = lean_ctor_get(x_1285, 7);
x_1303 = lean_ctor_get(x_1285, 8);
x_1304 = lean_ctor_get(x_1285, 9);
x_1305 = lean_ctor_get(x_1285, 10);
x_1306 = lean_ctor_get(x_1285, 11);
lean_inc(x_1306);
lean_inc(x_1305);
lean_inc(x_1304);
lean_inc(x_1303);
lean_inc(x_1302);
lean_inc(x_1301);
lean_inc(x_1300);
lean_inc(x_1299);
lean_inc(x_1298);
lean_inc(x_1297);
lean_inc(x_1296);
lean_inc(x_1295);
lean_dec(x_1285);
lean_inc(x_1280);
x_1307 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1296, x_1087, x_1280);
x_1308 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1308, 0, x_1295);
lean_ctor_set(x_1308, 1, x_1307);
lean_ctor_set(x_1308, 2, x_1297);
lean_ctor_set(x_1308, 3, x_1298);
lean_ctor_set(x_1308, 4, x_1299);
lean_ctor_set(x_1308, 5, x_1300);
lean_ctor_set(x_1308, 6, x_1301);
lean_ctor_set(x_1308, 7, x_1302);
lean_ctor_set(x_1308, 8, x_1303);
lean_ctor_set(x_1308, 9, x_1304);
lean_ctor_set(x_1308, 10, x_1305);
lean_ctor_set(x_1308, 11, x_1306);
x_1309 = lean_st_ref_set(x_3, x_1308, x_1286);
x_1310 = lean_ctor_get(x_1309, 1);
lean_inc(x_1310);
if (lean_is_exclusive(x_1309)) {
 lean_ctor_release(x_1309, 0);
 lean_ctor_release(x_1309, 1);
 x_1311 = x_1309;
} else {
 lean_dec_ref(x_1309);
 x_1311 = lean_box(0);
}
if (lean_is_scalar(x_1311)) {
 x_1312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1312 = x_1311;
}
lean_ctor_set(x_1312, 0, x_1280);
lean_ctor_set(x_1312, 1, x_1310);
x_1090 = x_1312;
goto block_1274;
}
}
else
{
uint8_t x_1313; 
lean_dec(x_1087);
x_1313 = !lean_is_exclusive(x_1279);
if (x_1313 == 0)
{
x_1090 = x_1279;
goto block_1274;
}
else
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1314 = lean_ctor_get(x_1279, 0);
x_1315 = lean_ctor_get(x_1279, 1);
lean_inc(x_1315);
lean_inc(x_1314);
lean_dec(x_1279);
x_1316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1316, 0, x_1314);
lean_ctor_set(x_1316, 1, x_1315);
x_1090 = x_1316;
goto block_1274;
}
}
}
else
{
lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_1087);
x_1317 = lean_ctor_get(x_1278, 0);
lean_inc(x_1317);
lean_dec(x_1278);
x_1318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1318, 0, x_1317);
lean_ctor_set(x_1318, 1, x_1276);
x_1090 = x_1318;
goto block_1274;
}
}
}
case 10:
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; uint8_t x_1385; 
x_1339 = lean_ctor_get(x_1, 1);
lean_inc(x_1339);
x_1385 = l_Lean_Expr_hasLevelParam(x_1339);
if (x_1385 == 0)
{
uint8_t x_1386; 
x_1386 = l_Lean_Expr_hasFVar(x_1339);
if (x_1386 == 0)
{
uint8_t x_1387; 
x_1387 = l_Lean_Expr_hasMVar(x_1339);
if (x_1387 == 0)
{
lean_object* x_1388; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1388, 0, x_1339);
lean_ctor_set(x_1388, 1, x_8);
x_9 = x_1388;
goto block_43;
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1389 = lean_st_ref_get(x_7, x_8);
x_1390 = lean_ctor_get(x_1389, 1);
lean_inc(x_1390);
lean_dec(x_1389);
x_1391 = lean_st_ref_get(x_3, x_1390);
x_1392 = lean_ctor_get(x_1391, 0);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1391, 1);
lean_inc(x_1393);
lean_dec(x_1391);
x_1340 = x_1392;
x_1341 = x_1393;
goto block_1384;
}
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
x_1394 = lean_st_ref_get(x_7, x_8);
x_1395 = lean_ctor_get(x_1394, 1);
lean_inc(x_1395);
lean_dec(x_1394);
x_1396 = lean_st_ref_get(x_3, x_1395);
x_1397 = lean_ctor_get(x_1396, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1396, 1);
lean_inc(x_1398);
lean_dec(x_1396);
x_1340 = x_1397;
x_1341 = x_1398;
goto block_1384;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1399 = lean_st_ref_get(x_7, x_8);
x_1400 = lean_ctor_get(x_1399, 1);
lean_inc(x_1400);
lean_dec(x_1399);
x_1401 = lean_st_ref_get(x_3, x_1400);
x_1402 = lean_ctor_get(x_1401, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1401, 1);
lean_inc(x_1403);
lean_dec(x_1401);
x_1340 = x_1402;
x_1341 = x_1403;
goto block_1384;
}
block_1384:
{
lean_object* x_1342; lean_object* x_1343; 
x_1342 = lean_ctor_get(x_1340, 1);
lean_inc(x_1342);
lean_dec(x_1340);
x_1343 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1342, x_1339);
lean_dec(x_1342);
if (lean_obj_tag(x_1343) == 0)
{
lean_object* x_1344; 
lean_inc(x_7);
lean_inc(x_1339);
x_1344 = l_Lean_Meta_Closure_collectExprAux(x_1339, x_2, x_3, x_4, x_5, x_6, x_7, x_1341);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; 
x_1345 = lean_ctor_get(x_1344, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1344, 1);
lean_inc(x_1346);
lean_dec(x_1344);
x_1347 = lean_st_ref_get(x_7, x_1346);
lean_dec(x_7);
x_1348 = lean_ctor_get(x_1347, 1);
lean_inc(x_1348);
lean_dec(x_1347);
x_1349 = lean_st_ref_take(x_3, x_1348);
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1349, 1);
lean_inc(x_1351);
lean_dec(x_1349);
x_1352 = !lean_is_exclusive(x_1350);
if (x_1352 == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; uint8_t x_1356; 
x_1353 = lean_ctor_get(x_1350, 1);
lean_inc(x_1345);
x_1354 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1353, x_1339, x_1345);
lean_ctor_set(x_1350, 1, x_1354);
x_1355 = lean_st_ref_set(x_3, x_1350, x_1351);
x_1356 = !lean_is_exclusive(x_1355);
if (x_1356 == 0)
{
lean_object* x_1357; 
x_1357 = lean_ctor_get(x_1355, 0);
lean_dec(x_1357);
lean_ctor_set(x_1355, 0, x_1345);
x_9 = x_1355;
goto block_43;
}
else
{
lean_object* x_1358; lean_object* x_1359; 
x_1358 = lean_ctor_get(x_1355, 1);
lean_inc(x_1358);
lean_dec(x_1355);
x_1359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1359, 0, x_1345);
lean_ctor_set(x_1359, 1, x_1358);
x_9 = x_1359;
goto block_43;
}
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1360 = lean_ctor_get(x_1350, 0);
x_1361 = lean_ctor_get(x_1350, 1);
x_1362 = lean_ctor_get(x_1350, 2);
x_1363 = lean_ctor_get(x_1350, 3);
x_1364 = lean_ctor_get(x_1350, 4);
x_1365 = lean_ctor_get(x_1350, 5);
x_1366 = lean_ctor_get(x_1350, 6);
x_1367 = lean_ctor_get(x_1350, 7);
x_1368 = lean_ctor_get(x_1350, 8);
x_1369 = lean_ctor_get(x_1350, 9);
x_1370 = lean_ctor_get(x_1350, 10);
x_1371 = lean_ctor_get(x_1350, 11);
lean_inc(x_1371);
lean_inc(x_1370);
lean_inc(x_1369);
lean_inc(x_1368);
lean_inc(x_1367);
lean_inc(x_1366);
lean_inc(x_1365);
lean_inc(x_1364);
lean_inc(x_1363);
lean_inc(x_1362);
lean_inc(x_1361);
lean_inc(x_1360);
lean_dec(x_1350);
lean_inc(x_1345);
x_1372 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1361, x_1339, x_1345);
x_1373 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1373, 0, x_1360);
lean_ctor_set(x_1373, 1, x_1372);
lean_ctor_set(x_1373, 2, x_1362);
lean_ctor_set(x_1373, 3, x_1363);
lean_ctor_set(x_1373, 4, x_1364);
lean_ctor_set(x_1373, 5, x_1365);
lean_ctor_set(x_1373, 6, x_1366);
lean_ctor_set(x_1373, 7, x_1367);
lean_ctor_set(x_1373, 8, x_1368);
lean_ctor_set(x_1373, 9, x_1369);
lean_ctor_set(x_1373, 10, x_1370);
lean_ctor_set(x_1373, 11, x_1371);
x_1374 = lean_st_ref_set(x_3, x_1373, x_1351);
x_1375 = lean_ctor_get(x_1374, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1376 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_1345);
lean_ctor_set(x_1377, 1, x_1375);
x_9 = x_1377;
goto block_43;
}
}
else
{
uint8_t x_1378; 
lean_dec(x_1339);
lean_dec(x_7);
x_1378 = !lean_is_exclusive(x_1344);
if (x_1378 == 0)
{
x_9 = x_1344;
goto block_43;
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1379 = lean_ctor_get(x_1344, 0);
x_1380 = lean_ctor_get(x_1344, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1344);
x_1381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1381, 0, x_1379);
lean_ctor_set(x_1381, 1, x_1380);
x_9 = x_1381;
goto block_43;
}
}
}
else
{
lean_object* x_1382; lean_object* x_1383; 
lean_dec(x_1339);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1382 = lean_ctor_get(x_1343, 0);
lean_inc(x_1382);
lean_dec(x_1343);
x_1383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1383, 0, x_1382);
lean_ctor_set(x_1383, 1, x_1341);
x_9 = x_1383;
goto block_43;
}
}
}
case 11:
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; uint8_t x_1450; 
x_1404 = lean_ctor_get(x_1, 2);
lean_inc(x_1404);
x_1450 = l_Lean_Expr_hasLevelParam(x_1404);
if (x_1450 == 0)
{
uint8_t x_1451; 
x_1451 = l_Lean_Expr_hasFVar(x_1404);
if (x_1451 == 0)
{
uint8_t x_1452; 
x_1452 = l_Lean_Expr_hasMVar(x_1404);
if (x_1452 == 0)
{
lean_object* x_1453; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1453, 0, x_1404);
lean_ctor_set(x_1453, 1, x_8);
x_44 = x_1453;
goto block_80;
}
else
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1454 = lean_st_ref_get(x_7, x_8);
x_1455 = lean_ctor_get(x_1454, 1);
lean_inc(x_1455);
lean_dec(x_1454);
x_1456 = lean_st_ref_get(x_3, x_1455);
x_1457 = lean_ctor_get(x_1456, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1456, 1);
lean_inc(x_1458);
lean_dec(x_1456);
x_1405 = x_1457;
x_1406 = x_1458;
goto block_1449;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
x_1459 = lean_st_ref_get(x_7, x_8);
x_1460 = lean_ctor_get(x_1459, 1);
lean_inc(x_1460);
lean_dec(x_1459);
x_1461 = lean_st_ref_get(x_3, x_1460);
x_1462 = lean_ctor_get(x_1461, 0);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1461, 1);
lean_inc(x_1463);
lean_dec(x_1461);
x_1405 = x_1462;
x_1406 = x_1463;
goto block_1449;
}
}
else
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; 
x_1464 = lean_st_ref_get(x_7, x_8);
x_1465 = lean_ctor_get(x_1464, 1);
lean_inc(x_1465);
lean_dec(x_1464);
x_1466 = lean_st_ref_get(x_3, x_1465);
x_1467 = lean_ctor_get(x_1466, 0);
lean_inc(x_1467);
x_1468 = lean_ctor_get(x_1466, 1);
lean_inc(x_1468);
lean_dec(x_1466);
x_1405 = x_1467;
x_1406 = x_1468;
goto block_1449;
}
block_1449:
{
lean_object* x_1407; lean_object* x_1408; 
x_1407 = lean_ctor_get(x_1405, 1);
lean_inc(x_1407);
lean_dec(x_1405);
x_1408 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1407, x_1404);
lean_dec(x_1407);
if (lean_obj_tag(x_1408) == 0)
{
lean_object* x_1409; 
lean_inc(x_7);
lean_inc(x_1404);
x_1409 = l_Lean_Meta_Closure_collectExprAux(x_1404, x_2, x_3, x_4, x_5, x_6, x_7, x_1406);
if (lean_obj_tag(x_1409) == 0)
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; uint8_t x_1417; 
x_1410 = lean_ctor_get(x_1409, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1409, 1);
lean_inc(x_1411);
lean_dec(x_1409);
x_1412 = lean_st_ref_get(x_7, x_1411);
lean_dec(x_7);
x_1413 = lean_ctor_get(x_1412, 1);
lean_inc(x_1413);
lean_dec(x_1412);
x_1414 = lean_st_ref_take(x_3, x_1413);
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
lean_dec(x_1414);
x_1417 = !lean_is_exclusive(x_1415);
if (x_1417 == 0)
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; uint8_t x_1421; 
x_1418 = lean_ctor_get(x_1415, 1);
lean_inc(x_1410);
x_1419 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1418, x_1404, x_1410);
lean_ctor_set(x_1415, 1, x_1419);
x_1420 = lean_st_ref_set(x_3, x_1415, x_1416);
x_1421 = !lean_is_exclusive(x_1420);
if (x_1421 == 0)
{
lean_object* x_1422; 
x_1422 = lean_ctor_get(x_1420, 0);
lean_dec(x_1422);
lean_ctor_set(x_1420, 0, x_1410);
x_44 = x_1420;
goto block_80;
}
else
{
lean_object* x_1423; lean_object* x_1424; 
x_1423 = lean_ctor_get(x_1420, 1);
lean_inc(x_1423);
lean_dec(x_1420);
x_1424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1424, 0, x_1410);
lean_ctor_set(x_1424, 1, x_1423);
x_44 = x_1424;
goto block_80;
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1425 = lean_ctor_get(x_1415, 0);
x_1426 = lean_ctor_get(x_1415, 1);
x_1427 = lean_ctor_get(x_1415, 2);
x_1428 = lean_ctor_get(x_1415, 3);
x_1429 = lean_ctor_get(x_1415, 4);
x_1430 = lean_ctor_get(x_1415, 5);
x_1431 = lean_ctor_get(x_1415, 6);
x_1432 = lean_ctor_get(x_1415, 7);
x_1433 = lean_ctor_get(x_1415, 8);
x_1434 = lean_ctor_get(x_1415, 9);
x_1435 = lean_ctor_get(x_1415, 10);
x_1436 = lean_ctor_get(x_1415, 11);
lean_inc(x_1436);
lean_inc(x_1435);
lean_inc(x_1434);
lean_inc(x_1433);
lean_inc(x_1432);
lean_inc(x_1431);
lean_inc(x_1430);
lean_inc(x_1429);
lean_inc(x_1428);
lean_inc(x_1427);
lean_inc(x_1426);
lean_inc(x_1425);
lean_dec(x_1415);
lean_inc(x_1410);
x_1437 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1426, x_1404, x_1410);
x_1438 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1438, 0, x_1425);
lean_ctor_set(x_1438, 1, x_1437);
lean_ctor_set(x_1438, 2, x_1427);
lean_ctor_set(x_1438, 3, x_1428);
lean_ctor_set(x_1438, 4, x_1429);
lean_ctor_set(x_1438, 5, x_1430);
lean_ctor_set(x_1438, 6, x_1431);
lean_ctor_set(x_1438, 7, x_1432);
lean_ctor_set(x_1438, 8, x_1433);
lean_ctor_set(x_1438, 9, x_1434);
lean_ctor_set(x_1438, 10, x_1435);
lean_ctor_set(x_1438, 11, x_1436);
x_1439 = lean_st_ref_set(x_3, x_1438, x_1416);
x_1440 = lean_ctor_get(x_1439, 1);
lean_inc(x_1440);
if (lean_is_exclusive(x_1439)) {
 lean_ctor_release(x_1439, 0);
 lean_ctor_release(x_1439, 1);
 x_1441 = x_1439;
} else {
 lean_dec_ref(x_1439);
 x_1441 = lean_box(0);
}
if (lean_is_scalar(x_1441)) {
 x_1442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1442 = x_1441;
}
lean_ctor_set(x_1442, 0, x_1410);
lean_ctor_set(x_1442, 1, x_1440);
x_44 = x_1442;
goto block_80;
}
}
else
{
uint8_t x_1443; 
lean_dec(x_1404);
lean_dec(x_7);
x_1443 = !lean_is_exclusive(x_1409);
if (x_1443 == 0)
{
x_44 = x_1409;
goto block_80;
}
else
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
x_1444 = lean_ctor_get(x_1409, 0);
x_1445 = lean_ctor_get(x_1409, 1);
lean_inc(x_1445);
lean_inc(x_1444);
lean_dec(x_1409);
x_1446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1446, 0, x_1444);
lean_ctor_set(x_1446, 1, x_1445);
x_44 = x_1446;
goto block_80;
}
}
}
else
{
lean_object* x_1447; lean_object* x_1448; 
lean_dec(x_1404);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1447 = lean_ctor_get(x_1408, 0);
lean_inc(x_1447);
lean_dec(x_1408);
x_1448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1448, 0, x_1447);
lean_ctor_set(x_1448, 1, x_1406);
x_44 = x_1448;
goto block_80;
}
}
}
default: 
{
lean_object* x_1469; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1469, 0, x_1);
lean_ctor_set(x_1469, 1, x_8);
return x_1469;
}
}
block_43:
{
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_expr_update_mdata(x_1, x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_18 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint64(x_18, sizeof(void*)*2, x_17);
x_19 = lean_expr_update_mdata(x_18, x_14);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_25 = x_1;
} else {
 lean_dec_ref(x_1);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(10, 2, 8);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set_uint64(x_26, sizeof(void*)*2, x_24);
x_27 = lean_expr_update_mdata(x_26, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = l_Lean_instInhabitedExpr;
x_32 = l_Lean_Expr_updateMData_x21___closed__3;
x_33 = lean_panic_fn(x_31, x_32);
lean_ctor_set(x_9, 0, x_33);
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
x_35 = l_Lean_instInhabitedExpr;
x_36 = l_Lean_Expr_updateMData_x21___closed__3;
x_37 = lean_panic_fn(x_35, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
block_80:
{
if (lean_obj_tag(x_44) == 0)
{
if (lean_obj_tag(x_1) == 11)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_1);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_expr_update_proj(x_1, x_47);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_54 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set_uint64(x_54, sizeof(void*)*3, x_53);
x_55 = lean_expr_update_proj(x_54, x_49);
lean_ctor_set(x_44, 0, x_55);
return x_44;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_44, 0);
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_44);
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_62 = x_1;
} else {
 lean_dec_ref(x_1);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(11, 3, 8);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set_uint64(x_63, sizeof(void*)*3, x_61);
x_64 = lean_expr_update_proj(x_63, x_56);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_44);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_44, 0);
lean_dec(x_67);
x_68 = l_Lean_instInhabitedExpr;
x_69 = l_Lean_Expr_updateProj_x21___closed__3;
x_70 = lean_panic_fn(x_68, x_69);
lean_ctor_set(x_44, 0, x_70);
return x_44;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_44, 1);
lean_inc(x_71);
lean_dec(x_44);
x_72 = l_Lean_instInhabitedExpr;
x_73 = l_Lean_Expr_updateProj_x21___closed__3;
x_74 = lean_panic_fn(x_72, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_44);
if (x_76 == 0)
{
return x_44;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_44, 0);
x_78 = lean_ctor_get(x_44, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_44);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_58; 
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
x_58 = l_Lean_Expr_hasLevelParam(x_10);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Expr_hasFVar(x_10);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_hasMVar(x_10);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_11);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_st_ref_get(x_7, x_11);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_get(x_3, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_13 = x_65;
x_14 = x_66;
goto block_57;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_st_ref_get(x_7, x_11);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_get(x_3, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_13 = x_70;
x_14 = x_71;
goto block_57;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_st_ref_get(x_7, x_11);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_get(x_3, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_13 = x_75;
x_14 = x_76;
goto block_57;
}
block_57:
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
lean_inc(x_7);
lean_inc(x_10);
x_17 = l_Lean_Meta_Closure_collectExprAux(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_7, x_19);
lean_dec(x_7);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_3, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_18);
x_27 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_26, x_10, x_18);
lean_ctor_set(x_23, 1, x_27);
x_28 = lean_st_ref_set(x_3, x_23, x_24);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_18);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
x_35 = lean_ctor_get(x_23, 2);
x_36 = lean_ctor_get(x_23, 3);
x_37 = lean_ctor_get(x_23, 4);
x_38 = lean_ctor_get(x_23, 5);
x_39 = lean_ctor_get(x_23, 6);
x_40 = lean_ctor_get(x_23, 7);
x_41 = lean_ctor_get(x_23, 8);
x_42 = lean_ctor_get(x_23, 9);
x_43 = lean_ctor_get(x_23, 10);
x_44 = lean_ctor_get(x_23, 11);
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
lean_dec(x_23);
lean_inc(x_18);
x_45 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_34, x_10, x_18);
x_46 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_35);
lean_ctor_set(x_46, 3, x_36);
lean_ctor_set(x_46, 4, x_37);
lean_ctor_set(x_46, 5, x_38);
lean_ctor_set(x_46, 6, x_39);
lean_ctor_set(x_46, 7, x_40);
lean_ctor_set(x_46, 8, x_41);
lean_ctor_set(x_46, 9, x_42);
lean_ctor_set(x_46, 10, x_43);
lean_ctor_set(x_46, 11, x_44);
x_47 = lean_st_ref_set(x_3, x_46, x_24);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_18);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_10);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_ctor_get(x_16, 0);
lean_inc(x_55);
lean_dec(x_16);
if (lean_is_scalar(x_12)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_12;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_14);
return x_56;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
return x_9;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_9, 0);
x_79 = lean_ctor_get(x_9, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_9);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
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
x_5 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 11);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_isEmpty___rarg(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_10);
x_16 = lean_st_ref_get(x_5, x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_19, 11);
x_23 = l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(x_22);
x_24 = lean_array_pop(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_25, x_24, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_19, 11, x_28);
x_30 = lean_st_ref_set(x_1, x_19, x_20);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
x_37 = lean_ctor_get(x_19, 2);
x_38 = lean_ctor_get(x_19, 3);
x_39 = lean_ctor_get(x_19, 4);
x_40 = lean_ctor_get(x_19, 5);
x_41 = lean_ctor_get(x_19, 6);
x_42 = lean_ctor_get(x_19, 7);
x_43 = lean_ctor_get(x_19, 8);
x_44 = lean_ctor_get(x_19, 9);
x_45 = lean_ctor_get(x_19, 10);
x_46 = lean_ctor_get(x_19, 11);
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
lean_dec(x_19);
x_47 = l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(x_46);
x_48 = lean_array_pop(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_49, x_48, x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_36);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_54, 3, x_38);
lean_ctor_set(x_54, 4, x_39);
lean_ctor_set(x_54, 5, x_40);
lean_ctor_set(x_54, 6, x_41);
lean_ctor_set(x_54, 7, x_42);
lean_ctor_set(x_54, 8, x_43);
lean_ctor_set(x_54, 9, x_44);
lean_ctor_set(x_54, 10, x_45);
lean_ctor_set(x_54, 11, x_52);
x_55 = lean_st_ref_set(x_1, x_54, x_20);
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
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_7);
x_59 = lean_box(0);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_10, 0);
x_61 = lean_ctor_get(x_10, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_10);
x_62 = lean_ctor_get(x_60, 11);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Array_isEmpty___rarg(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_64 = lean_st_ref_get(x_5, x_61);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_1, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 6);
lean_inc(x_75);
x_76 = lean_ctor_get(x_67, 7);
lean_inc(x_76);
x_77 = lean_ctor_get(x_67, 8);
lean_inc(x_77);
x_78 = lean_ctor_get(x_67, 9);
lean_inc(x_78);
x_79 = lean_ctor_get(x_67, 10);
lean_inc(x_79);
x_80 = lean_ctor_get(x_67, 11);
lean_inc(x_80);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 lean_ctor_release(x_67, 4);
 lean_ctor_release(x_67, 5);
 lean_ctor_release(x_67, 6);
 lean_ctor_release(x_67, 7);
 lean_ctor_release(x_67, 8);
 lean_ctor_release(x_67, 9);
 lean_ctor_release(x_67, 10);
 lean_ctor_release(x_67, 11);
 x_81 = x_67;
} else {
 lean_dec_ref(x_67);
 x_81 = lean_box(0);
}
x_82 = l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(x_80);
x_83 = lean_array_pop(x_80);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_84, x_83, x_82);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_86);
if (lean_is_scalar(x_81)) {
 x_89 = lean_alloc_ctor(0, 12, 0);
} else {
 x_89 = x_81;
}
lean_ctor_set(x_89, 0, x_69);
lean_ctor_set(x_89, 1, x_70);
lean_ctor_set(x_89, 2, x_71);
lean_ctor_set(x_89, 3, x_72);
lean_ctor_set(x_89, 4, x_73);
lean_ctor_set(x_89, 5, x_74);
lean_ctor_set(x_89, 6, x_75);
lean_ctor_set(x_89, 7, x_76);
lean_ctor_set(x_89, 8, x_77);
lean_ctor_set(x_89, 9, x_78);
lean_ctor_set(x_89, 10, x_79);
lean_ctor_set(x_89, 11, x_87);
x_90 = lean_st_ref_set(x_1, x_89, x_68);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_7);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_61);
return x_95;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 10);
x_16 = lean_array_push(x_15, x_1);
lean_ctor_set(x_12, 10, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
x_30 = lean_ctor_get(x_12, 6);
x_31 = lean_ctor_get(x_12, 7);
x_32 = lean_ctor_get(x_12, 8);
x_33 = lean_ctor_get(x_12, 9);
x_34 = lean_ctor_get(x_12, 10);
x_35 = lean_ctor_get(x_12, 11);
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
lean_inc(x_24);
lean_dec(x_12);
x_36 = lean_array_push(x_34, x_1);
x_37 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set(x_37, 7, x_31);
lean_ctor_set(x_37, 8, x_32);
lean_ctor_set(x_37, 9, x_33);
lean_ctor_set(x_37, 10, x_36);
lean_ctor_set(x_37, 11, x_35);
x_38 = lean_st_ref_set(x_3, x_37, x_13);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
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
lean_inc(x_10);
x_12 = l_Lean_Meta_Closure_collectExpr(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_18, 5);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 2, x_2);
lean_ctor_set(x_23, 3, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_4);
x_24 = lean_array_push(x_21, x_23);
lean_ctor_set(x_18, 5, x_24);
x_25 = lean_st_ref_set(x_6, x_18, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
x_34 = lean_ctor_get(x_18, 2);
x_35 = lean_ctor_get(x_18, 3);
x_36 = lean_ctor_get(x_18, 4);
x_37 = lean_ctor_get(x_18, 5);
x_38 = lean_ctor_get(x_18, 6);
x_39 = lean_ctor_get(x_18, 7);
x_40 = lean_ctor_get(x_18, 8);
x_41 = lean_ctor_get(x_18, 9);
x_42 = lean_ctor_get(x_18, 10);
x_43 = lean_ctor_get(x_18, 11);
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
lean_inc(x_32);
lean_dec(x_18);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_1);
lean_ctor_set(x_45, 2, x_2);
lean_ctor_set(x_45, 3, x_13);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_4);
x_46 = lean_array_push(x_37, x_45);
x_47 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_33);
lean_ctor_set(x_47, 2, x_34);
lean_ctor_set(x_47, 3, x_35);
lean_ctor_set(x_47, 4, x_36);
lean_ctor_set(x_47, 5, x_46);
lean_ctor_set(x_47, 6, x_38);
lean_ctor_set(x_47, 7, x_39);
lean_ctor_set(x_47, 8, x_40);
lean_ctor_set(x_47, 9, x_41);
lean_ctor_set(x_47, 10, x_42);
lean_ctor_set(x_47, 11, x_43);
x_48 = lean_st_ref_set(x_6, x_47, x_19);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
return x_12;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_12);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
lean_inc(x_1);
x_12 = l_Lean_replaceFVarIdAtLocalDecl(x_1, x_2, x_11);
x_13 = 1;
x_14 = x_4 + x_13;
x_15 = x_12;
x_16 = lean_array_uset(x_10, x_4, x_15);
x_4 = x_14;
x_5 = x_16;
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
x_20 = l_Lean_Meta_getLocalDecl(x_18, x_3, x_4, x_5, x_6, x_17);
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
x_43 = l_Lean_Meta_getZetaFVarIds___rarg(x_4, x_5, x_6, x_36);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_6, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_2, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_70 = lean_ctor_get(x_67, 7);
x_71 = lean_unsigned_to_nat(0u);
x_72 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_71);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_72);
x_73 = lean_array_push(x_70, x_21);
lean_ctor_set(x_67, 7, x_73);
x_74 = lean_st_ref_set(x_2, x_67, x_68);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_st_ref_get(x_6, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_take(x_2, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_79, 5);
x_83 = lean_array_get_size(x_82);
x_84 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_85 = 0;
x_86 = x_82;
x_87 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_19, x_62, x_84, x_85, x_86);
lean_dec(x_62);
x_88 = x_87;
lean_ctor_set(x_79, 5, x_88);
x_89 = lean_st_ref_set(x_2, x_79, x_80);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_7 = x_90;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_92 = lean_ctor_get(x_79, 0);
x_93 = lean_ctor_get(x_79, 1);
x_94 = lean_ctor_get(x_79, 2);
x_95 = lean_ctor_get(x_79, 3);
x_96 = lean_ctor_get(x_79, 4);
x_97 = lean_ctor_get(x_79, 5);
x_98 = lean_ctor_get(x_79, 6);
x_99 = lean_ctor_get(x_79, 7);
x_100 = lean_ctor_get(x_79, 8);
x_101 = lean_ctor_get(x_79, 9);
x_102 = lean_ctor_get(x_79, 10);
x_103 = lean_ctor_get(x_79, 11);
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
lean_dec(x_79);
x_104 = lean_array_get_size(x_97);
x_105 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_106 = 0;
x_107 = x_97;
x_108 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_19, x_62, x_105, x_106, x_107);
lean_dec(x_62);
x_109 = x_108;
x_110 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_110, 0, x_92);
lean_ctor_set(x_110, 1, x_93);
lean_ctor_set(x_110, 2, x_94);
lean_ctor_set(x_110, 3, x_95);
lean_ctor_set(x_110, 4, x_96);
lean_ctor_set(x_110, 5, x_109);
lean_ctor_set(x_110, 6, x_98);
lean_ctor_set(x_110, 7, x_99);
lean_ctor_set(x_110, 8, x_100);
lean_ctor_set(x_110, 9, x_101);
lean_ctor_set(x_110, 10, x_102);
lean_ctor_set(x_110, 11, x_103);
x_111 = lean_st_ref_set(x_2, x_110, x_80);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_7 = x_112;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_114 = lean_ctor_get(x_67, 0);
x_115 = lean_ctor_get(x_67, 1);
x_116 = lean_ctor_get(x_67, 2);
x_117 = lean_ctor_get(x_67, 3);
x_118 = lean_ctor_get(x_67, 4);
x_119 = lean_ctor_get(x_67, 5);
x_120 = lean_ctor_get(x_67, 6);
x_121 = lean_ctor_get(x_67, 7);
x_122 = lean_ctor_get(x_67, 8);
x_123 = lean_ctor_get(x_67, 9);
x_124 = lean_ctor_get(x_67, 10);
x_125 = lean_ctor_get(x_67, 11);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_67);
x_126 = lean_unsigned_to_nat(0u);
x_127 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_126);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_127);
x_128 = lean_array_push(x_121, x_21);
x_129 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_129, 0, x_114);
lean_ctor_set(x_129, 1, x_115);
lean_ctor_set(x_129, 2, x_116);
lean_ctor_set(x_129, 3, x_117);
lean_ctor_set(x_129, 4, x_118);
lean_ctor_set(x_129, 5, x_119);
lean_ctor_set(x_129, 6, x_120);
lean_ctor_set(x_129, 7, x_128);
lean_ctor_set(x_129, 8, x_122);
lean_ctor_set(x_129, 9, x_123);
lean_ctor_set(x_129, 10, x_124);
lean_ctor_set(x_129, 11, x_125);
x_130 = lean_st_ref_set(x_2, x_129, x_68);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_get(x_6, x_131);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_take(x_2, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 5);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 6);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 7);
lean_inc(x_144);
x_145 = lean_ctor_get(x_135, 8);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 9);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 10);
lean_inc(x_147);
x_148 = lean_ctor_get(x_135, 11);
lean_inc(x_148);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 lean_ctor_release(x_135, 6);
 lean_ctor_release(x_135, 7);
 lean_ctor_release(x_135, 8);
 lean_ctor_release(x_135, 9);
 lean_ctor_release(x_135, 10);
 lean_ctor_release(x_135, 11);
 x_149 = x_135;
} else {
 lean_dec_ref(x_135);
 x_149 = lean_box(0);
}
x_150 = lean_array_get_size(x_142);
x_151 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_152 = 0;
x_153 = x_142;
x_154 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_19, x_62, x_151, x_152, x_153);
lean_dec(x_62);
x_155 = x_154;
if (lean_is_scalar(x_149)) {
 x_156 = lean_alloc_ctor(0, 12, 0);
} else {
 x_156 = x_149;
}
lean_ctor_set(x_156, 0, x_137);
lean_ctor_set(x_156, 1, x_138);
lean_ctor_set(x_156, 2, x_139);
lean_ctor_set(x_156, 3, x_140);
lean_ctor_set(x_156, 4, x_141);
lean_ctor_set(x_156, 5, x_155);
lean_ctor_set(x_156, 6, x_143);
lean_ctor_set(x_156, 7, x_144);
lean_ctor_set(x_156, 8, x_145);
lean_ctor_set(x_156, 9, x_146);
lean_ctor_set(x_156, 10, x_147);
lean_ctor_set(x_156, 11, x_148);
x_157 = lean_st_ref_set(x_2, x_156, x_136);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_7 = x_158;
goto _start;
}
}
else
{
uint8_t x_160; 
lean_dec(x_59);
lean_free_object(x_21);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_61);
if (x_160 == 0)
{
return x_61;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_61, 0);
x_162 = lean_ctor_get(x_61, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_61);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_free_object(x_21);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_164 = !lean_is_exclusive(x_58);
if (x_164 == 0)
{
return x_58;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_58, 0);
x_166 = lean_ctor_get(x_58, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_58);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_168 = lean_ctor_get(x_21, 2);
x_169 = lean_ctor_get(x_21, 3);
x_170 = lean_ctor_get(x_21, 4);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_21);
x_171 = l_Lean_Meta_getZetaFVarIds___rarg(x_4, x_5, x_6, x_36);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_NameSet_contains(x_172, x_18);
lean_dec(x_172);
if (x_174 == 0)
{
uint8_t x_175; lean_object* x_176; 
lean_dec(x_170);
x_175 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_176 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_168, x_169, x_175, x_1, x_2, x_3, x_4, x_5, x_6, x_173);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_mkFVar(x_18);
x_179 = l_Lean_Meta_Closure_pushFVarArg(x_178, x_1, x_2, x_3, x_4, x_5, x_6, x_177);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_7 = x_180;
goto _start;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; 
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_186 = l_Lean_Meta_Closure_collectExpr(x_169, x_1, x_2, x_3, x_4, x_5, x_6, x_173);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_189 = l_Lean_Meta_Closure_collectExpr(x_170, x_1, x_2, x_3, x_4, x_5, x_6, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; size_t x_236; size_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_st_ref_get(x_6, x_191);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_st_ref_take(x_2, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_195, 5);
lean_inc(x_202);
x_203 = lean_ctor_get(x_195, 6);
lean_inc(x_203);
x_204 = lean_ctor_get(x_195, 7);
lean_inc(x_204);
x_205 = lean_ctor_get(x_195, 8);
lean_inc(x_205);
x_206 = lean_ctor_get(x_195, 9);
lean_inc(x_206);
x_207 = lean_ctor_get(x_195, 10);
lean_inc(x_207);
x_208 = lean_ctor_get(x_195, 11);
lean_inc(x_208);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 lean_ctor_release(x_195, 5);
 lean_ctor_release(x_195, 6);
 lean_ctor_release(x_195, 7);
 lean_ctor_release(x_195, 8);
 lean_ctor_release(x_195, 9);
 lean_ctor_release(x_195, 10);
 lean_ctor_release(x_195, 11);
 x_209 = x_195;
} else {
 lean_dec_ref(x_195);
 x_209 = lean_box(0);
}
x_210 = lean_unsigned_to_nat(0u);
x_211 = 0;
lean_inc(x_190);
lean_inc(x_19);
x_212 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_19);
lean_ctor_set(x_212, 2, x_168);
lean_ctor_set(x_212, 3, x_187);
lean_ctor_set(x_212, 4, x_190);
lean_ctor_set_uint8(x_212, sizeof(void*)*5, x_211);
x_213 = lean_array_push(x_204, x_212);
if (lean_is_scalar(x_209)) {
 x_214 = lean_alloc_ctor(0, 12, 0);
} else {
 x_214 = x_209;
}
lean_ctor_set(x_214, 0, x_197);
lean_ctor_set(x_214, 1, x_198);
lean_ctor_set(x_214, 2, x_199);
lean_ctor_set(x_214, 3, x_200);
lean_ctor_set(x_214, 4, x_201);
lean_ctor_set(x_214, 5, x_202);
lean_ctor_set(x_214, 6, x_203);
lean_ctor_set(x_214, 7, x_213);
lean_ctor_set(x_214, 8, x_205);
lean_ctor_set(x_214, 9, x_206);
lean_ctor_set(x_214, 10, x_207);
lean_ctor_set(x_214, 11, x_208);
x_215 = lean_st_ref_set(x_2, x_214, x_196);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_get(x_6, x_216);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_st_ref_take(x_2, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_220, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 4);
lean_inc(x_226);
x_227 = lean_ctor_get(x_220, 5);
lean_inc(x_227);
x_228 = lean_ctor_get(x_220, 6);
lean_inc(x_228);
x_229 = lean_ctor_get(x_220, 7);
lean_inc(x_229);
x_230 = lean_ctor_get(x_220, 8);
lean_inc(x_230);
x_231 = lean_ctor_get(x_220, 9);
lean_inc(x_231);
x_232 = lean_ctor_get(x_220, 10);
lean_inc(x_232);
x_233 = lean_ctor_get(x_220, 11);
lean_inc(x_233);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 lean_ctor_release(x_220, 2);
 lean_ctor_release(x_220, 3);
 lean_ctor_release(x_220, 4);
 lean_ctor_release(x_220, 5);
 lean_ctor_release(x_220, 6);
 lean_ctor_release(x_220, 7);
 lean_ctor_release(x_220, 8);
 lean_ctor_release(x_220, 9);
 lean_ctor_release(x_220, 10);
 lean_ctor_release(x_220, 11);
 x_234 = x_220;
} else {
 lean_dec_ref(x_220);
 x_234 = lean_box(0);
}
x_235 = lean_array_get_size(x_227);
x_236 = lean_usize_of_nat(x_235);
lean_dec(x_235);
x_237 = 0;
x_238 = x_227;
x_239 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_19, x_190, x_236, x_237, x_238);
lean_dec(x_190);
x_240 = x_239;
if (lean_is_scalar(x_234)) {
 x_241 = lean_alloc_ctor(0, 12, 0);
} else {
 x_241 = x_234;
}
lean_ctor_set(x_241, 0, x_222);
lean_ctor_set(x_241, 1, x_223);
lean_ctor_set(x_241, 2, x_224);
lean_ctor_set(x_241, 3, x_225);
lean_ctor_set(x_241, 4, x_226);
lean_ctor_set(x_241, 5, x_240);
lean_ctor_set(x_241, 6, x_228);
lean_ctor_set(x_241, 7, x_229);
lean_ctor_set(x_241, 8, x_230);
lean_ctor_set(x_241, 9, x_231);
lean_ctor_set(x_241, 10, x_232);
lean_ctor_set(x_241, 11, x_233);
x_242 = lean_st_ref_set(x_2, x_241, x_221);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_7 = x_243;
goto _start;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_187);
lean_dec(x_168);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_245 = lean_ctor_get(x_189, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_189, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_247 = x_189;
} else {
 lean_dec_ref(x_189);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_249 = lean_ctor_get(x_186, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_186, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_251 = x_186;
} else {
 lean_dec_ref(x_186);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_20);
if (x_253 == 0)
{
return x_20;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_20, 0);
x_255 = lean_ctor_get(x_20, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_20);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_LocalDecl_toExpr(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_instInhabitedLocalDecl;
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
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_usize_of_nat(x_4);
x_6 = 0;
lean_inc(x_2);
x_7 = x_2;
x_8 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_5, x_6, x_7);
x_9 = x_8;
x_10 = lean_expr_abstract(x_3, x_9);
x_11 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(x_1, x_2, x_9, x_4, x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(x_6, x_2, x_3, x_4, x_5);
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
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_instInhabitedLocalDecl;
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
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
x_5 = 0;
lean_inc(x_1);
x_6 = x_1;
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_6);
x_8 = x_7;
x_9 = lean_expr_abstract(x_2, x_8);
x_10 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_8, x_3, x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_instInhabitedLocalDecl;
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
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
x_5 = 0;
lean_inc(x_1);
x_6 = x_1;
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_6);
x_8 = x_7;
x_9 = lean_expr_abstract(x_2, x_8);
x_10 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_8, x_3, x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Meta_resetZetaFVarIds___rarg(x_6, x_7, x_8, x_9);
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
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get_uint8(x_11, 0);
x_43 = lean_ctor_get_uint8(x_11, 1);
x_44 = lean_ctor_get_uint8(x_11, 2);
x_45 = lean_ctor_get_uint8(x_11, 3);
x_46 = lean_ctor_get_uint8(x_11, 4);
x_47 = lean_ctor_get_uint8(x_11, 5);
x_48 = lean_ctor_get_uint8(x_11, 6);
x_49 = lean_ctor_get_uint8(x_11, 8);
lean_dec(x_11);
x_50 = 1;
x_51 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_51, 0, x_42);
lean_ctor_set_uint8(x_51, 1, x_43);
lean_ctor_set_uint8(x_51, 2, x_44);
lean_ctor_set_uint8(x_51, 3, x_45);
lean_ctor_set_uint8(x_51, 4, x_46);
lean_ctor_set_uint8(x_51, 5, x_47);
lean_ctor_set_uint8(x_51, 6, x_48);
lean_ctor_set_uint8(x_51, 7, x_50);
lean_ctor_set_uint8(x_51, 8, x_49);
lean_ctor_set(x_5, 0, x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_56);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_56);
lean_dec(x_53);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_71 = lean_ctor_get(x_52, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_52, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_73 = x_52;
} else {
 lean_dec_ref(x_52);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_5, 1);
x_76 = lean_ctor_get(x_5, 2);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_5);
x_77 = lean_ctor_get_uint8(x_11, 0);
x_78 = lean_ctor_get_uint8(x_11, 1);
x_79 = lean_ctor_get_uint8(x_11, 2);
x_80 = lean_ctor_get_uint8(x_11, 3);
x_81 = lean_ctor_get_uint8(x_11, 4);
x_82 = lean_ctor_get_uint8(x_11, 5);
x_83 = lean_ctor_get_uint8(x_11, 6);
x_84 = lean_ctor_get_uint8(x_11, 8);
if (lean_is_exclusive(x_11)) {
 x_85 = x_11;
} else {
 lean_dec_ref(x_11);
 x_85 = lean_box(0);
}
x_86 = 1;
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 0, 9);
} else {
 x_87 = x_85;
}
lean_ctor_set_uint8(x_87, 0, x_77);
lean_ctor_set_uint8(x_87, 1, x_78);
lean_ctor_set_uint8(x_87, 2, x_79);
lean_ctor_set_uint8(x_87, 3, x_80);
lean_ctor_set_uint8(x_87, 4, x_81);
lean_ctor_set_uint8(x_87, 5, x_82);
lean_ctor_set_uint8(x_87, 6, x_83);
lean_ctor_set_uint8(x_87, 7, x_86);
lean_ctor_set_uint8(x_87, 8, x_84);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_75);
lean_ctor_set(x_88, 2, x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_88);
x_89 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_88, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_88);
x_92 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_88, x_6, x_7, x_8, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Meta_Closure_process(x_3, x_4, x_88, x_6, x_7, x_8, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
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
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_93);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
lean_dec(x_90);
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_92, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_106 = x_92;
} else {
 lean_dec_ref(x_92);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_88);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_108 = lean_ctor_get(x_89, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_89, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_110 = x_89;
} else {
 lean_dec_ref(x_89);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
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
x_1 = l_Std_HashMap_instInhabitedHashMap___closed__1;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(x_3);
lean_inc(x_7);
x_16 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_15, x_13, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_7, x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_13, x_20);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_23, 5);
lean_inc(x_26);
x_27 = l_Array_reverse___rarg(x_26);
x_28 = lean_ctor_get(x_23, 6);
lean_inc(x_28);
x_29 = l_Array_append___rarg(x_27, x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_23, 7);
lean_inc(x_30);
x_31 = l_Array_reverse___rarg(x_30);
lean_inc(x_31);
x_32 = l_Lean_Meta_Closure_mkForall(x_31, x_24);
lean_dec(x_24);
lean_inc(x_29);
x_33 = l_Lean_Meta_Closure_mkForall(x_29, x_32);
lean_dec(x_32);
x_34 = l_Lean_Meta_Closure_mkLambda(x_31, x_25);
lean_dec(x_25);
x_35 = l_Lean_Meta_Closure_mkLambda(x_29, x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_23, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_23, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 10);
lean_inc(x_38);
x_39 = l_Array_reverse___rarg(x_38);
x_40 = lean_ctor_get(x_23, 9);
lean_inc(x_40);
lean_dec(x_23);
x_41 = l_Array_append___rarg(x_39, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_21, 0, x_42);
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_ctor_get(x_43, 5);
lean_inc(x_47);
x_48 = l_Array_reverse___rarg(x_47);
x_49 = lean_ctor_get(x_43, 6);
lean_inc(x_49);
x_50 = l_Array_append___rarg(x_48, x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_43, 7);
lean_inc(x_51);
x_52 = l_Array_reverse___rarg(x_51);
lean_inc(x_52);
x_53 = l_Lean_Meta_Closure_mkForall(x_52, x_45);
lean_dec(x_45);
lean_inc(x_50);
x_54 = l_Lean_Meta_Closure_mkForall(x_50, x_53);
lean_dec(x_53);
x_55 = l_Lean_Meta_Closure_mkLambda(x_52, x_46);
lean_dec(x_46);
x_56 = l_Lean_Meta_Closure_mkLambda(x_50, x_55);
lean_dec(x_55);
x_57 = lean_ctor_get(x_43, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_43, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_43, 10);
lean_inc(x_59);
x_60 = l_Array_reverse___rarg(x_59);
x_61 = lean_ctor_get(x_43, 9);
lean_inc(x_61);
lean_dec(x_43);
x_62 = l_Array_append___rarg(x_60, x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set(x_63, 2, x_56);
lean_ctor_set(x_63, 3, x_58);
lean_ctor_set(x_63, 4, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_44);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_16, 0);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_16);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
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
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Lean_KernelException_toMessageData(x_1, x_7);
x_9 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_14, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_15;
}
}
}
lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(x_13, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_15, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_16;
}
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_array_to_list(lean_box(0), x_9);
x_11 = l_Lean_mkConst(x_2, x_10);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_mkAppN(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termIf_____x3a__Then__Else_____closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termIfLet___x3a_x3d__Then__Else_____closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_90; lean_object* x_91; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_st_ref_get(x_9, x_10);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get_uint8(x_110, sizeof(void*)*1);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = 0;
x_90 = x_113;
x_91 = x_112;
goto block_107;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_115 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__4;
x_116 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_115, x_6, x_7, x_8, x_9, x_114);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_unbox(x_117);
lean_dec(x_117);
x_90 = x_119;
x_91 = x_118;
goto block_107;
}
block_89:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint32_t x_26; uint32_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_array_to_list(lean_box(0), x_19);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_21);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_ctor_get(x_13, 2);
lean_inc(x_23);
lean_inc(x_23);
lean_inc(x_18);
x_24 = l_Lean_getMaxHeight(x_18, x_23);
x_25 = lean_unbox_uint32(x_24);
lean_dec(x_24);
x_26 = 1;
x_27 = x_25 + x_26;
x_28 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_28, 0, x_27);
lean_inc(x_21);
lean_inc(x_18);
x_29 = l_Lean_Environment_hasUnsafe(x_18, x_21);
x_30 = lean_st_ref_get(x_9, x_17);
if (x_29 == 0)
{
uint8_t x_83; 
lean_inc(x_23);
x_83 = l_Lean_Environment_hasUnsafe(x_18, x_23);
x_31 = x_83;
goto block_82;
}
else
{
uint8_t x_84; 
lean_dec(x_18);
x_84 = 1;
x_31 = x_84;
goto block_82;
}
block_82:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; lean_object* x_54; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_inc(x_23);
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_71 = lean_ctor_get(x_30, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*1);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_30, 1);
lean_inc(x_74);
lean_dec(x_30);
x_75 = 0;
x_53 = x_75;
x_54 = x_74;
goto block_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_ctor_get(x_30, 1);
lean_inc(x_76);
lean_dec(x_30);
x_77 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__4;
x_78 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_77, x_6, x_7, x_8, x_9, x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_unbox(x_79);
lean_dec(x_79);
x_53 = x_81;
x_54 = x_80;
goto block_70;
}
block_52:
{
lean_object* x_35; 
lean_inc(x_8);
x_35 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_33, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_35) == 0)
{
if (x_5 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_13, x_1, x_37, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_inc(x_8);
x_40 = l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(x_33, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_33);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_13, x_1, x_41, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_41);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_33);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
block_70:
{
if (x_53 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_34 = x_54;
goto block_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc(x_1);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_1);
x_56 = l_Lean_KernelException_toMessageData___closed__15;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Meta_mkAuxDefinition___closed__1;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_21);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_mkAuxDefinition___closed__2;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_23);
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
x_67 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__4;
x_68 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_67, x_66, x_6, x_7, x_8, x_9, x_54);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_34 = x_69;
goto block_52;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_12);
if (x_85 == 0)
{
return x_12;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_12, 0);
x_87 = lean_ctor_get(x_12, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_12);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_107:
{
if (x_90 == 0)
{
x_11 = x_91;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_inc(x_1);
x_92 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_92, 0, x_1);
x_93 = l_Lean_KernelException_toMessageData___closed__15;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Meta_mkAuxDefinition___closed__1;
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_2);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_2);
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Meta_mkAuxDefinition___closed__2;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_3);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_3);
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_93);
x_104 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__4;
x_105 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_104, x_103, x_6, x_7, x_8, x_9, x_91);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_11 = x_106;
goto block_89;
}
}
}
}
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_mkAuxDefinition(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_inferType(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_headBeta(x_9);
x_12 = 0;
x_13 = 1;
x_14 = l_Lean_Meta_mkAuxDefinition(x_1, x_11, x_2, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
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
l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1 = _init_l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1);
l_Lean_Meta_Closure_instInhabitedToProcessElement = _init_l_Lean_Meta_Closure_instInhabitedToProcessElement();
lean_mark_persistent(l_Lean_Meta_Closure_instInhabitedToProcessElement);
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
l_Lean_Meta_mkAuxDefinition___closed__1 = _init_l_Lean_Meta_mkAuxDefinition___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___closed__1);
l_Lean_Meta_mkAuxDefinition___closed__2 = _init_l_Lean_Meta_mkAuxDefinition___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
