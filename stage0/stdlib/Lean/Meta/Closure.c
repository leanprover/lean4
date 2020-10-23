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
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Level_LevelToFormat_toResult___closed__3;
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1___closed__1;
extern lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__2;
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
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel_match__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedExpr___default___spec__1(lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1(lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalDecl_Lean_LocalContext___instance__1;
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkBinding_match__1(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitExpr___spec__7(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitExpr___spec__5(lean_object*, lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object*);
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
lean_object* l_Lean_Meta_Closure_State_exprMVarArgs___default;
lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_levelParams___default;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Nat_foldRevAux___main___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkBinding_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
extern lean_object* l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Meta_Closure_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__2(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitExpr___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux___rarg(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___at_Lean_ppGoal___spec__7___closed__4;
lean_object* l_Array_iterateMAux___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitExpr___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__1(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Meta_Closure_mkValueTypeClosureAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1___closed__1() {
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
static lean_object* _init_l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1___closed__1;
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
lean_object* x_10; uint8_t x_90; 
x_90 = l_Lean_Level_hasMVar(x_2);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Level_hasParam(x_2);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_9);
return x_92;
}
else
{
lean_object* x_93; 
x_93 = lean_box(0);
x_10 = x_93;
goto block_89;
}
}
else
{
lean_object* x_94; 
x_94 = lean_box(0);
x_10 = x_94;
goto block_89;
}
block_89:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_15, x_2);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_free_object(x_11);
lean_inc(x_4);
lean_inc(x_2);
x_17 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_18);
x_25 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_24, x_2, x_18);
lean_ctor_set(x_21, 0, x_25);
x_26 = lean_st_ref_set(x_4, x_21, x_22);
lean_dec(x_4);
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
x_43 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_31, x_2, x_18);
x_44 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_32);
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
x_45 = lean_st_ref_set(x_4, x_44, x_22);
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_53);
return x_11;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_56, x_2);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_inc(x_4);
lean_inc(x_2);
x_58 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_take(x_4, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 6);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 7);
lean_inc(x_71);
x_72 = lean_ctor_get(x_62, 8);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 9);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 10);
lean_inc(x_74);
x_75 = lean_ctor_get(x_62, 11);
lean_inc(x_75);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 lean_ctor_release(x_62, 5);
 lean_ctor_release(x_62, 6);
 lean_ctor_release(x_62, 7);
 lean_ctor_release(x_62, 8);
 lean_ctor_release(x_62, 9);
 lean_ctor_release(x_62, 10);
 lean_ctor_release(x_62, 11);
 x_76 = x_62;
} else {
 lean_dec_ref(x_62);
 x_76 = lean_box(0);
}
lean_inc(x_59);
x_77 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_64, x_2, x_59);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 12, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_65);
lean_ctor_set(x_78, 2, x_66);
lean_ctor_set(x_78, 3, x_67);
lean_ctor_set(x_78, 4, x_68);
lean_ctor_set(x_78, 5, x_69);
lean_ctor_set(x_78, 6, x_70);
lean_ctor_set(x_78, 7, x_71);
lean_ctor_set(x_78, 8, x_72);
lean_ctor_set(x_78, 9, x_73);
lean_ctor_set(x_78, 10, x_74);
lean_ctor_set(x_78, 11, x_75);
x_79 = lean_st_ref_set(x_4, x_78, x_63);
lean_dec(x_4);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_59);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_4);
lean_dec(x_2);
x_83 = lean_ctor_get(x_58, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_58, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_85 = x_58;
} else {
 lean_dec_ref(x_58);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_57, 0);
lean_inc(x_87);
lean_dec(x_57);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_55);
return x_88;
}
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
lean_object* x_10; uint8_t x_90; 
x_90 = l_Lean_Expr_hasLevelParam(x_2);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Expr_hasFVar(x_2);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = l_Lean_Expr_hasMVar(x_2);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_2);
lean_ctor_set(x_93, 1, x_9);
return x_93;
}
else
{
lean_object* x_94; 
x_94 = lean_box(0);
x_10 = x_94;
goto block_89;
}
}
else
{
lean_object* x_95; 
x_95 = lean_box(0);
x_10 = x_95;
goto block_89;
}
}
else
{
lean_object* x_96; 
x_96 = lean_box(0);
x_10 = x_96;
goto block_89;
}
block_89:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_4, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_15, x_2);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_free_object(x_11);
lean_inc(x_4);
lean_inc(x_2);
x_17 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_4, x_19);
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
x_25 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_24, x_2, x_18);
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_4, x_21, x_22);
lean_dec(x_4);
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
x_43 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_32, x_2, x_18);
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
x_45 = lean_st_ref_set(x_4, x_44, x_22);
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_53);
return x_11;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_56, x_2);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_inc(x_4);
lean_inc(x_2);
x_58 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_take(x_4, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 6);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 7);
lean_inc(x_71);
x_72 = lean_ctor_get(x_62, 8);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 9);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 10);
lean_inc(x_74);
x_75 = lean_ctor_get(x_62, 11);
lean_inc(x_75);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 lean_ctor_release(x_62, 5);
 lean_ctor_release(x_62, 6);
 lean_ctor_release(x_62, 7);
 lean_ctor_release(x_62, 8);
 lean_ctor_release(x_62, 9);
 lean_ctor_release(x_62, 10);
 lean_ctor_release(x_62, 11);
 x_76 = x_62;
} else {
 lean_dec_ref(x_62);
 x_76 = lean_box(0);
}
lean_inc(x_59);
x_77 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_65, x_2, x_59);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 12, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_66);
lean_ctor_set(x_78, 3, x_67);
lean_ctor_set(x_78, 4, x_68);
lean_ctor_set(x_78, 5, x_69);
lean_ctor_set(x_78, 6, x_70);
lean_ctor_set(x_78, 7, x_71);
lean_ctor_set(x_78, 8, x_72);
lean_ctor_set(x_78, 9, x_73);
lean_ctor_set(x_78, 10, x_74);
lean_ctor_set(x_78, 11, x_75);
x_79 = lean_st_ref_set(x_4, x_78, x_63);
lean_dec(x_4);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_59);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_4);
lean_dec(x_2);
x_83 = lean_ctor_get(x_58, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_58, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_85 = x_58;
} else {
 lean_dec_ref(x_58);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_57, 0);
lean_inc(x_87);
lean_dec(x_57);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_55);
return x_88;
}
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
x_13 = l_Lean_Level_LevelToFormat_toResult___closed__3;
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
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_97; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_12 = x_1;
} else {
 lean_dec_ref(x_1);
 x_12 = lean_box(0);
}
x_97 = l_Lean_Level_hasMVar(x_10);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l_Lean_Level_hasParam(x_10);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_12);
lean_inc(x_10);
x_99 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_99, 0, x_10);
lean_ctor_set_uint64(x_99, sizeof(void*)*1, x_11);
x_100 = lean_level_update_succ(x_99, x_10);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_8);
return x_101;
}
else
{
lean_object* x_102; 
x_102 = lean_box(0);
x_13 = x_102;
goto block_96;
}
}
else
{
lean_object* x_103; 
x_103 = lean_box(0);
x_13 = x_103;
goto block_96;
}
block_96:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_13);
x_14 = lean_st_ref_get(x_3, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_18, x_10);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_14);
lean_inc(x_10);
x_20 = l_Lean_Meta_Closure_collectLevelAux(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_21);
lean_inc(x_10);
x_28 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_27, x_10, x_21);
lean_ctor_set(x_24, 0, x_28);
x_29 = lean_st_ref_set(x_3, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
if (lean_is_scalar(x_12)) {
 x_32 = lean_alloc_ctor(1, 1, 8);
} else {
 x_32 = x_12;
}
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set_uint64(x_32, sizeof(void*)*1, x_11);
x_33 = lean_level_update_succ(x_32, x_21);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
if (lean_is_scalar(x_12)) {
 x_35 = lean_alloc_ctor(1, 1, 8);
} else {
 x_35 = x_12;
}
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set_uint64(x_35, sizeof(void*)*1, x_11);
x_36 = lean_level_update_succ(x_35, x_21);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
x_40 = lean_ctor_get(x_24, 2);
x_41 = lean_ctor_get(x_24, 3);
x_42 = lean_ctor_get(x_24, 4);
x_43 = lean_ctor_get(x_24, 5);
x_44 = lean_ctor_get(x_24, 6);
x_45 = lean_ctor_get(x_24, 7);
x_46 = lean_ctor_get(x_24, 8);
x_47 = lean_ctor_get(x_24, 9);
x_48 = lean_ctor_get(x_24, 10);
x_49 = lean_ctor_get(x_24, 11);
lean_inc(x_49);
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
lean_dec(x_24);
lean_inc(x_21);
lean_inc(x_10);
x_50 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_38, x_10, x_21);
x_51 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
lean_ctor_set(x_51, 2, x_40);
lean_ctor_set(x_51, 3, x_41);
lean_ctor_set(x_51, 4, x_42);
lean_ctor_set(x_51, 5, x_43);
lean_ctor_set(x_51, 6, x_44);
lean_ctor_set(x_51, 7, x_45);
lean_ctor_set(x_51, 8, x_46);
lean_ctor_set(x_51, 9, x_47);
lean_ctor_set(x_51, 10, x_48);
lean_ctor_set(x_51, 11, x_49);
x_52 = lean_st_ref_set(x_3, x_51, x_25);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_12)) {
 x_55 = lean_alloc_ctor(1, 1, 8);
} else {
 x_55 = x_12;
}
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set_uint64(x_55, sizeof(void*)*1, x_11);
x_56 = lean_level_update_succ(x_55, x_21);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_19, 0);
lean_inc(x_58);
lean_dec(x_19);
if (lean_is_scalar(x_12)) {
 x_59 = lean_alloc_ctor(1, 1, 8);
} else {
 x_59 = x_12;
}
lean_ctor_set(x_59, 0, x_10);
lean_ctor_set_uint64(x_59, sizeof(void*)*1, x_11);
x_60 = lean_level_update_succ(x_59, x_58);
lean_ctor_set(x_14, 0, x_60);
return x_14;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_14, 0);
x_62 = lean_ctor_get(x_14, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_14);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_63, x_10);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_inc(x_10);
x_65 = l_Lean_Meta_Closure_collectLevelAux(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_st_ref_take(x_3, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_69, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_69, 8);
lean_inc(x_79);
x_80 = lean_ctor_get(x_69, 9);
lean_inc(x_80);
x_81 = lean_ctor_get(x_69, 10);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 11);
lean_inc(x_82);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 lean_ctor_release(x_69, 4);
 lean_ctor_release(x_69, 5);
 lean_ctor_release(x_69, 6);
 lean_ctor_release(x_69, 7);
 lean_ctor_release(x_69, 8);
 lean_ctor_release(x_69, 9);
 lean_ctor_release(x_69, 10);
 lean_ctor_release(x_69, 11);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
lean_inc(x_66);
lean_inc(x_10);
x_84 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_71, x_10, x_66);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 12, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
lean_ctor_set(x_85, 2, x_73);
lean_ctor_set(x_85, 3, x_74);
lean_ctor_set(x_85, 4, x_75);
lean_ctor_set(x_85, 5, x_76);
lean_ctor_set(x_85, 6, x_77);
lean_ctor_set(x_85, 7, x_78);
lean_ctor_set(x_85, 8, x_79);
lean_ctor_set(x_85, 9, x_80);
lean_ctor_set(x_85, 10, x_81);
lean_ctor_set(x_85, 11, x_82);
x_86 = lean_st_ref_set(x_3, x_85, x_70);
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
if (lean_is_scalar(x_12)) {
 x_89 = lean_alloc_ctor(1, 1, 8);
} else {
 x_89 = x_12;
}
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set_uint64(x_89, sizeof(void*)*1, x_11);
x_90 = lean_level_update_succ(x_89, x_66);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_64, 0);
lean_inc(x_92);
lean_dec(x_64);
if (lean_is_scalar(x_12)) {
 x_93 = lean_alloc_ctor(1, 1, 8);
} else {
 x_93 = x_12;
}
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set_uint64(x_93, sizeof(void*)*1, x_11);
x_94 = lean_level_update_succ(x_93, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_62);
return x_95;
}
}
}
}
case 2:
{
lean_object* x_104; lean_object* x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_202; uint8_t x_237; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_107 = x_1;
} else {
 lean_dec_ref(x_1);
 x_107 = lean_box(0);
}
x_237 = l_Lean_Level_hasMVar(x_104);
if (x_237 == 0)
{
uint8_t x_238; 
x_238 = l_Lean_Level_hasParam(x_104);
if (x_238 == 0)
{
lean_inc(x_104);
x_108 = x_104;
x_109 = x_8;
goto block_201;
}
else
{
lean_object* x_239; 
x_239 = lean_box(0);
x_202 = x_239;
goto block_236;
}
}
else
{
lean_object* x_240; 
x_240 = lean_box(0);
x_202 = x_240;
goto block_236;
}
block_201:
{
lean_object* x_110; uint8_t x_194; 
x_194 = l_Lean_Level_hasMVar(x_105);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = l_Lean_Level_hasParam(x_105);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_107);
lean_inc(x_105);
x_196 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_196, 0, x_104);
lean_ctor_set(x_196, 1, x_105);
lean_ctor_set_uint64(x_196, sizeof(void*)*2, x_106);
x_197 = lean_level_update_max(x_196, x_108, x_105);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_109);
return x_198;
}
else
{
lean_object* x_199; 
x_199 = lean_box(0);
x_110 = x_199;
goto block_193;
}
}
else
{
lean_object* x_200; 
x_200 = lean_box(0);
x_110 = x_200;
goto block_193;
}
block_193:
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_110);
x_111 = lean_st_ref_get(x_3, x_109);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_115, x_105);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_free_object(x_111);
lean_inc(x_105);
x_117 = l_Lean_Meta_Closure_collectLevelAux(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_114);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_st_ref_take(x_3, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = !lean_is_exclusive(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_118);
lean_inc(x_105);
x_125 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_124, x_105, x_118);
lean_ctor_set(x_121, 0, x_125);
x_126 = lean_st_ref_set(x_3, x_121, x_122);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
lean_dec(x_128);
if (lean_is_scalar(x_107)) {
 x_129 = lean_alloc_ctor(2, 2, 8);
} else {
 x_129 = x_107;
}
lean_ctor_set(x_129, 0, x_104);
lean_ctor_set(x_129, 1, x_105);
lean_ctor_set_uint64(x_129, sizeof(void*)*2, x_106);
x_130 = lean_level_update_max(x_129, x_108, x_118);
lean_ctor_set(x_126, 0, x_130);
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
if (lean_is_scalar(x_107)) {
 x_132 = lean_alloc_ctor(2, 2, 8);
} else {
 x_132 = x_107;
}
lean_ctor_set(x_132, 0, x_104);
lean_ctor_set(x_132, 1, x_105);
lean_ctor_set_uint64(x_132, sizeof(void*)*2, x_106);
x_133 = lean_level_update_max(x_132, x_108, x_118);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
x_139 = lean_ctor_get(x_121, 4);
x_140 = lean_ctor_get(x_121, 5);
x_141 = lean_ctor_get(x_121, 6);
x_142 = lean_ctor_get(x_121, 7);
x_143 = lean_ctor_get(x_121, 8);
x_144 = lean_ctor_get(x_121, 9);
x_145 = lean_ctor_get(x_121, 10);
x_146 = lean_ctor_get(x_121, 11);
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
lean_inc(x_135);
lean_dec(x_121);
lean_inc(x_118);
lean_inc(x_105);
x_147 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_135, x_105, x_118);
x_148 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_136);
lean_ctor_set(x_148, 2, x_137);
lean_ctor_set(x_148, 3, x_138);
lean_ctor_set(x_148, 4, x_139);
lean_ctor_set(x_148, 5, x_140);
lean_ctor_set(x_148, 6, x_141);
lean_ctor_set(x_148, 7, x_142);
lean_ctor_set(x_148, 8, x_143);
lean_ctor_set(x_148, 9, x_144);
lean_ctor_set(x_148, 10, x_145);
lean_ctor_set(x_148, 11, x_146);
x_149 = lean_st_ref_set(x_3, x_148, x_122);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_152 = lean_alloc_ctor(2, 2, 8);
} else {
 x_152 = x_107;
}
lean_ctor_set(x_152, 0, x_104);
lean_ctor_set(x_152, 1, x_105);
lean_ctor_set_uint64(x_152, sizeof(void*)*2, x_106);
x_153 = lean_level_update_max(x_152, x_108, x_118);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_116, 0);
lean_inc(x_155);
lean_dec(x_116);
if (lean_is_scalar(x_107)) {
 x_156 = lean_alloc_ctor(2, 2, 8);
} else {
 x_156 = x_107;
}
lean_ctor_set(x_156, 0, x_104);
lean_ctor_set(x_156, 1, x_105);
lean_ctor_set_uint64(x_156, sizeof(void*)*2, x_106);
x_157 = lean_level_update_max(x_156, x_108, x_155);
lean_ctor_set(x_111, 0, x_157);
return x_111;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_111, 0);
x_159 = lean_ctor_get(x_111, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_111);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_160, x_105);
lean_dec(x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_inc(x_105);
x_162 = l_Lean_Meta_Closure_collectLevelAux(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_159);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_st_ref_take(x_3, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_166, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_166, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 5);
lean_inc(x_173);
x_174 = lean_ctor_get(x_166, 6);
lean_inc(x_174);
x_175 = lean_ctor_get(x_166, 7);
lean_inc(x_175);
x_176 = lean_ctor_get(x_166, 8);
lean_inc(x_176);
x_177 = lean_ctor_get(x_166, 9);
lean_inc(x_177);
x_178 = lean_ctor_get(x_166, 10);
lean_inc(x_178);
x_179 = lean_ctor_get(x_166, 11);
lean_inc(x_179);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 lean_ctor_release(x_166, 5);
 lean_ctor_release(x_166, 6);
 lean_ctor_release(x_166, 7);
 lean_ctor_release(x_166, 8);
 lean_ctor_release(x_166, 9);
 lean_ctor_release(x_166, 10);
 lean_ctor_release(x_166, 11);
 x_180 = x_166;
} else {
 lean_dec_ref(x_166);
 x_180 = lean_box(0);
}
lean_inc(x_163);
lean_inc(x_105);
x_181 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_168, x_105, x_163);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 12, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_169);
lean_ctor_set(x_182, 2, x_170);
lean_ctor_set(x_182, 3, x_171);
lean_ctor_set(x_182, 4, x_172);
lean_ctor_set(x_182, 5, x_173);
lean_ctor_set(x_182, 6, x_174);
lean_ctor_set(x_182, 7, x_175);
lean_ctor_set(x_182, 8, x_176);
lean_ctor_set(x_182, 9, x_177);
lean_ctor_set(x_182, 10, x_178);
lean_ctor_set(x_182, 11, x_179);
x_183 = lean_st_ref_set(x_3, x_182, x_167);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_186 = lean_alloc_ctor(2, 2, 8);
} else {
 x_186 = x_107;
}
lean_ctor_set(x_186, 0, x_104);
lean_ctor_set(x_186, 1, x_105);
lean_ctor_set_uint64(x_186, sizeof(void*)*2, x_106);
x_187 = lean_level_update_max(x_186, x_108, x_163);
if (lean_is_scalar(x_185)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_185;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_161, 0);
lean_inc(x_189);
lean_dec(x_161);
if (lean_is_scalar(x_107)) {
 x_190 = lean_alloc_ctor(2, 2, 8);
} else {
 x_190 = x_107;
}
lean_ctor_set(x_190, 0, x_104);
lean_ctor_set(x_190, 1, x_105);
lean_ctor_set_uint64(x_190, sizeof(void*)*2, x_106);
x_191 = lean_level_update_max(x_190, x_108, x_189);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_159);
return x_192;
}
}
}
}
block_236:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_202);
x_203 = lean_st_ref_get(x_3, x_8);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_206, x_104);
lean_dec(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_inc(x_104);
x_208 = l_Lean_Meta_Closure_collectLevelAux(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_205);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_st_ref_take(x_3, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_209);
lean_inc(x_104);
x_216 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_215, x_104, x_209);
lean_ctor_set(x_212, 0, x_216);
x_217 = lean_st_ref_set(x_3, x_212, x_213);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_108 = x_209;
x_109 = x_218;
goto block_201;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_219 = lean_ctor_get(x_212, 0);
x_220 = lean_ctor_get(x_212, 1);
x_221 = lean_ctor_get(x_212, 2);
x_222 = lean_ctor_get(x_212, 3);
x_223 = lean_ctor_get(x_212, 4);
x_224 = lean_ctor_get(x_212, 5);
x_225 = lean_ctor_get(x_212, 6);
x_226 = lean_ctor_get(x_212, 7);
x_227 = lean_ctor_get(x_212, 8);
x_228 = lean_ctor_get(x_212, 9);
x_229 = lean_ctor_get(x_212, 10);
x_230 = lean_ctor_get(x_212, 11);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_212);
lean_inc(x_209);
lean_inc(x_104);
x_231 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_219, x_104, x_209);
x_232 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_220);
lean_ctor_set(x_232, 2, x_221);
lean_ctor_set(x_232, 3, x_222);
lean_ctor_set(x_232, 4, x_223);
lean_ctor_set(x_232, 5, x_224);
lean_ctor_set(x_232, 6, x_225);
lean_ctor_set(x_232, 7, x_226);
lean_ctor_set(x_232, 8, x_227);
lean_ctor_set(x_232, 9, x_228);
lean_ctor_set(x_232, 10, x_229);
lean_ctor_set(x_232, 11, x_230);
x_233 = lean_st_ref_set(x_3, x_232, x_213);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_108 = x_209;
x_109 = x_234;
goto block_201;
}
}
else
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_207, 0);
lean_inc(x_235);
lean_dec(x_207);
x_108 = x_235;
x_109 = x_205;
goto block_201;
}
}
}
case 3:
{
lean_object* x_241; lean_object* x_242; uint64_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_339; uint8_t x_374; 
x_241 = lean_ctor_get(x_1, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_1, 1);
lean_inc(x_242);
x_243 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_244 = x_1;
} else {
 lean_dec_ref(x_1);
 x_244 = lean_box(0);
}
x_374 = l_Lean_Level_hasMVar(x_241);
if (x_374 == 0)
{
uint8_t x_375; 
x_375 = l_Lean_Level_hasParam(x_241);
if (x_375 == 0)
{
lean_inc(x_241);
x_245 = x_241;
x_246 = x_8;
goto block_338;
}
else
{
lean_object* x_376; 
x_376 = lean_box(0);
x_339 = x_376;
goto block_373;
}
}
else
{
lean_object* x_377; 
x_377 = lean_box(0);
x_339 = x_377;
goto block_373;
}
block_338:
{
lean_object* x_247; uint8_t x_331; 
x_331 = l_Lean_Level_hasMVar(x_242);
if (x_331 == 0)
{
uint8_t x_332; 
x_332 = l_Lean_Level_hasParam(x_242);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_244);
lean_inc(x_242);
x_333 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_333, 0, x_241);
lean_ctor_set(x_333, 1, x_242);
lean_ctor_set_uint64(x_333, sizeof(void*)*2, x_243);
x_334 = lean_level_update_imax(x_333, x_245, x_242);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_246);
return x_335;
}
else
{
lean_object* x_336; 
x_336 = lean_box(0);
x_247 = x_336;
goto block_330;
}
}
else
{
lean_object* x_337; 
x_337 = lean_box(0);
x_247 = x_337;
goto block_330;
}
block_330:
{
lean_object* x_248; uint8_t x_249; 
lean_dec(x_247);
x_248 = lean_st_ref_get(x_3, x_246);
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_248, 0);
x_251 = lean_ctor_get(x_248, 1);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_252, x_242);
lean_dec(x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
lean_free_object(x_248);
lean_inc(x_242);
x_254 = l_Lean_Meta_Closure_collectLevelAux(x_242, x_2, x_3, x_4, x_5, x_6, x_7, x_251);
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
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_261 = lean_ctor_get(x_258, 0);
lean_inc(x_255);
lean_inc(x_242);
x_262 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_261, x_242, x_255);
lean_ctor_set(x_258, 0, x_262);
x_263 = lean_st_ref_set(x_3, x_258, x_259);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_263, 0);
lean_dec(x_265);
if (lean_is_scalar(x_244)) {
 x_266 = lean_alloc_ctor(3, 2, 8);
} else {
 x_266 = x_244;
}
lean_ctor_set(x_266, 0, x_241);
lean_ctor_set(x_266, 1, x_242);
lean_ctor_set_uint64(x_266, sizeof(void*)*2, x_243);
x_267 = lean_level_update_imax(x_266, x_245, x_255);
lean_ctor_set(x_263, 0, x_267);
return x_263;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
lean_dec(x_263);
if (lean_is_scalar(x_244)) {
 x_269 = lean_alloc_ctor(3, 2, 8);
} else {
 x_269 = x_244;
}
lean_ctor_set(x_269, 0, x_241);
lean_ctor_set(x_269, 1, x_242);
lean_ctor_set_uint64(x_269, sizeof(void*)*2, x_243);
x_270 = lean_level_update_imax(x_269, x_245, x_255);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_268);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_272 = lean_ctor_get(x_258, 0);
x_273 = lean_ctor_get(x_258, 1);
x_274 = lean_ctor_get(x_258, 2);
x_275 = lean_ctor_get(x_258, 3);
x_276 = lean_ctor_get(x_258, 4);
x_277 = lean_ctor_get(x_258, 5);
x_278 = lean_ctor_get(x_258, 6);
x_279 = lean_ctor_get(x_258, 7);
x_280 = lean_ctor_get(x_258, 8);
x_281 = lean_ctor_get(x_258, 9);
x_282 = lean_ctor_get(x_258, 10);
x_283 = lean_ctor_get(x_258, 11);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_258);
lean_inc(x_255);
lean_inc(x_242);
x_284 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_272, x_242, x_255);
x_285 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_273);
lean_ctor_set(x_285, 2, x_274);
lean_ctor_set(x_285, 3, x_275);
lean_ctor_set(x_285, 4, x_276);
lean_ctor_set(x_285, 5, x_277);
lean_ctor_set(x_285, 6, x_278);
lean_ctor_set(x_285, 7, x_279);
lean_ctor_set(x_285, 8, x_280);
lean_ctor_set(x_285, 9, x_281);
lean_ctor_set(x_285, 10, x_282);
lean_ctor_set(x_285, 11, x_283);
x_286 = lean_st_ref_set(x_3, x_285, x_259);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_288 = x_286;
} else {
 lean_dec_ref(x_286);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_289 = lean_alloc_ctor(3, 2, 8);
} else {
 x_289 = x_244;
}
lean_ctor_set(x_289, 0, x_241);
lean_ctor_set(x_289, 1, x_242);
lean_ctor_set_uint64(x_289, sizeof(void*)*2, x_243);
x_290 = lean_level_update_imax(x_289, x_245, x_255);
if (lean_is_scalar(x_288)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_288;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_287);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_253, 0);
lean_inc(x_292);
lean_dec(x_253);
if (lean_is_scalar(x_244)) {
 x_293 = lean_alloc_ctor(3, 2, 8);
} else {
 x_293 = x_244;
}
lean_ctor_set(x_293, 0, x_241);
lean_ctor_set(x_293, 1, x_242);
lean_ctor_set_uint64(x_293, sizeof(void*)*2, x_243);
x_294 = lean_level_update_imax(x_293, x_245, x_292);
lean_ctor_set(x_248, 0, x_294);
return x_248;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_248, 0);
x_296 = lean_ctor_get(x_248, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_248);
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
lean_dec(x_295);
x_298 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_297, x_242);
lean_dec(x_297);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_inc(x_242);
x_299 = l_Lean_Meta_Closure_collectLevelAux(x_242, x_2, x_3, x_4, x_5, x_6, x_7, x_296);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_st_ref_take(x_3, x_301);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_303, 2);
lean_inc(x_307);
x_308 = lean_ctor_get(x_303, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_303, 4);
lean_inc(x_309);
x_310 = lean_ctor_get(x_303, 5);
lean_inc(x_310);
x_311 = lean_ctor_get(x_303, 6);
lean_inc(x_311);
x_312 = lean_ctor_get(x_303, 7);
lean_inc(x_312);
x_313 = lean_ctor_get(x_303, 8);
lean_inc(x_313);
x_314 = lean_ctor_get(x_303, 9);
lean_inc(x_314);
x_315 = lean_ctor_get(x_303, 10);
lean_inc(x_315);
x_316 = lean_ctor_get(x_303, 11);
lean_inc(x_316);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 lean_ctor_release(x_303, 2);
 lean_ctor_release(x_303, 3);
 lean_ctor_release(x_303, 4);
 lean_ctor_release(x_303, 5);
 lean_ctor_release(x_303, 6);
 lean_ctor_release(x_303, 7);
 lean_ctor_release(x_303, 8);
 lean_ctor_release(x_303, 9);
 lean_ctor_release(x_303, 10);
 lean_ctor_release(x_303, 11);
 x_317 = x_303;
} else {
 lean_dec_ref(x_303);
 x_317 = lean_box(0);
}
lean_inc(x_300);
lean_inc(x_242);
x_318 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_305, x_242, x_300);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 12, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_306);
lean_ctor_set(x_319, 2, x_307);
lean_ctor_set(x_319, 3, x_308);
lean_ctor_set(x_319, 4, x_309);
lean_ctor_set(x_319, 5, x_310);
lean_ctor_set(x_319, 6, x_311);
lean_ctor_set(x_319, 7, x_312);
lean_ctor_set(x_319, 8, x_313);
lean_ctor_set(x_319, 9, x_314);
lean_ctor_set(x_319, 10, x_315);
lean_ctor_set(x_319, 11, x_316);
x_320 = lean_st_ref_set(x_3, x_319, x_304);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_322 = x_320;
} else {
 lean_dec_ref(x_320);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_323 = lean_alloc_ctor(3, 2, 8);
} else {
 x_323 = x_244;
}
lean_ctor_set(x_323, 0, x_241);
lean_ctor_set(x_323, 1, x_242);
lean_ctor_set_uint64(x_323, sizeof(void*)*2, x_243);
x_324 = lean_level_update_imax(x_323, x_245, x_300);
if (lean_is_scalar(x_322)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_322;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_321);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_326 = lean_ctor_get(x_298, 0);
lean_inc(x_326);
lean_dec(x_298);
if (lean_is_scalar(x_244)) {
 x_327 = lean_alloc_ctor(3, 2, 8);
} else {
 x_327 = x_244;
}
lean_ctor_set(x_327, 0, x_241);
lean_ctor_set(x_327, 1, x_242);
lean_ctor_set_uint64(x_327, sizeof(void*)*2, x_243);
x_328 = lean_level_update_imax(x_327, x_245, x_326);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_296);
return x_329;
}
}
}
}
block_373:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_339);
x_340 = lean_st_ref_get(x_3, x_8);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
lean_dec(x_341);
x_344 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_343, x_241);
lean_dec(x_343);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
lean_inc(x_241);
x_345 = l_Lean_Meta_Closure_collectLevelAux(x_241, x_2, x_3, x_4, x_5, x_6, x_7, x_342);
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
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_346);
lean_inc(x_241);
x_353 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_352, x_241, x_346);
lean_ctor_set(x_349, 0, x_353);
x_354 = lean_st_ref_set(x_3, x_349, x_350);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
x_245 = x_346;
x_246 = x_355;
goto block_338;
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
lean_inc(x_241);
x_368 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_356, x_241, x_346);
x_369 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_357);
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
x_245 = x_346;
x_246 = x_371;
goto block_338;
}
}
else
{
lean_object* x_372; 
x_372 = lean_ctor_get(x_344, 0);
lean_inc(x_372);
lean_dec(x_344);
x_245 = x_372;
x_246 = x_342;
goto block_338;
}
}
}
default: 
{
lean_object* x_378; 
x_378 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_378;
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
lean_object* x_9; uint8_t x_81; 
x_81 = l_Lean_Level_hasMVar(x_1);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Level_hasParam(x_1);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_8);
return x_83;
}
else
{
lean_object* x_84; 
x_84 = lean_box(0);
x_9 = x_84;
goto block_80;
}
}
else
{
lean_object* x_85; 
x_85 = lean_box(0);
x_9 = x_85;
goto block_80;
}
block_80:
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_9);
x_10 = lean_st_ref_get(x_3, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_14, x_1);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_10);
lean_inc(x_1);
x_16 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_3, x_18);
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
lean_inc(x_17);
x_24 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_23, x_1, x_17);
lean_ctor_set(x_20, 0, x_24);
x_25 = lean_st_ref_set(x_3, x_20, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_17);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
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
lean_inc(x_17);
x_42 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_30, x_1, x_17);
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
x_44 = lean_st_ref_set(x_3, x_43, x_21);
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
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_48);
return x_10;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_51, x_1);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_1);
x_53 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_take(x_3, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 7);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 8);
lean_inc(x_67);
x_68 = lean_ctor_get(x_57, 9);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 10);
lean_inc(x_69);
x_70 = lean_ctor_get(x_57, 11);
lean_inc(x_70);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 lean_ctor_release(x_57, 7);
 lean_ctor_release(x_57, 8);
 lean_ctor_release(x_57, 9);
 lean_ctor_release(x_57, 10);
 lean_ctor_release(x_57, 11);
 x_71 = x_57;
} else {
 lean_dec_ref(x_57);
 x_71 = lean_box(0);
}
lean_inc(x_54);
x_72 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_59, x_1, x_54);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 12, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_63);
lean_ctor_set(x_73, 5, x_64);
lean_ctor_set(x_73, 6, x_65);
lean_ctor_set(x_73, 7, x_66);
lean_ctor_set(x_73, 8, x_67);
lean_ctor_set(x_73, 9, x_68);
lean_ctor_set(x_73, 10, x_69);
lean_ctor_set(x_73, 11, x_70);
x_74 = lean_st_ref_set(x_3, x_73, x_58);
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
lean_ctor_set(x_77, 0, x_54);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_52, 0);
lean_inc(x_78);
lean_dec(x_52);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_50);
return x_79;
}
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
lean_object* x_9; 
x_9 = l_Lean_Meta_instantiateMVarsImp(x_1, x_4, x_5, x_6, x_7, x_8);
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
x_9 = l_Lean_Meta_instantiateMVarsImp(x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_Closure_preprocess___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_19 = l_Lean_throwUnknownConstant___rarg___closed__3;
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
x_31 = l_Lean_throwUnknownConstant___rarg___closed__3;
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
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
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
x_28 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
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
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_9);
x_10 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_Closure_collectExprAux___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = lean_unbox(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_Closure_pushToProcess(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_mkFVar(x_14);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_mkFVar(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = l_Lean_LocalDecl_value_x3f(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_7, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Meta_Closure_pushToProcess(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lean_mkFVar(x_28);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_mkFVar(x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_39 = l_Lean_Meta_Closure_preprocess(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_123; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_123 = l_Lean_Expr_hasLevelParam(x_41);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = l_Lean_Expr_hasFVar(x_41);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = l_Lean_Expr_hasMVar(x_41);
if (x_125 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
else
{
lean_object* x_126; 
lean_free_object(x_39);
x_126 = lean_box(0);
x_43 = x_126;
goto block_122;
}
}
else
{
lean_object* x_127; 
lean_free_object(x_39);
x_127 = lean_box(0);
x_43 = x_127;
goto block_122;
}
}
else
{
lean_object* x_128; 
lean_free_object(x_39);
x_128 = lean_box(0);
x_43 = x_128;
goto block_122;
}
block_122:
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_43);
x_44 = lean_st_ref_get(x_3, x_42);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_48, x_41);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_free_object(x_44);
lean_inc(x_41);
x_50 = l_Lean_Meta_Closure_collectExprAux(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_take(x_3, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_51);
x_58 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_57, x_41, x_51);
lean_ctor_set(x_54, 1, x_58);
x_59 = lean_st_ref_set(x_3, x_54, x_55);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_51);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
x_66 = lean_ctor_get(x_54, 2);
x_67 = lean_ctor_get(x_54, 3);
x_68 = lean_ctor_get(x_54, 4);
x_69 = lean_ctor_get(x_54, 5);
x_70 = lean_ctor_get(x_54, 6);
x_71 = lean_ctor_get(x_54, 7);
x_72 = lean_ctor_get(x_54, 8);
x_73 = lean_ctor_get(x_54, 9);
x_74 = lean_ctor_get(x_54, 10);
x_75 = lean_ctor_get(x_54, 11);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
lean_inc(x_51);
x_76 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_65, x_41, x_51);
x_77 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_66);
lean_ctor_set(x_77, 3, x_67);
lean_ctor_set(x_77, 4, x_68);
lean_ctor_set(x_77, 5, x_69);
lean_ctor_set(x_77, 6, x_70);
lean_ctor_set(x_77, 7, x_71);
lean_ctor_set(x_77, 8, x_72);
lean_ctor_set(x_77, 9, x_73);
lean_ctor_set(x_77, 10, x_74);
lean_ctor_set(x_77, 11, x_75);
x_78 = lean_st_ref_set(x_3, x_77, x_55);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_51);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_41);
x_82 = !lean_is_exclusive(x_50);
if (x_82 == 0)
{
return x_50;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_50, 0);
x_84 = lean_ctor_get(x_50, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_50);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = lean_ctor_get(x_49, 0);
lean_inc(x_86);
lean_dec(x_49);
lean_ctor_set(x_44, 0, x_86);
return x_44;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_44, 0);
x_88 = lean_ctor_get(x_44, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_44);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_89, x_41);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_inc(x_41);
x_91 = l_Lean_Meta_Closure_collectExprAux(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_take(x_3, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_95, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_95, 7);
lean_inc(x_104);
x_105 = lean_ctor_get(x_95, 8);
lean_inc(x_105);
x_106 = lean_ctor_get(x_95, 9);
lean_inc(x_106);
x_107 = lean_ctor_get(x_95, 10);
lean_inc(x_107);
x_108 = lean_ctor_get(x_95, 11);
lean_inc(x_108);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 lean_ctor_release(x_95, 2);
 lean_ctor_release(x_95, 3);
 lean_ctor_release(x_95, 4);
 lean_ctor_release(x_95, 5);
 lean_ctor_release(x_95, 6);
 lean_ctor_release(x_95, 7);
 lean_ctor_release(x_95, 8);
 lean_ctor_release(x_95, 9);
 lean_ctor_release(x_95, 10);
 lean_ctor_release(x_95, 11);
 x_109 = x_95;
} else {
 lean_dec_ref(x_95);
 x_109 = lean_box(0);
}
lean_inc(x_92);
x_110 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_98, x_41, x_92);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 12, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_97);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_99);
lean_ctor_set(x_111, 3, x_100);
lean_ctor_set(x_111, 4, x_101);
lean_ctor_set(x_111, 5, x_102);
lean_ctor_set(x_111, 6, x_103);
lean_ctor_set(x_111, 7, x_104);
lean_ctor_set(x_111, 8, x_105);
lean_ctor_set(x_111, 9, x_106);
lean_ctor_set(x_111, 10, x_107);
lean_ctor_set(x_111, 11, x_108);
x_112 = lean_st_ref_set(x_3, x_111, x_96);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_92);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_41);
x_116 = lean_ctor_get(x_91, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_91, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_118 = x_91;
} else {
 lean_dec_ref(x_91);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = lean_ctor_get(x_90, 0);
lean_inc(x_120);
lean_dec(x_90);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_88);
return x_121;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_170; 
x_129 = lean_ctor_get(x_39, 0);
x_130 = lean_ctor_get(x_39, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_39);
x_170 = l_Lean_Expr_hasLevelParam(x_129);
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = l_Lean_Expr_hasFVar(x_129);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasMVar(x_129);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_129);
lean_ctor_set(x_173, 1, x_130);
return x_173;
}
else
{
lean_object* x_174; 
x_174 = lean_box(0);
x_131 = x_174;
goto block_169;
}
}
else
{
lean_object* x_175; 
x_175 = lean_box(0);
x_131 = x_175;
goto block_169;
}
}
else
{
lean_object* x_176; 
x_176 = lean_box(0);
x_131 = x_176;
goto block_169;
}
block_169:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_131);
x_132 = lean_st_ref_get(x_3, x_130);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_136, x_129);
lean_dec(x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_inc(x_129);
x_138 = l_Lean_Meta_Closure_collectExprAux(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_134);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_st_ref_take(x_3, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_142, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_142, 5);
lean_inc(x_149);
x_150 = lean_ctor_get(x_142, 6);
lean_inc(x_150);
x_151 = lean_ctor_get(x_142, 7);
lean_inc(x_151);
x_152 = lean_ctor_get(x_142, 8);
lean_inc(x_152);
x_153 = lean_ctor_get(x_142, 9);
lean_inc(x_153);
x_154 = lean_ctor_get(x_142, 10);
lean_inc(x_154);
x_155 = lean_ctor_get(x_142, 11);
lean_inc(x_155);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 lean_ctor_release(x_142, 5);
 lean_ctor_release(x_142, 6);
 lean_ctor_release(x_142, 7);
 lean_ctor_release(x_142, 8);
 lean_ctor_release(x_142, 9);
 lean_ctor_release(x_142, 10);
 lean_ctor_release(x_142, 11);
 x_156 = x_142;
} else {
 lean_dec_ref(x_142);
 x_156 = lean_box(0);
}
lean_inc(x_139);
x_157 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_145, x_129, x_139);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 12, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_144);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_146);
lean_ctor_set(x_158, 3, x_147);
lean_ctor_set(x_158, 4, x_148);
lean_ctor_set(x_158, 5, x_149);
lean_ctor_set(x_158, 6, x_150);
lean_ctor_set(x_158, 7, x_151);
lean_ctor_set(x_158, 8, x_152);
lean_ctor_set(x_158, 9, x_153);
lean_ctor_set(x_158, 10, x_154);
lean_ctor_set(x_158, 11, x_155);
x_159 = lean_st_ref_set(x_3, x_158, x_143);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_139);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_129);
x_163 = lean_ctor_get(x_138, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_138, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_165 = x_138;
} else {
 lean_dec_ref(x_138);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_129);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_167 = lean_ctor_get(x_137, 0);
lean_inc(x_167);
lean_dec(x_137);
if (lean_is_scalar(x_135)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_135;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_134);
return x_168;
}
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = !lean_is_exclusive(x_39);
if (x_177 == 0)
{
return x_39;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_39, 0);
x_179 = lean_ctor_get(x_39, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_39);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_181 = !lean_is_exclusive(x_10);
if (x_181 == 0)
{
return x_10;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_10, 0);
x_183 = lean_ctor_get(x_10, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_10);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
case 2:
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_1, 0);
lean_inc(x_185);
x_186 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_Closure_collectExprAux___spec__3(x_185, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 2);
lean_inc(x_189);
lean_dec(x_187);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_190 = l_Lean_Meta_Closure_preprocess(x_189, x_2, x_3, x_4, x_5, x_6, x_7, x_188);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_243; uint8_t x_282; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_282 = l_Lean_Expr_hasLevelParam(x_191);
if (x_282 == 0)
{
uint8_t x_283; 
x_283 = l_Lean_Expr_hasFVar(x_191);
if (x_283 == 0)
{
uint8_t x_284; 
x_284 = l_Lean_Expr_hasMVar(x_191);
if (x_284 == 0)
{
x_193 = x_191;
x_194 = x_192;
goto block_242;
}
else
{
lean_object* x_285; 
x_285 = lean_box(0);
x_243 = x_285;
goto block_281;
}
}
else
{
lean_object* x_286; 
x_286 = lean_box(0);
x_243 = x_286;
goto block_281;
}
}
else
{
lean_object* x_287; 
x_287 = lean_box(0);
x_243 = x_287;
goto block_281;
}
block_242:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_195 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_7, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_197);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_st_ref_take(x_3, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = !lean_is_exclusive(x_202);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_205 = lean_ctor_get(x_202, 6);
x_206 = lean_ctor_get(x_202, 9);
x_207 = lean_unsigned_to_nat(0u);
x_208 = 0;
lean_inc(x_196);
x_209 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_196);
lean_ctor_set(x_209, 2, x_199);
lean_ctor_set(x_209, 3, x_193);
lean_ctor_set_uint8(x_209, sizeof(void*)*4, x_208);
x_210 = lean_array_push(x_205, x_209);
x_211 = lean_array_push(x_206, x_1);
lean_ctor_set(x_202, 9, x_211);
lean_ctor_set(x_202, 6, x_210);
x_212 = lean_st_ref_set(x_3, x_202, x_203);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 0);
lean_dec(x_214);
x_215 = l_Lean_mkFVar(x_196);
lean_ctor_set(x_212, 0, x_215);
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
x_217 = l_Lean_mkFVar(x_196);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_219 = lean_ctor_get(x_202, 0);
x_220 = lean_ctor_get(x_202, 1);
x_221 = lean_ctor_get(x_202, 2);
x_222 = lean_ctor_get(x_202, 3);
x_223 = lean_ctor_get(x_202, 4);
x_224 = lean_ctor_get(x_202, 5);
x_225 = lean_ctor_get(x_202, 6);
x_226 = lean_ctor_get(x_202, 7);
x_227 = lean_ctor_get(x_202, 8);
x_228 = lean_ctor_get(x_202, 9);
x_229 = lean_ctor_get(x_202, 10);
x_230 = lean_ctor_get(x_202, 11);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_202);
x_231 = lean_unsigned_to_nat(0u);
x_232 = 0;
lean_inc(x_196);
x_233 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_196);
lean_ctor_set(x_233, 2, x_199);
lean_ctor_set(x_233, 3, x_193);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_array_push(x_225, x_233);
x_235 = lean_array_push(x_228, x_1);
x_236 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_236, 0, x_219);
lean_ctor_set(x_236, 1, x_220);
lean_ctor_set(x_236, 2, x_221);
lean_ctor_set(x_236, 3, x_222);
lean_ctor_set(x_236, 4, x_223);
lean_ctor_set(x_236, 5, x_224);
lean_ctor_set(x_236, 6, x_234);
lean_ctor_set(x_236, 7, x_226);
lean_ctor_set(x_236, 8, x_227);
lean_ctor_set(x_236, 9, x_235);
lean_ctor_set(x_236, 10, x_229);
lean_ctor_set(x_236, 11, x_230);
x_237 = lean_st_ref_set(x_3, x_236, x_203);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = l_Lean_mkFVar(x_196);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_238);
return x_241;
}
}
block_281:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_243);
x_244 = lean_st_ref_get(x_3, x_192);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_247, x_191);
lean_dec(x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_191);
x_249 = l_Lean_Meta_Closure_collectExprAux(x_191, x_2, x_3, x_4, x_5, x_6, x_7, x_246);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_st_ref_take(x_3, x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_250);
x_257 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_256, x_191, x_250);
lean_ctor_set(x_253, 1, x_257);
x_258 = lean_st_ref_set(x_3, x_253, x_254);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_193 = x_250;
x_194 = x_259;
goto block_242;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_260 = lean_ctor_get(x_253, 0);
x_261 = lean_ctor_get(x_253, 1);
x_262 = lean_ctor_get(x_253, 2);
x_263 = lean_ctor_get(x_253, 3);
x_264 = lean_ctor_get(x_253, 4);
x_265 = lean_ctor_get(x_253, 5);
x_266 = lean_ctor_get(x_253, 6);
x_267 = lean_ctor_get(x_253, 7);
x_268 = lean_ctor_get(x_253, 8);
x_269 = lean_ctor_get(x_253, 9);
x_270 = lean_ctor_get(x_253, 10);
x_271 = lean_ctor_get(x_253, 11);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_253);
lean_inc(x_250);
x_272 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_261, x_191, x_250);
x_273 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_273, 0, x_260);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_273, 2, x_262);
lean_ctor_set(x_273, 3, x_263);
lean_ctor_set(x_273, 4, x_264);
lean_ctor_set(x_273, 5, x_265);
lean_ctor_set(x_273, 6, x_266);
lean_ctor_set(x_273, 7, x_267);
lean_ctor_set(x_273, 8, x_268);
lean_ctor_set(x_273, 9, x_269);
lean_ctor_set(x_273, 10, x_270);
lean_ctor_set(x_273, 11, x_271);
x_274 = lean_st_ref_set(x_3, x_273, x_254);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_193 = x_250;
x_194 = x_275;
goto block_242;
}
}
else
{
uint8_t x_276; 
lean_dec(x_191);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_249);
if (x_276 == 0)
{
return x_249;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_249, 0);
x_278 = lean_ctor_get(x_249, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_249);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; 
lean_dec(x_191);
x_280 = lean_ctor_get(x_248, 0);
lean_inc(x_280);
lean_dec(x_248);
x_193 = x_280;
x_194 = x_246;
goto block_242;
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_288 = !lean_is_exclusive(x_190);
if (x_288 == 0)
{
return x_190;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_190, 0);
x_290 = lean_ctor_get(x_190, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_190);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_186);
if (x_292 == 0)
{
return x_186;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_186, 0);
x_294 = lean_ctor_get(x_186, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_186);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
case 3:
{
uint8_t x_296; 
x_296 = !lean_is_exclusive(x_1);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_297 = lean_ctor_get(x_1, 0);
lean_inc(x_297);
x_298 = l_Lean_Meta_Closure_collectLevel(x_297, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_298, 0);
x_301 = lean_expr_update_sort(x_1, x_300);
lean_ctor_set(x_298, 0, x_301);
return x_298;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_ctor_get(x_298, 0);
x_303 = lean_ctor_get(x_298, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_298);
x_304 = lean_expr_update_sort(x_1, x_302);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
else
{
lean_object* x_306; uint64_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_306 = lean_ctor_get(x_1, 0);
x_307 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_306);
lean_dec(x_1);
lean_inc(x_306);
x_308 = l_Lean_Meta_Closure_collectLevel(x_306, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
x_312 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_312, 0, x_306);
lean_ctor_set_uint64(x_312, sizeof(void*)*1, x_307);
x_313 = lean_expr_update_sort(x_312, x_309);
if (lean_is_scalar(x_311)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_311;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_310);
return x_314;
}
}
case 4:
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_1);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_1, 1);
lean_inc(x_316);
x_317 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4(x_316, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
else
{
lean_object* x_325; lean_object* x_326; uint64_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_325 = lean_ctor_get(x_1, 0);
x_326 = lean_ctor_get(x_1, 1);
x_327 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_1);
lean_inc(x_326);
x_328 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4(x_326, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_332 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_332, 0, x_325);
lean_ctor_set(x_332, 1, x_326);
lean_ctor_set_uint64(x_332, sizeof(void*)*2, x_327);
x_333 = lean_expr_update_const(x_332, x_329);
if (lean_is_scalar(x_331)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_331;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_330);
return x_334;
}
}
case 5:
{
lean_object* x_335; lean_object* x_336; uint64_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_443; uint8_t x_482; 
x_335 = lean_ctor_get(x_1, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_1, 1);
lean_inc(x_336);
x_337 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_338 = x_1;
} else {
 lean_dec_ref(x_1);
 x_338 = lean_box(0);
}
x_482 = l_Lean_Expr_hasLevelParam(x_335);
if (x_482 == 0)
{
uint8_t x_483; 
x_483 = l_Lean_Expr_hasFVar(x_335);
if (x_483 == 0)
{
uint8_t x_484; 
x_484 = l_Lean_Expr_hasMVar(x_335);
if (x_484 == 0)
{
lean_inc(x_335);
x_339 = x_335;
x_340 = x_8;
goto block_442;
}
else
{
lean_object* x_485; 
x_485 = lean_box(0);
x_443 = x_485;
goto block_481;
}
}
else
{
lean_object* x_486; 
x_486 = lean_box(0);
x_443 = x_486;
goto block_481;
}
}
else
{
lean_object* x_487; 
x_487 = lean_box(0);
x_443 = x_487;
goto block_481;
}
block_442:
{
lean_object* x_341; uint8_t x_433; 
x_433 = l_Lean_Expr_hasLevelParam(x_336);
if (x_433 == 0)
{
uint8_t x_434; 
x_434 = l_Lean_Expr_hasFVar(x_336);
if (x_434 == 0)
{
uint8_t x_435; 
x_435 = l_Lean_Expr_hasMVar(x_336);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_338);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_336);
x_436 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_436, 0, x_335);
lean_ctor_set(x_436, 1, x_336);
lean_ctor_set_uint64(x_436, sizeof(void*)*2, x_337);
x_437 = lean_expr_update_app(x_436, x_339, x_336);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_340);
return x_438;
}
else
{
lean_object* x_439; 
x_439 = lean_box(0);
x_341 = x_439;
goto block_432;
}
}
else
{
lean_object* x_440; 
x_440 = lean_box(0);
x_341 = x_440;
goto block_432;
}
}
else
{
lean_object* x_441; 
x_441 = lean_box(0);
x_341 = x_441;
goto block_432;
}
block_432:
{
lean_object* x_342; uint8_t x_343; 
lean_dec(x_341);
x_342 = lean_st_ref_get(x_3, x_340);
x_343 = !lean_is_exclusive(x_342);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_342, 0);
x_345 = lean_ctor_get(x_342, 1);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_346, x_336);
lean_dec(x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; 
lean_free_object(x_342);
lean_inc(x_336);
x_348 = l_Lean_Meta_Closure_collectExprAux(x_336, x_2, x_3, x_4, x_5, x_6, x_7, x_345);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_st_ref_take(x_3, x_350);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = !lean_is_exclusive(x_352);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_349);
lean_inc(x_336);
x_356 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_355, x_336, x_349);
lean_ctor_set(x_352, 1, x_356);
x_357 = lean_st_ref_set(x_3, x_352, x_353);
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_357, 0);
lean_dec(x_359);
if (lean_is_scalar(x_338)) {
 x_360 = lean_alloc_ctor(5, 2, 8);
} else {
 x_360 = x_338;
}
lean_ctor_set(x_360, 0, x_335);
lean_ctor_set(x_360, 1, x_336);
lean_ctor_set_uint64(x_360, sizeof(void*)*2, x_337);
x_361 = lean_expr_update_app(x_360, x_339, x_349);
lean_ctor_set(x_357, 0, x_361);
return x_357;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_362 = lean_ctor_get(x_357, 1);
lean_inc(x_362);
lean_dec(x_357);
if (lean_is_scalar(x_338)) {
 x_363 = lean_alloc_ctor(5, 2, 8);
} else {
 x_363 = x_338;
}
lean_ctor_set(x_363, 0, x_335);
lean_ctor_set(x_363, 1, x_336);
lean_ctor_set_uint64(x_363, sizeof(void*)*2, x_337);
x_364 = lean_expr_update_app(x_363, x_339, x_349);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_362);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_366 = lean_ctor_get(x_352, 0);
x_367 = lean_ctor_get(x_352, 1);
x_368 = lean_ctor_get(x_352, 2);
x_369 = lean_ctor_get(x_352, 3);
x_370 = lean_ctor_get(x_352, 4);
x_371 = lean_ctor_get(x_352, 5);
x_372 = lean_ctor_get(x_352, 6);
x_373 = lean_ctor_get(x_352, 7);
x_374 = lean_ctor_get(x_352, 8);
x_375 = lean_ctor_get(x_352, 9);
x_376 = lean_ctor_get(x_352, 10);
x_377 = lean_ctor_get(x_352, 11);
lean_inc(x_377);
lean_inc(x_376);
lean_inc(x_375);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_352);
lean_inc(x_349);
lean_inc(x_336);
x_378 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_367, x_336, x_349);
x_379 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_379, 0, x_366);
lean_ctor_set(x_379, 1, x_378);
lean_ctor_set(x_379, 2, x_368);
lean_ctor_set(x_379, 3, x_369);
lean_ctor_set(x_379, 4, x_370);
lean_ctor_set(x_379, 5, x_371);
lean_ctor_set(x_379, 6, x_372);
lean_ctor_set(x_379, 7, x_373);
lean_ctor_set(x_379, 8, x_374);
lean_ctor_set(x_379, 9, x_375);
lean_ctor_set(x_379, 10, x_376);
lean_ctor_set(x_379, 11, x_377);
x_380 = lean_st_ref_set(x_3, x_379, x_353);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_383 = lean_alloc_ctor(5, 2, 8);
} else {
 x_383 = x_338;
}
lean_ctor_set(x_383, 0, x_335);
lean_ctor_set(x_383, 1, x_336);
lean_ctor_set_uint64(x_383, sizeof(void*)*2, x_337);
x_384 = lean_expr_update_app(x_383, x_339, x_349);
if (lean_is_scalar(x_382)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_382;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_381);
return x_385;
}
}
else
{
uint8_t x_386; 
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
x_386 = !lean_is_exclusive(x_348);
if (x_386 == 0)
{
return x_348;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_348, 0);
x_388 = lean_ctor_get(x_348, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_348);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_390 = lean_ctor_get(x_347, 0);
lean_inc(x_390);
lean_dec(x_347);
if (lean_is_scalar(x_338)) {
 x_391 = lean_alloc_ctor(5, 2, 8);
} else {
 x_391 = x_338;
}
lean_ctor_set(x_391, 0, x_335);
lean_ctor_set(x_391, 1, x_336);
lean_ctor_set_uint64(x_391, sizeof(void*)*2, x_337);
x_392 = lean_expr_update_app(x_391, x_339, x_390);
lean_ctor_set(x_342, 0, x_392);
return x_342;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = lean_ctor_get(x_342, 0);
x_394 = lean_ctor_get(x_342, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_342);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_395, x_336);
lean_dec(x_395);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; 
lean_inc(x_336);
x_397 = l_Lean_Meta_Closure_collectExprAux(x_336, x_2, x_3, x_4, x_5, x_6, x_7, x_394);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_st_ref_take(x_3, x_399);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = lean_ctor_get(x_401, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_401, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_401, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_401, 4);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 5);
lean_inc(x_408);
x_409 = lean_ctor_get(x_401, 6);
lean_inc(x_409);
x_410 = lean_ctor_get(x_401, 7);
lean_inc(x_410);
x_411 = lean_ctor_get(x_401, 8);
lean_inc(x_411);
x_412 = lean_ctor_get(x_401, 9);
lean_inc(x_412);
x_413 = lean_ctor_get(x_401, 10);
lean_inc(x_413);
x_414 = lean_ctor_get(x_401, 11);
lean_inc(x_414);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 lean_ctor_release(x_401, 3);
 lean_ctor_release(x_401, 4);
 lean_ctor_release(x_401, 5);
 lean_ctor_release(x_401, 6);
 lean_ctor_release(x_401, 7);
 lean_ctor_release(x_401, 8);
 lean_ctor_release(x_401, 9);
 lean_ctor_release(x_401, 10);
 lean_ctor_release(x_401, 11);
 x_415 = x_401;
} else {
 lean_dec_ref(x_401);
 x_415 = lean_box(0);
}
lean_inc(x_398);
lean_inc(x_336);
x_416 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_404, x_336, x_398);
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(0, 12, 0);
} else {
 x_417 = x_415;
}
lean_ctor_set(x_417, 0, x_403);
lean_ctor_set(x_417, 1, x_416);
lean_ctor_set(x_417, 2, x_405);
lean_ctor_set(x_417, 3, x_406);
lean_ctor_set(x_417, 4, x_407);
lean_ctor_set(x_417, 5, x_408);
lean_ctor_set(x_417, 6, x_409);
lean_ctor_set(x_417, 7, x_410);
lean_ctor_set(x_417, 8, x_411);
lean_ctor_set(x_417, 9, x_412);
lean_ctor_set(x_417, 10, x_413);
lean_ctor_set(x_417, 11, x_414);
x_418 = lean_st_ref_set(x_3, x_417, x_402);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_420 = x_418;
} else {
 lean_dec_ref(x_418);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_421 = lean_alloc_ctor(5, 2, 8);
} else {
 x_421 = x_338;
}
lean_ctor_set(x_421, 0, x_335);
lean_ctor_set(x_421, 1, x_336);
lean_ctor_set_uint64(x_421, sizeof(void*)*2, x_337);
x_422 = lean_expr_update_app(x_421, x_339, x_398);
if (lean_is_scalar(x_420)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_420;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_419);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
x_424 = lean_ctor_get(x_397, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_397, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_426 = x_397;
} else {
 lean_dec_ref(x_397);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
return x_427;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_428 = lean_ctor_get(x_396, 0);
lean_inc(x_428);
lean_dec(x_396);
if (lean_is_scalar(x_338)) {
 x_429 = lean_alloc_ctor(5, 2, 8);
} else {
 x_429 = x_338;
}
lean_ctor_set(x_429, 0, x_335);
lean_ctor_set(x_429, 1, x_336);
lean_ctor_set_uint64(x_429, sizeof(void*)*2, x_337);
x_430 = lean_expr_update_app(x_429, x_339, x_428);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_394);
return x_431;
}
}
}
}
block_481:
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_443);
x_444 = lean_st_ref_get(x_3, x_8);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_447, x_335);
lean_dec(x_447);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_335);
x_449 = l_Lean_Meta_Closure_collectExprAux(x_335, x_2, x_3, x_4, x_5, x_6, x_7, x_446);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = lean_st_ref_take(x_3, x_451);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = !lean_is_exclusive(x_453);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_450);
lean_inc(x_335);
x_457 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_456, x_335, x_450);
lean_ctor_set(x_453, 1, x_457);
x_458 = lean_st_ref_set(x_3, x_453, x_454);
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
lean_dec(x_458);
x_339 = x_450;
x_340 = x_459;
goto block_442;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_460 = lean_ctor_get(x_453, 0);
x_461 = lean_ctor_get(x_453, 1);
x_462 = lean_ctor_get(x_453, 2);
x_463 = lean_ctor_get(x_453, 3);
x_464 = lean_ctor_get(x_453, 4);
x_465 = lean_ctor_get(x_453, 5);
x_466 = lean_ctor_get(x_453, 6);
x_467 = lean_ctor_get(x_453, 7);
x_468 = lean_ctor_get(x_453, 8);
x_469 = lean_ctor_get(x_453, 9);
x_470 = lean_ctor_get(x_453, 10);
x_471 = lean_ctor_get(x_453, 11);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_453);
lean_inc(x_450);
lean_inc(x_335);
x_472 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_461, x_335, x_450);
x_473 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_473, 0, x_460);
lean_ctor_set(x_473, 1, x_472);
lean_ctor_set(x_473, 2, x_462);
lean_ctor_set(x_473, 3, x_463);
lean_ctor_set(x_473, 4, x_464);
lean_ctor_set(x_473, 5, x_465);
lean_ctor_set(x_473, 6, x_466);
lean_ctor_set(x_473, 7, x_467);
lean_ctor_set(x_473, 8, x_468);
lean_ctor_set(x_473, 9, x_469);
lean_ctor_set(x_473, 10, x_470);
lean_ctor_set(x_473, 11, x_471);
x_474 = lean_st_ref_set(x_3, x_473, x_454);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
x_339 = x_450;
x_340 = x_475;
goto block_442;
}
}
else
{
uint8_t x_476; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_476 = !lean_is_exclusive(x_449);
if (x_476 == 0)
{
return x_449;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_449, 0);
x_478 = lean_ctor_get(x_449, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_449);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
}
else
{
lean_object* x_480; 
x_480 = lean_ctor_get(x_448, 0);
lean_inc(x_480);
lean_dec(x_448);
x_339 = x_480;
x_340 = x_446;
goto block_442;
}
}
}
case 6:
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; uint64_t x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_548; uint8_t x_587; 
x_488 = lean_ctor_get(x_1, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_1, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_1, 2);
lean_inc(x_490);
x_491 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_492 = x_1;
} else {
 lean_dec_ref(x_1);
 x_492 = lean_box(0);
}
x_587 = l_Lean_Expr_hasLevelParam(x_489);
if (x_587 == 0)
{
uint8_t x_588; 
x_588 = l_Lean_Expr_hasFVar(x_489);
if (x_588 == 0)
{
uint8_t x_589; 
x_589 = l_Lean_Expr_hasMVar(x_489);
if (x_589 == 0)
{
lean_inc(x_489);
x_493 = x_489;
x_494 = x_8;
goto block_547;
}
else
{
lean_object* x_590; 
x_590 = lean_box(0);
x_548 = x_590;
goto block_586;
}
}
else
{
lean_object* x_591; 
x_591 = lean_box(0);
x_548 = x_591;
goto block_586;
}
}
else
{
lean_object* x_592; 
x_592 = lean_box(0);
x_548 = x_592;
goto block_586;
}
block_547:
{
lean_object* x_495; lean_object* x_496; lean_object* x_502; uint8_t x_541; 
x_541 = l_Lean_Expr_hasLevelParam(x_490);
if (x_541 == 0)
{
uint8_t x_542; 
x_542 = l_Lean_Expr_hasFVar(x_490);
if (x_542 == 0)
{
uint8_t x_543; 
x_543 = l_Lean_Expr_hasMVar(x_490);
if (x_543 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_490);
x_495 = x_490;
x_496 = x_494;
goto block_501;
}
else
{
lean_object* x_544; 
x_544 = lean_box(0);
x_502 = x_544;
goto block_540;
}
}
else
{
lean_object* x_545; 
x_545 = lean_box(0);
x_502 = x_545;
goto block_540;
}
}
else
{
lean_object* x_546; 
x_546 = lean_box(0);
x_502 = x_546;
goto block_540;
}
block_501:
{
lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; 
if (lean_is_scalar(x_492)) {
 x_497 = lean_alloc_ctor(6, 3, 8);
} else {
 x_497 = x_492;
}
lean_ctor_set(x_497, 0, x_488);
lean_ctor_set(x_497, 1, x_489);
lean_ctor_set(x_497, 2, x_490);
lean_ctor_set_uint64(x_497, sizeof(void*)*3, x_491);
x_498 = (uint8_t)((x_491 << 24) >> 61);
x_499 = lean_expr_update_lambda(x_497, x_498, x_493, x_495);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_496);
return x_500;
}
block_540:
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_502);
x_503 = lean_st_ref_get(x_3, x_494);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_507 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_506, x_490);
lean_dec(x_506);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; 
lean_inc(x_490);
x_508 = l_Lean_Meta_Closure_collectExprAux(x_490, x_2, x_3, x_4, x_5, x_6, x_7, x_505);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_st_ref_take(x_3, x_510);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = !lean_is_exclusive(x_512);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_515 = lean_ctor_get(x_512, 1);
lean_inc(x_509);
lean_inc(x_490);
x_516 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_515, x_490, x_509);
lean_ctor_set(x_512, 1, x_516);
x_517 = lean_st_ref_set(x_3, x_512, x_513);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
lean_dec(x_517);
x_495 = x_509;
x_496 = x_518;
goto block_501;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_519 = lean_ctor_get(x_512, 0);
x_520 = lean_ctor_get(x_512, 1);
x_521 = lean_ctor_get(x_512, 2);
x_522 = lean_ctor_get(x_512, 3);
x_523 = lean_ctor_get(x_512, 4);
x_524 = lean_ctor_get(x_512, 5);
x_525 = lean_ctor_get(x_512, 6);
x_526 = lean_ctor_get(x_512, 7);
x_527 = lean_ctor_get(x_512, 8);
x_528 = lean_ctor_get(x_512, 9);
x_529 = lean_ctor_get(x_512, 10);
x_530 = lean_ctor_get(x_512, 11);
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
lean_inc(x_519);
lean_dec(x_512);
lean_inc(x_509);
lean_inc(x_490);
x_531 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_520, x_490, x_509);
x_532 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_532, 0, x_519);
lean_ctor_set(x_532, 1, x_531);
lean_ctor_set(x_532, 2, x_521);
lean_ctor_set(x_532, 3, x_522);
lean_ctor_set(x_532, 4, x_523);
lean_ctor_set(x_532, 5, x_524);
lean_ctor_set(x_532, 6, x_525);
lean_ctor_set(x_532, 7, x_526);
lean_ctor_set(x_532, 8, x_527);
lean_ctor_set(x_532, 9, x_528);
lean_ctor_set(x_532, 10, x_529);
lean_ctor_set(x_532, 11, x_530);
x_533 = lean_st_ref_set(x_3, x_532, x_513);
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
lean_dec(x_533);
x_495 = x_509;
x_496 = x_534;
goto block_501;
}
}
else
{
uint8_t x_535; 
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
x_535 = !lean_is_exclusive(x_508);
if (x_535 == 0)
{
return x_508;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_508, 0);
x_537 = lean_ctor_get(x_508, 1);
lean_inc(x_537);
lean_inc(x_536);
lean_dec(x_508);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
return x_538;
}
}
}
else
{
lean_object* x_539; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_539 = lean_ctor_get(x_507, 0);
lean_inc(x_539);
lean_dec(x_507);
x_495 = x_539;
x_496 = x_505;
goto block_501;
}
}
}
block_586:
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_548);
x_549 = lean_st_ref_get(x_3, x_8);
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_552, x_489);
lean_dec(x_552);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_489);
x_554 = l_Lean_Meta_Closure_collectExprAux(x_489, x_2, x_3, x_4, x_5, x_6, x_7, x_551);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_st_ref_take(x_3, x_556);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = !lean_is_exclusive(x_558);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_555);
lean_inc(x_489);
x_562 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_561, x_489, x_555);
lean_ctor_set(x_558, 1, x_562);
x_563 = lean_st_ref_set(x_3, x_558, x_559);
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
lean_dec(x_563);
x_493 = x_555;
x_494 = x_564;
goto block_547;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_565 = lean_ctor_get(x_558, 0);
x_566 = lean_ctor_get(x_558, 1);
x_567 = lean_ctor_get(x_558, 2);
x_568 = lean_ctor_get(x_558, 3);
x_569 = lean_ctor_get(x_558, 4);
x_570 = lean_ctor_get(x_558, 5);
x_571 = lean_ctor_get(x_558, 6);
x_572 = lean_ctor_get(x_558, 7);
x_573 = lean_ctor_get(x_558, 8);
x_574 = lean_ctor_get(x_558, 9);
x_575 = lean_ctor_get(x_558, 10);
x_576 = lean_ctor_get(x_558, 11);
lean_inc(x_576);
lean_inc(x_575);
lean_inc(x_574);
lean_inc(x_573);
lean_inc(x_572);
lean_inc(x_571);
lean_inc(x_570);
lean_inc(x_569);
lean_inc(x_568);
lean_inc(x_567);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_558);
lean_inc(x_555);
lean_inc(x_489);
x_577 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_566, x_489, x_555);
x_578 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_578, 0, x_565);
lean_ctor_set(x_578, 1, x_577);
lean_ctor_set(x_578, 2, x_567);
lean_ctor_set(x_578, 3, x_568);
lean_ctor_set(x_578, 4, x_569);
lean_ctor_set(x_578, 5, x_570);
lean_ctor_set(x_578, 6, x_571);
lean_ctor_set(x_578, 7, x_572);
lean_ctor_set(x_578, 8, x_573);
lean_ctor_set(x_578, 9, x_574);
lean_ctor_set(x_578, 10, x_575);
lean_ctor_set(x_578, 11, x_576);
x_579 = lean_st_ref_set(x_3, x_578, x_559);
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
x_493 = x_555;
x_494 = x_580;
goto block_547;
}
}
else
{
uint8_t x_581; 
lean_dec(x_492);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_581 = !lean_is_exclusive(x_554);
if (x_581 == 0)
{
return x_554;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_554, 0);
x_583 = lean_ctor_get(x_554, 1);
lean_inc(x_583);
lean_inc(x_582);
lean_dec(x_554);
x_584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
else
{
lean_object* x_585; 
x_585 = lean_ctor_get(x_553, 0);
lean_inc(x_585);
lean_dec(x_553);
x_493 = x_585;
x_494 = x_551;
goto block_547;
}
}
}
case 7:
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; uint64_t x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_653; uint8_t x_692; 
x_593 = lean_ctor_get(x_1, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_1, 1);
lean_inc(x_594);
x_595 = lean_ctor_get(x_1, 2);
lean_inc(x_595);
x_596 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_597 = x_1;
} else {
 lean_dec_ref(x_1);
 x_597 = lean_box(0);
}
x_692 = l_Lean_Expr_hasLevelParam(x_594);
if (x_692 == 0)
{
uint8_t x_693; 
x_693 = l_Lean_Expr_hasFVar(x_594);
if (x_693 == 0)
{
uint8_t x_694; 
x_694 = l_Lean_Expr_hasMVar(x_594);
if (x_694 == 0)
{
lean_inc(x_594);
x_598 = x_594;
x_599 = x_8;
goto block_652;
}
else
{
lean_object* x_695; 
x_695 = lean_box(0);
x_653 = x_695;
goto block_691;
}
}
else
{
lean_object* x_696; 
x_696 = lean_box(0);
x_653 = x_696;
goto block_691;
}
}
else
{
lean_object* x_697; 
x_697 = lean_box(0);
x_653 = x_697;
goto block_691;
}
block_652:
{
lean_object* x_600; lean_object* x_601; lean_object* x_607; uint8_t x_646; 
x_646 = l_Lean_Expr_hasLevelParam(x_595);
if (x_646 == 0)
{
uint8_t x_647; 
x_647 = l_Lean_Expr_hasFVar(x_595);
if (x_647 == 0)
{
uint8_t x_648; 
x_648 = l_Lean_Expr_hasMVar(x_595);
if (x_648 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_595);
x_600 = x_595;
x_601 = x_599;
goto block_606;
}
else
{
lean_object* x_649; 
x_649 = lean_box(0);
x_607 = x_649;
goto block_645;
}
}
else
{
lean_object* x_650; 
x_650 = lean_box(0);
x_607 = x_650;
goto block_645;
}
}
else
{
lean_object* x_651; 
x_651 = lean_box(0);
x_607 = x_651;
goto block_645;
}
block_606:
{
lean_object* x_602; uint8_t x_603; lean_object* x_604; lean_object* x_605; 
if (lean_is_scalar(x_597)) {
 x_602 = lean_alloc_ctor(7, 3, 8);
} else {
 x_602 = x_597;
}
lean_ctor_set(x_602, 0, x_593);
lean_ctor_set(x_602, 1, x_594);
lean_ctor_set(x_602, 2, x_595);
lean_ctor_set_uint64(x_602, sizeof(void*)*3, x_596);
x_603 = (uint8_t)((x_596 << 24) >> 61);
x_604 = lean_expr_update_forall(x_602, x_603, x_598, x_600);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_601);
return x_605;
}
block_645:
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_607);
x_608 = lean_st_ref_get(x_3, x_599);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_611, x_595);
lean_dec(x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; 
lean_inc(x_595);
x_613 = l_Lean_Meta_Closure_collectExprAux(x_595, x_2, x_3, x_4, x_5, x_6, x_7, x_610);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = lean_st_ref_take(x_3, x_615);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = !lean_is_exclusive(x_617);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_614);
lean_inc(x_595);
x_621 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_620, x_595, x_614);
lean_ctor_set(x_617, 1, x_621);
x_622 = lean_st_ref_set(x_3, x_617, x_618);
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
lean_dec(x_622);
x_600 = x_614;
x_601 = x_623;
goto block_606;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_624 = lean_ctor_get(x_617, 0);
x_625 = lean_ctor_get(x_617, 1);
x_626 = lean_ctor_get(x_617, 2);
x_627 = lean_ctor_get(x_617, 3);
x_628 = lean_ctor_get(x_617, 4);
x_629 = lean_ctor_get(x_617, 5);
x_630 = lean_ctor_get(x_617, 6);
x_631 = lean_ctor_get(x_617, 7);
x_632 = lean_ctor_get(x_617, 8);
x_633 = lean_ctor_get(x_617, 9);
x_634 = lean_ctor_get(x_617, 10);
x_635 = lean_ctor_get(x_617, 11);
lean_inc(x_635);
lean_inc(x_634);
lean_inc(x_633);
lean_inc(x_632);
lean_inc(x_631);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
lean_inc(x_627);
lean_inc(x_626);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_617);
lean_inc(x_614);
lean_inc(x_595);
x_636 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_625, x_595, x_614);
x_637 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_637, 0, x_624);
lean_ctor_set(x_637, 1, x_636);
lean_ctor_set(x_637, 2, x_626);
lean_ctor_set(x_637, 3, x_627);
lean_ctor_set(x_637, 4, x_628);
lean_ctor_set(x_637, 5, x_629);
lean_ctor_set(x_637, 6, x_630);
lean_ctor_set(x_637, 7, x_631);
lean_ctor_set(x_637, 8, x_632);
lean_ctor_set(x_637, 9, x_633);
lean_ctor_set(x_637, 10, x_634);
lean_ctor_set(x_637, 11, x_635);
x_638 = lean_st_ref_set(x_3, x_637, x_618);
x_639 = lean_ctor_get(x_638, 1);
lean_inc(x_639);
lean_dec(x_638);
x_600 = x_614;
x_601 = x_639;
goto block_606;
}
}
else
{
uint8_t x_640; 
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
x_640 = !lean_is_exclusive(x_613);
if (x_640 == 0)
{
return x_613;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_613, 0);
x_642 = lean_ctor_get(x_613, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_613);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
}
else
{
lean_object* x_644; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_644 = lean_ctor_get(x_612, 0);
lean_inc(x_644);
lean_dec(x_612);
x_600 = x_644;
x_601 = x_610;
goto block_606;
}
}
}
block_691:
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_653);
x_654 = lean_st_ref_get(x_3, x_8);
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_658 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_657, x_594);
lean_dec(x_657);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_594);
x_659 = l_Lean_Meta_Closure_collectExprAux(x_594, x_2, x_3, x_4, x_5, x_6, x_7, x_656);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
lean_dec(x_659);
x_662 = lean_st_ref_take(x_3, x_661);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_665 = !lean_is_exclusive(x_663);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_666 = lean_ctor_get(x_663, 1);
lean_inc(x_660);
lean_inc(x_594);
x_667 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_666, x_594, x_660);
lean_ctor_set(x_663, 1, x_667);
x_668 = lean_st_ref_set(x_3, x_663, x_664);
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
lean_dec(x_668);
x_598 = x_660;
x_599 = x_669;
goto block_652;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_670 = lean_ctor_get(x_663, 0);
x_671 = lean_ctor_get(x_663, 1);
x_672 = lean_ctor_get(x_663, 2);
x_673 = lean_ctor_get(x_663, 3);
x_674 = lean_ctor_get(x_663, 4);
x_675 = lean_ctor_get(x_663, 5);
x_676 = lean_ctor_get(x_663, 6);
x_677 = lean_ctor_get(x_663, 7);
x_678 = lean_ctor_get(x_663, 8);
x_679 = lean_ctor_get(x_663, 9);
x_680 = lean_ctor_get(x_663, 10);
x_681 = lean_ctor_get(x_663, 11);
lean_inc(x_681);
lean_inc(x_680);
lean_inc(x_679);
lean_inc(x_678);
lean_inc(x_677);
lean_inc(x_676);
lean_inc(x_675);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_663);
lean_inc(x_660);
lean_inc(x_594);
x_682 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_671, x_594, x_660);
x_683 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_683, 0, x_670);
lean_ctor_set(x_683, 1, x_682);
lean_ctor_set(x_683, 2, x_672);
lean_ctor_set(x_683, 3, x_673);
lean_ctor_set(x_683, 4, x_674);
lean_ctor_set(x_683, 5, x_675);
lean_ctor_set(x_683, 6, x_676);
lean_ctor_set(x_683, 7, x_677);
lean_ctor_set(x_683, 8, x_678);
lean_ctor_set(x_683, 9, x_679);
lean_ctor_set(x_683, 10, x_680);
lean_ctor_set(x_683, 11, x_681);
x_684 = lean_st_ref_set(x_3, x_683, x_664);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec(x_684);
x_598 = x_660;
x_599 = x_685;
goto block_652;
}
}
else
{
uint8_t x_686; 
lean_dec(x_597);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_686 = !lean_is_exclusive(x_659);
if (x_686 == 0)
{
return x_659;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_659, 0);
x_688 = lean_ctor_get(x_659, 1);
lean_inc(x_688);
lean_inc(x_687);
lean_dec(x_659);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
return x_689;
}
}
}
else
{
lean_object* x_690; 
x_690 = lean_ctor_get(x_658, 0);
lean_inc(x_690);
lean_dec(x_658);
x_598 = x_690;
x_599 = x_656;
goto block_652;
}
}
}
case 8:
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint64_t x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_856; uint8_t x_895; 
x_698 = lean_ctor_get(x_1, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_1, 1);
lean_inc(x_699);
x_700 = lean_ctor_get(x_1, 2);
lean_inc(x_700);
x_701 = lean_ctor_get(x_1, 3);
lean_inc(x_701);
x_702 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_703 = x_1;
} else {
 lean_dec_ref(x_1);
 x_703 = lean_box(0);
}
x_895 = l_Lean_Expr_hasLevelParam(x_699);
if (x_895 == 0)
{
uint8_t x_896; 
x_896 = l_Lean_Expr_hasFVar(x_699);
if (x_896 == 0)
{
uint8_t x_897; 
x_897 = l_Lean_Expr_hasMVar(x_699);
if (x_897 == 0)
{
lean_inc(x_699);
x_704 = x_699;
x_705 = x_8;
goto block_855;
}
else
{
lean_object* x_898; 
x_898 = lean_box(0);
x_856 = x_898;
goto block_894;
}
}
else
{
lean_object* x_899; 
x_899 = lean_box(0);
x_856 = x_899;
goto block_894;
}
}
else
{
lean_object* x_900; 
x_900 = lean_box(0);
x_856 = x_900;
goto block_894;
}
block_855:
{
lean_object* x_706; lean_object* x_707; lean_object* x_810; uint8_t x_849; 
x_849 = l_Lean_Expr_hasLevelParam(x_700);
if (x_849 == 0)
{
uint8_t x_850; 
x_850 = l_Lean_Expr_hasFVar(x_700);
if (x_850 == 0)
{
uint8_t x_851; 
x_851 = l_Lean_Expr_hasMVar(x_700);
if (x_851 == 0)
{
lean_inc(x_700);
x_706 = x_700;
x_707 = x_705;
goto block_809;
}
else
{
lean_object* x_852; 
x_852 = lean_box(0);
x_810 = x_852;
goto block_848;
}
}
else
{
lean_object* x_853; 
x_853 = lean_box(0);
x_810 = x_853;
goto block_848;
}
}
else
{
lean_object* x_854; 
x_854 = lean_box(0);
x_810 = x_854;
goto block_848;
}
block_809:
{
lean_object* x_708; uint8_t x_800; 
x_800 = l_Lean_Expr_hasLevelParam(x_701);
if (x_800 == 0)
{
uint8_t x_801; 
x_801 = l_Lean_Expr_hasFVar(x_701);
if (x_801 == 0)
{
uint8_t x_802; 
x_802 = l_Lean_Expr_hasMVar(x_701);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_703);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_701);
x_803 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_803, 0, x_698);
lean_ctor_set(x_803, 1, x_699);
lean_ctor_set(x_803, 2, x_700);
lean_ctor_set(x_803, 3, x_701);
lean_ctor_set_uint64(x_803, sizeof(void*)*4, x_702);
x_804 = lean_expr_update_let(x_803, x_704, x_706, x_701);
x_805 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_707);
return x_805;
}
else
{
lean_object* x_806; 
x_806 = lean_box(0);
x_708 = x_806;
goto block_799;
}
}
else
{
lean_object* x_807; 
x_807 = lean_box(0);
x_708 = x_807;
goto block_799;
}
}
else
{
lean_object* x_808; 
x_808 = lean_box(0);
x_708 = x_808;
goto block_799;
}
block_799:
{
lean_object* x_709; uint8_t x_710; 
lean_dec(x_708);
x_709 = lean_st_ref_get(x_3, x_707);
x_710 = !lean_is_exclusive(x_709);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_711 = lean_ctor_get(x_709, 0);
x_712 = lean_ctor_get(x_709, 1);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
x_714 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_713, x_701);
lean_dec(x_713);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; 
lean_free_object(x_709);
lean_inc(x_701);
x_715 = l_Lean_Meta_Closure_collectExprAux(x_701, x_2, x_3, x_4, x_5, x_6, x_7, x_712);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = lean_st_ref_take(x_3, x_717);
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_721 = !lean_is_exclusive(x_719);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; 
x_722 = lean_ctor_get(x_719, 1);
lean_inc(x_716);
lean_inc(x_701);
x_723 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_722, x_701, x_716);
lean_ctor_set(x_719, 1, x_723);
x_724 = lean_st_ref_set(x_3, x_719, x_720);
x_725 = !lean_is_exclusive(x_724);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_724, 0);
lean_dec(x_726);
if (lean_is_scalar(x_703)) {
 x_727 = lean_alloc_ctor(8, 4, 8);
} else {
 x_727 = x_703;
}
lean_ctor_set(x_727, 0, x_698);
lean_ctor_set(x_727, 1, x_699);
lean_ctor_set(x_727, 2, x_700);
lean_ctor_set(x_727, 3, x_701);
lean_ctor_set_uint64(x_727, sizeof(void*)*4, x_702);
x_728 = lean_expr_update_let(x_727, x_704, x_706, x_716);
lean_ctor_set(x_724, 0, x_728);
return x_724;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_ctor_get(x_724, 1);
lean_inc(x_729);
lean_dec(x_724);
if (lean_is_scalar(x_703)) {
 x_730 = lean_alloc_ctor(8, 4, 8);
} else {
 x_730 = x_703;
}
lean_ctor_set(x_730, 0, x_698);
lean_ctor_set(x_730, 1, x_699);
lean_ctor_set(x_730, 2, x_700);
lean_ctor_set(x_730, 3, x_701);
lean_ctor_set_uint64(x_730, sizeof(void*)*4, x_702);
x_731 = lean_expr_update_let(x_730, x_704, x_706, x_716);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_729);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_733 = lean_ctor_get(x_719, 0);
x_734 = lean_ctor_get(x_719, 1);
x_735 = lean_ctor_get(x_719, 2);
x_736 = lean_ctor_get(x_719, 3);
x_737 = lean_ctor_get(x_719, 4);
x_738 = lean_ctor_get(x_719, 5);
x_739 = lean_ctor_get(x_719, 6);
x_740 = lean_ctor_get(x_719, 7);
x_741 = lean_ctor_get(x_719, 8);
x_742 = lean_ctor_get(x_719, 9);
x_743 = lean_ctor_get(x_719, 10);
x_744 = lean_ctor_get(x_719, 11);
lean_inc(x_744);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_741);
lean_inc(x_740);
lean_inc(x_739);
lean_inc(x_738);
lean_inc(x_737);
lean_inc(x_736);
lean_inc(x_735);
lean_inc(x_734);
lean_inc(x_733);
lean_dec(x_719);
lean_inc(x_716);
lean_inc(x_701);
x_745 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_734, x_701, x_716);
x_746 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_746, 0, x_733);
lean_ctor_set(x_746, 1, x_745);
lean_ctor_set(x_746, 2, x_735);
lean_ctor_set(x_746, 3, x_736);
lean_ctor_set(x_746, 4, x_737);
lean_ctor_set(x_746, 5, x_738);
lean_ctor_set(x_746, 6, x_739);
lean_ctor_set(x_746, 7, x_740);
lean_ctor_set(x_746, 8, x_741);
lean_ctor_set(x_746, 9, x_742);
lean_ctor_set(x_746, 10, x_743);
lean_ctor_set(x_746, 11, x_744);
x_747 = lean_st_ref_set(x_3, x_746, x_720);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_749 = x_747;
} else {
 lean_dec_ref(x_747);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_750 = lean_alloc_ctor(8, 4, 8);
} else {
 x_750 = x_703;
}
lean_ctor_set(x_750, 0, x_698);
lean_ctor_set(x_750, 1, x_699);
lean_ctor_set(x_750, 2, x_700);
lean_ctor_set(x_750, 3, x_701);
lean_ctor_set_uint64(x_750, sizeof(void*)*4, x_702);
x_751 = lean_expr_update_let(x_750, x_704, x_706, x_716);
if (lean_is_scalar(x_749)) {
 x_752 = lean_alloc_ctor(0, 2, 0);
} else {
 x_752 = x_749;
}
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_748);
return x_752;
}
}
else
{
uint8_t x_753; 
lean_dec(x_706);
lean_dec(x_704);
lean_dec(x_703);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec(x_698);
x_753 = !lean_is_exclusive(x_715);
if (x_753 == 0)
{
return x_715;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_715, 0);
x_755 = lean_ctor_get(x_715, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_715);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_757 = lean_ctor_get(x_714, 0);
lean_inc(x_757);
lean_dec(x_714);
if (lean_is_scalar(x_703)) {
 x_758 = lean_alloc_ctor(8, 4, 8);
} else {
 x_758 = x_703;
}
lean_ctor_set(x_758, 0, x_698);
lean_ctor_set(x_758, 1, x_699);
lean_ctor_set(x_758, 2, x_700);
lean_ctor_set(x_758, 3, x_701);
lean_ctor_set_uint64(x_758, sizeof(void*)*4, x_702);
x_759 = lean_expr_update_let(x_758, x_704, x_706, x_757);
lean_ctor_set(x_709, 0, x_759);
return x_709;
}
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_760 = lean_ctor_get(x_709, 0);
x_761 = lean_ctor_get(x_709, 1);
lean_inc(x_761);
lean_inc(x_760);
lean_dec(x_709);
x_762 = lean_ctor_get(x_760, 1);
lean_inc(x_762);
lean_dec(x_760);
x_763 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_762, x_701);
lean_dec(x_762);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; 
lean_inc(x_701);
x_764 = l_Lean_Meta_Closure_collectExprAux(x_701, x_2, x_3, x_4, x_5, x_6, x_7, x_761);
if (lean_obj_tag(x_764) == 0)
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_765 = lean_ctor_get(x_764, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_764, 1);
lean_inc(x_766);
lean_dec(x_764);
x_767 = lean_st_ref_take(x_3, x_766);
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_767, 1);
lean_inc(x_769);
lean_dec(x_767);
x_770 = lean_ctor_get(x_768, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_768, 1);
lean_inc(x_771);
x_772 = lean_ctor_get(x_768, 2);
lean_inc(x_772);
x_773 = lean_ctor_get(x_768, 3);
lean_inc(x_773);
x_774 = lean_ctor_get(x_768, 4);
lean_inc(x_774);
x_775 = lean_ctor_get(x_768, 5);
lean_inc(x_775);
x_776 = lean_ctor_get(x_768, 6);
lean_inc(x_776);
x_777 = lean_ctor_get(x_768, 7);
lean_inc(x_777);
x_778 = lean_ctor_get(x_768, 8);
lean_inc(x_778);
x_779 = lean_ctor_get(x_768, 9);
lean_inc(x_779);
x_780 = lean_ctor_get(x_768, 10);
lean_inc(x_780);
x_781 = lean_ctor_get(x_768, 11);
lean_inc(x_781);
if (lean_is_exclusive(x_768)) {
 lean_ctor_release(x_768, 0);
 lean_ctor_release(x_768, 1);
 lean_ctor_release(x_768, 2);
 lean_ctor_release(x_768, 3);
 lean_ctor_release(x_768, 4);
 lean_ctor_release(x_768, 5);
 lean_ctor_release(x_768, 6);
 lean_ctor_release(x_768, 7);
 lean_ctor_release(x_768, 8);
 lean_ctor_release(x_768, 9);
 lean_ctor_release(x_768, 10);
 lean_ctor_release(x_768, 11);
 x_782 = x_768;
} else {
 lean_dec_ref(x_768);
 x_782 = lean_box(0);
}
lean_inc(x_765);
lean_inc(x_701);
x_783 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_771, x_701, x_765);
if (lean_is_scalar(x_782)) {
 x_784 = lean_alloc_ctor(0, 12, 0);
} else {
 x_784 = x_782;
}
lean_ctor_set(x_784, 0, x_770);
lean_ctor_set(x_784, 1, x_783);
lean_ctor_set(x_784, 2, x_772);
lean_ctor_set(x_784, 3, x_773);
lean_ctor_set(x_784, 4, x_774);
lean_ctor_set(x_784, 5, x_775);
lean_ctor_set(x_784, 6, x_776);
lean_ctor_set(x_784, 7, x_777);
lean_ctor_set(x_784, 8, x_778);
lean_ctor_set(x_784, 9, x_779);
lean_ctor_set(x_784, 10, x_780);
lean_ctor_set(x_784, 11, x_781);
x_785 = lean_st_ref_set(x_3, x_784, x_769);
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_787 = x_785;
} else {
 lean_dec_ref(x_785);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_788 = lean_alloc_ctor(8, 4, 8);
} else {
 x_788 = x_703;
}
lean_ctor_set(x_788, 0, x_698);
lean_ctor_set(x_788, 1, x_699);
lean_ctor_set(x_788, 2, x_700);
lean_ctor_set(x_788, 3, x_701);
lean_ctor_set_uint64(x_788, sizeof(void*)*4, x_702);
x_789 = lean_expr_update_let(x_788, x_704, x_706, x_765);
if (lean_is_scalar(x_787)) {
 x_790 = lean_alloc_ctor(0, 2, 0);
} else {
 x_790 = x_787;
}
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_786);
return x_790;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_706);
lean_dec(x_704);
lean_dec(x_703);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec(x_698);
x_791 = lean_ctor_get(x_764, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_764, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_764)) {
 lean_ctor_release(x_764, 0);
 lean_ctor_release(x_764, 1);
 x_793 = x_764;
} else {
 lean_dec_ref(x_764);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_795 = lean_ctor_get(x_763, 0);
lean_inc(x_795);
lean_dec(x_763);
if (lean_is_scalar(x_703)) {
 x_796 = lean_alloc_ctor(8, 4, 8);
} else {
 x_796 = x_703;
}
lean_ctor_set(x_796, 0, x_698);
lean_ctor_set(x_796, 1, x_699);
lean_ctor_set(x_796, 2, x_700);
lean_ctor_set(x_796, 3, x_701);
lean_ctor_set_uint64(x_796, sizeof(void*)*4, x_702);
x_797 = lean_expr_update_let(x_796, x_704, x_706, x_795);
x_798 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_761);
return x_798;
}
}
}
}
block_848:
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
lean_dec(x_810);
x_811 = lean_st_ref_get(x_3, x_705);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_814 = lean_ctor_get(x_812, 1);
lean_inc(x_814);
lean_dec(x_812);
x_815 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_814, x_700);
lean_dec(x_814);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_700);
x_816 = l_Lean_Meta_Closure_collectExprAux(x_700, x_2, x_3, x_4, x_5, x_6, x_7, x_813);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; uint8_t x_822; 
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
x_819 = lean_st_ref_take(x_3, x_818);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
x_822 = !lean_is_exclusive(x_820);
if (x_822 == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_823 = lean_ctor_get(x_820, 1);
lean_inc(x_817);
lean_inc(x_700);
x_824 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_823, x_700, x_817);
lean_ctor_set(x_820, 1, x_824);
x_825 = lean_st_ref_set(x_3, x_820, x_821);
x_826 = lean_ctor_get(x_825, 1);
lean_inc(x_826);
lean_dec(x_825);
x_706 = x_817;
x_707 = x_826;
goto block_809;
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_827 = lean_ctor_get(x_820, 0);
x_828 = lean_ctor_get(x_820, 1);
x_829 = lean_ctor_get(x_820, 2);
x_830 = lean_ctor_get(x_820, 3);
x_831 = lean_ctor_get(x_820, 4);
x_832 = lean_ctor_get(x_820, 5);
x_833 = lean_ctor_get(x_820, 6);
x_834 = lean_ctor_get(x_820, 7);
x_835 = lean_ctor_get(x_820, 8);
x_836 = lean_ctor_get(x_820, 9);
x_837 = lean_ctor_get(x_820, 10);
x_838 = lean_ctor_get(x_820, 11);
lean_inc(x_838);
lean_inc(x_837);
lean_inc(x_836);
lean_inc(x_835);
lean_inc(x_834);
lean_inc(x_833);
lean_inc(x_832);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_inc(x_828);
lean_inc(x_827);
lean_dec(x_820);
lean_inc(x_817);
lean_inc(x_700);
x_839 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_828, x_700, x_817);
x_840 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_840, 0, x_827);
lean_ctor_set(x_840, 1, x_839);
lean_ctor_set(x_840, 2, x_829);
lean_ctor_set(x_840, 3, x_830);
lean_ctor_set(x_840, 4, x_831);
lean_ctor_set(x_840, 5, x_832);
lean_ctor_set(x_840, 6, x_833);
lean_ctor_set(x_840, 7, x_834);
lean_ctor_set(x_840, 8, x_835);
lean_ctor_set(x_840, 9, x_836);
lean_ctor_set(x_840, 10, x_837);
lean_ctor_set(x_840, 11, x_838);
x_841 = lean_st_ref_set(x_3, x_840, x_821);
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
lean_dec(x_841);
x_706 = x_817;
x_707 = x_842;
goto block_809;
}
}
else
{
uint8_t x_843; 
lean_dec(x_704);
lean_dec(x_703);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_843 = !lean_is_exclusive(x_816);
if (x_843 == 0)
{
return x_816;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_844 = lean_ctor_get(x_816, 0);
x_845 = lean_ctor_get(x_816, 1);
lean_inc(x_845);
lean_inc(x_844);
lean_dec(x_816);
x_846 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_846, 0, x_844);
lean_ctor_set(x_846, 1, x_845);
return x_846;
}
}
}
else
{
lean_object* x_847; 
x_847 = lean_ctor_get(x_815, 0);
lean_inc(x_847);
lean_dec(x_815);
x_706 = x_847;
x_707 = x_813;
goto block_809;
}
}
}
block_894:
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec(x_856);
x_857 = lean_st_ref_get(x_3, x_8);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
lean_dec(x_858);
x_861 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_860, x_699);
lean_dec(x_860);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_699);
x_862 = l_Lean_Meta_Closure_collectExprAux(x_699, x_2, x_3, x_4, x_5, x_6, x_7, x_859);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; uint8_t x_868; 
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
lean_dec(x_862);
x_865 = lean_st_ref_take(x_3, x_864);
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
x_868 = !lean_is_exclusive(x_866);
if (x_868 == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_866, 1);
lean_inc(x_863);
lean_inc(x_699);
x_870 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_869, x_699, x_863);
lean_ctor_set(x_866, 1, x_870);
x_871 = lean_st_ref_set(x_3, x_866, x_867);
x_872 = lean_ctor_get(x_871, 1);
lean_inc(x_872);
lean_dec(x_871);
x_704 = x_863;
x_705 = x_872;
goto block_855;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_873 = lean_ctor_get(x_866, 0);
x_874 = lean_ctor_get(x_866, 1);
x_875 = lean_ctor_get(x_866, 2);
x_876 = lean_ctor_get(x_866, 3);
x_877 = lean_ctor_get(x_866, 4);
x_878 = lean_ctor_get(x_866, 5);
x_879 = lean_ctor_get(x_866, 6);
x_880 = lean_ctor_get(x_866, 7);
x_881 = lean_ctor_get(x_866, 8);
x_882 = lean_ctor_get(x_866, 9);
x_883 = lean_ctor_get(x_866, 10);
x_884 = lean_ctor_get(x_866, 11);
lean_inc(x_884);
lean_inc(x_883);
lean_inc(x_882);
lean_inc(x_881);
lean_inc(x_880);
lean_inc(x_879);
lean_inc(x_878);
lean_inc(x_877);
lean_inc(x_876);
lean_inc(x_875);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_866);
lean_inc(x_863);
lean_inc(x_699);
x_885 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_874, x_699, x_863);
x_886 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_886, 0, x_873);
lean_ctor_set(x_886, 1, x_885);
lean_ctor_set(x_886, 2, x_875);
lean_ctor_set(x_886, 3, x_876);
lean_ctor_set(x_886, 4, x_877);
lean_ctor_set(x_886, 5, x_878);
lean_ctor_set(x_886, 6, x_879);
lean_ctor_set(x_886, 7, x_880);
lean_ctor_set(x_886, 8, x_881);
lean_ctor_set(x_886, 9, x_882);
lean_ctor_set(x_886, 10, x_883);
lean_ctor_set(x_886, 11, x_884);
x_887 = lean_st_ref_set(x_3, x_886, x_867);
x_888 = lean_ctor_get(x_887, 1);
lean_inc(x_888);
lean_dec(x_887);
x_704 = x_863;
x_705 = x_888;
goto block_855;
}
}
else
{
uint8_t x_889; 
lean_dec(x_703);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_889 = !lean_is_exclusive(x_862);
if (x_889 == 0)
{
return x_862;
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_890 = lean_ctor_get(x_862, 0);
x_891 = lean_ctor_get(x_862, 1);
lean_inc(x_891);
lean_inc(x_890);
lean_dec(x_862);
x_892 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_892, 0, x_890);
lean_ctor_set(x_892, 1, x_891);
return x_892;
}
}
}
else
{
lean_object* x_893; 
x_893 = lean_ctor_get(x_861, 0);
lean_inc(x_893);
lean_dec(x_861);
x_704 = x_893;
x_705 = x_859;
goto block_855;
}
}
}
case 10:
{
lean_object* x_901; lean_object* x_902; uint64_t x_903; lean_object* x_904; lean_object* x_905; uint8_t x_997; 
x_901 = lean_ctor_get(x_1, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_1, 1);
lean_inc(x_902);
x_903 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_904 = x_1;
} else {
 lean_dec_ref(x_1);
 x_904 = lean_box(0);
}
x_997 = l_Lean_Expr_hasLevelParam(x_902);
if (x_997 == 0)
{
uint8_t x_998; 
x_998 = l_Lean_Expr_hasFVar(x_902);
if (x_998 == 0)
{
uint8_t x_999; 
x_999 = l_Lean_Expr_hasMVar(x_902);
if (x_999 == 0)
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_904);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_902);
x_1000 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_1000, 0, x_901);
lean_ctor_set(x_1000, 1, x_902);
lean_ctor_set_uint64(x_1000, sizeof(void*)*2, x_903);
x_1001 = lean_expr_update_mdata(x_1000, x_902);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_8);
return x_1002;
}
else
{
lean_object* x_1003; 
x_1003 = lean_box(0);
x_905 = x_1003;
goto block_996;
}
}
else
{
lean_object* x_1004; 
x_1004 = lean_box(0);
x_905 = x_1004;
goto block_996;
}
}
else
{
lean_object* x_1005; 
x_1005 = lean_box(0);
x_905 = x_1005;
goto block_996;
}
block_996:
{
lean_object* x_906; uint8_t x_907; 
lean_dec(x_905);
x_906 = lean_st_ref_get(x_3, x_8);
x_907 = !lean_is_exclusive(x_906);
if (x_907 == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_908 = lean_ctor_get(x_906, 0);
x_909 = lean_ctor_get(x_906, 1);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_910, x_902);
lean_dec(x_910);
if (lean_obj_tag(x_911) == 0)
{
lean_object* x_912; 
lean_free_object(x_906);
lean_inc(x_902);
x_912 = l_Lean_Meta_Closure_collectExprAux(x_902, x_2, x_3, x_4, x_5, x_6, x_7, x_909);
if (lean_obj_tag(x_912) == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; uint8_t x_918; 
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
x_915 = lean_st_ref_take(x_3, x_914);
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
x_918 = !lean_is_exclusive(x_916);
if (x_918 == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; uint8_t x_922; 
x_919 = lean_ctor_get(x_916, 1);
lean_inc(x_913);
lean_inc(x_902);
x_920 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_919, x_902, x_913);
lean_ctor_set(x_916, 1, x_920);
x_921 = lean_st_ref_set(x_3, x_916, x_917);
x_922 = !lean_is_exclusive(x_921);
if (x_922 == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_923 = lean_ctor_get(x_921, 0);
lean_dec(x_923);
if (lean_is_scalar(x_904)) {
 x_924 = lean_alloc_ctor(10, 2, 8);
} else {
 x_924 = x_904;
}
lean_ctor_set(x_924, 0, x_901);
lean_ctor_set(x_924, 1, x_902);
lean_ctor_set_uint64(x_924, sizeof(void*)*2, x_903);
x_925 = lean_expr_update_mdata(x_924, x_913);
lean_ctor_set(x_921, 0, x_925);
return x_921;
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_926 = lean_ctor_get(x_921, 1);
lean_inc(x_926);
lean_dec(x_921);
if (lean_is_scalar(x_904)) {
 x_927 = lean_alloc_ctor(10, 2, 8);
} else {
 x_927 = x_904;
}
lean_ctor_set(x_927, 0, x_901);
lean_ctor_set(x_927, 1, x_902);
lean_ctor_set_uint64(x_927, sizeof(void*)*2, x_903);
x_928 = lean_expr_update_mdata(x_927, x_913);
x_929 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_929, 0, x_928);
lean_ctor_set(x_929, 1, x_926);
return x_929;
}
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_930 = lean_ctor_get(x_916, 0);
x_931 = lean_ctor_get(x_916, 1);
x_932 = lean_ctor_get(x_916, 2);
x_933 = lean_ctor_get(x_916, 3);
x_934 = lean_ctor_get(x_916, 4);
x_935 = lean_ctor_get(x_916, 5);
x_936 = lean_ctor_get(x_916, 6);
x_937 = lean_ctor_get(x_916, 7);
x_938 = lean_ctor_get(x_916, 8);
x_939 = lean_ctor_get(x_916, 9);
x_940 = lean_ctor_get(x_916, 10);
x_941 = lean_ctor_get(x_916, 11);
lean_inc(x_941);
lean_inc(x_940);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
lean_inc(x_936);
lean_inc(x_935);
lean_inc(x_934);
lean_inc(x_933);
lean_inc(x_932);
lean_inc(x_931);
lean_inc(x_930);
lean_dec(x_916);
lean_inc(x_913);
lean_inc(x_902);
x_942 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_931, x_902, x_913);
x_943 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_943, 0, x_930);
lean_ctor_set(x_943, 1, x_942);
lean_ctor_set(x_943, 2, x_932);
lean_ctor_set(x_943, 3, x_933);
lean_ctor_set(x_943, 4, x_934);
lean_ctor_set(x_943, 5, x_935);
lean_ctor_set(x_943, 6, x_936);
lean_ctor_set(x_943, 7, x_937);
lean_ctor_set(x_943, 8, x_938);
lean_ctor_set(x_943, 9, x_939);
lean_ctor_set(x_943, 10, x_940);
lean_ctor_set(x_943, 11, x_941);
x_944 = lean_st_ref_set(x_3, x_943, x_917);
x_945 = lean_ctor_get(x_944, 1);
lean_inc(x_945);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 lean_ctor_release(x_944, 1);
 x_946 = x_944;
} else {
 lean_dec_ref(x_944);
 x_946 = lean_box(0);
}
if (lean_is_scalar(x_904)) {
 x_947 = lean_alloc_ctor(10, 2, 8);
} else {
 x_947 = x_904;
}
lean_ctor_set(x_947, 0, x_901);
lean_ctor_set(x_947, 1, x_902);
lean_ctor_set_uint64(x_947, sizeof(void*)*2, x_903);
x_948 = lean_expr_update_mdata(x_947, x_913);
if (lean_is_scalar(x_946)) {
 x_949 = lean_alloc_ctor(0, 2, 0);
} else {
 x_949 = x_946;
}
lean_ctor_set(x_949, 0, x_948);
lean_ctor_set(x_949, 1, x_945);
return x_949;
}
}
else
{
uint8_t x_950; 
lean_dec(x_904);
lean_dec(x_902);
lean_dec(x_901);
x_950 = !lean_is_exclusive(x_912);
if (x_950 == 0)
{
return x_912;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_912, 0);
x_952 = lean_ctor_get(x_912, 1);
lean_inc(x_952);
lean_inc(x_951);
lean_dec(x_912);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
return x_953;
}
}
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_954 = lean_ctor_get(x_911, 0);
lean_inc(x_954);
lean_dec(x_911);
if (lean_is_scalar(x_904)) {
 x_955 = lean_alloc_ctor(10, 2, 8);
} else {
 x_955 = x_904;
}
lean_ctor_set(x_955, 0, x_901);
lean_ctor_set(x_955, 1, x_902);
lean_ctor_set_uint64(x_955, sizeof(void*)*2, x_903);
x_956 = lean_expr_update_mdata(x_955, x_954);
lean_ctor_set(x_906, 0, x_956);
return x_906;
}
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_957 = lean_ctor_get(x_906, 0);
x_958 = lean_ctor_get(x_906, 1);
lean_inc(x_958);
lean_inc(x_957);
lean_dec(x_906);
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
lean_dec(x_957);
x_960 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_959, x_902);
lean_dec(x_959);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; 
lean_inc(x_902);
x_961 = l_Lean_Meta_Closure_collectExprAux(x_902, x_2, x_3, x_4, x_5, x_6, x_7, x_958);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_964 = lean_st_ref_take(x_3, x_963);
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec(x_964);
x_967 = lean_ctor_get(x_965, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_965, 1);
lean_inc(x_968);
x_969 = lean_ctor_get(x_965, 2);
lean_inc(x_969);
x_970 = lean_ctor_get(x_965, 3);
lean_inc(x_970);
x_971 = lean_ctor_get(x_965, 4);
lean_inc(x_971);
x_972 = lean_ctor_get(x_965, 5);
lean_inc(x_972);
x_973 = lean_ctor_get(x_965, 6);
lean_inc(x_973);
x_974 = lean_ctor_get(x_965, 7);
lean_inc(x_974);
x_975 = lean_ctor_get(x_965, 8);
lean_inc(x_975);
x_976 = lean_ctor_get(x_965, 9);
lean_inc(x_976);
x_977 = lean_ctor_get(x_965, 10);
lean_inc(x_977);
x_978 = lean_ctor_get(x_965, 11);
lean_inc(x_978);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 lean_ctor_release(x_965, 2);
 lean_ctor_release(x_965, 3);
 lean_ctor_release(x_965, 4);
 lean_ctor_release(x_965, 5);
 lean_ctor_release(x_965, 6);
 lean_ctor_release(x_965, 7);
 lean_ctor_release(x_965, 8);
 lean_ctor_release(x_965, 9);
 lean_ctor_release(x_965, 10);
 lean_ctor_release(x_965, 11);
 x_979 = x_965;
} else {
 lean_dec_ref(x_965);
 x_979 = lean_box(0);
}
lean_inc(x_962);
lean_inc(x_902);
x_980 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_968, x_902, x_962);
if (lean_is_scalar(x_979)) {
 x_981 = lean_alloc_ctor(0, 12, 0);
} else {
 x_981 = x_979;
}
lean_ctor_set(x_981, 0, x_967);
lean_ctor_set(x_981, 1, x_980);
lean_ctor_set(x_981, 2, x_969);
lean_ctor_set(x_981, 3, x_970);
lean_ctor_set(x_981, 4, x_971);
lean_ctor_set(x_981, 5, x_972);
lean_ctor_set(x_981, 6, x_973);
lean_ctor_set(x_981, 7, x_974);
lean_ctor_set(x_981, 8, x_975);
lean_ctor_set(x_981, 9, x_976);
lean_ctor_set(x_981, 10, x_977);
lean_ctor_set(x_981, 11, x_978);
x_982 = lean_st_ref_set(x_3, x_981, x_966);
x_983 = lean_ctor_get(x_982, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_984 = x_982;
} else {
 lean_dec_ref(x_982);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_904)) {
 x_985 = lean_alloc_ctor(10, 2, 8);
} else {
 x_985 = x_904;
}
lean_ctor_set(x_985, 0, x_901);
lean_ctor_set(x_985, 1, x_902);
lean_ctor_set_uint64(x_985, sizeof(void*)*2, x_903);
x_986 = lean_expr_update_mdata(x_985, x_962);
if (lean_is_scalar(x_984)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_984;
}
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_983);
return x_987;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_904);
lean_dec(x_902);
lean_dec(x_901);
x_988 = lean_ctor_get(x_961, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_961, 1);
lean_inc(x_989);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_990 = x_961;
} else {
 lean_dec_ref(x_961);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(1, 2, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_988);
lean_ctor_set(x_991, 1, x_989);
return x_991;
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_992 = lean_ctor_get(x_960, 0);
lean_inc(x_992);
lean_dec(x_960);
if (lean_is_scalar(x_904)) {
 x_993 = lean_alloc_ctor(10, 2, 8);
} else {
 x_993 = x_904;
}
lean_ctor_set(x_993, 0, x_901);
lean_ctor_set(x_993, 1, x_902);
lean_ctor_set_uint64(x_993, sizeof(void*)*2, x_903);
x_994 = lean_expr_update_mdata(x_993, x_992);
x_995 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_995, 0, x_994);
lean_ctor_set(x_995, 1, x_958);
return x_995;
}
}
}
}
case 11:
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; uint64_t x_1009; lean_object* x_1010; lean_object* x_1011; uint8_t x_1103; 
x_1006 = lean_ctor_get(x_1, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1, 1);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1, 2);
lean_inc(x_1008);
x_1009 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_1010 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1010 = lean_box(0);
}
x_1103 = l_Lean_Expr_hasLevelParam(x_1008);
if (x_1103 == 0)
{
uint8_t x_1104; 
x_1104 = l_Lean_Expr_hasFVar(x_1008);
if (x_1104 == 0)
{
uint8_t x_1105; 
x_1105 = l_Lean_Expr_hasMVar(x_1008);
if (x_1105 == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_1010);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_1008);
x_1106 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_1106, 0, x_1006);
lean_ctor_set(x_1106, 1, x_1007);
lean_ctor_set(x_1106, 2, x_1008);
lean_ctor_set_uint64(x_1106, sizeof(void*)*3, x_1009);
x_1107 = lean_expr_update_proj(x_1106, x_1008);
x_1108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_8);
return x_1108;
}
else
{
lean_object* x_1109; 
x_1109 = lean_box(0);
x_1011 = x_1109;
goto block_1102;
}
}
else
{
lean_object* x_1110; 
x_1110 = lean_box(0);
x_1011 = x_1110;
goto block_1102;
}
}
else
{
lean_object* x_1111; 
x_1111 = lean_box(0);
x_1011 = x_1111;
goto block_1102;
}
block_1102:
{
lean_object* x_1012; uint8_t x_1013; 
lean_dec(x_1011);
x_1012 = lean_st_ref_get(x_3, x_8);
x_1013 = !lean_is_exclusive(x_1012);
if (x_1013 == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1014 = lean_ctor_get(x_1012, 0);
x_1015 = lean_ctor_get(x_1012, 1);
x_1016 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
lean_dec(x_1014);
x_1017 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1016, x_1008);
lean_dec(x_1016);
if (lean_obj_tag(x_1017) == 0)
{
lean_object* x_1018; 
lean_free_object(x_1012);
lean_inc(x_1008);
x_1018 = l_Lean_Meta_Closure_collectExprAux(x_1008, x_2, x_3, x_4, x_5, x_6, x_7, x_1015);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; 
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
lean_dec(x_1018);
x_1021 = lean_st_ref_take(x_3, x_1020);
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
lean_dec(x_1021);
x_1024 = !lean_is_exclusive(x_1022);
if (x_1024 == 0)
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; uint8_t x_1028; 
x_1025 = lean_ctor_get(x_1022, 1);
lean_inc(x_1019);
lean_inc(x_1008);
x_1026 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1025, x_1008, x_1019);
lean_ctor_set(x_1022, 1, x_1026);
x_1027 = lean_st_ref_set(x_3, x_1022, x_1023);
x_1028 = !lean_is_exclusive(x_1027);
if (x_1028 == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_1027, 0);
lean_dec(x_1029);
if (lean_is_scalar(x_1010)) {
 x_1030 = lean_alloc_ctor(11, 3, 8);
} else {
 x_1030 = x_1010;
}
lean_ctor_set(x_1030, 0, x_1006);
lean_ctor_set(x_1030, 1, x_1007);
lean_ctor_set(x_1030, 2, x_1008);
lean_ctor_set_uint64(x_1030, sizeof(void*)*3, x_1009);
x_1031 = lean_expr_update_proj(x_1030, x_1019);
lean_ctor_set(x_1027, 0, x_1031);
return x_1027;
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1032 = lean_ctor_get(x_1027, 1);
lean_inc(x_1032);
lean_dec(x_1027);
if (lean_is_scalar(x_1010)) {
 x_1033 = lean_alloc_ctor(11, 3, 8);
} else {
 x_1033 = x_1010;
}
lean_ctor_set(x_1033, 0, x_1006);
lean_ctor_set(x_1033, 1, x_1007);
lean_ctor_set(x_1033, 2, x_1008);
lean_ctor_set_uint64(x_1033, sizeof(void*)*3, x_1009);
x_1034 = lean_expr_update_proj(x_1033, x_1019);
x_1035 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1035, 0, x_1034);
lean_ctor_set(x_1035, 1, x_1032);
return x_1035;
}
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1036 = lean_ctor_get(x_1022, 0);
x_1037 = lean_ctor_get(x_1022, 1);
x_1038 = lean_ctor_get(x_1022, 2);
x_1039 = lean_ctor_get(x_1022, 3);
x_1040 = lean_ctor_get(x_1022, 4);
x_1041 = lean_ctor_get(x_1022, 5);
x_1042 = lean_ctor_get(x_1022, 6);
x_1043 = lean_ctor_get(x_1022, 7);
x_1044 = lean_ctor_get(x_1022, 8);
x_1045 = lean_ctor_get(x_1022, 9);
x_1046 = lean_ctor_get(x_1022, 10);
x_1047 = lean_ctor_get(x_1022, 11);
lean_inc(x_1047);
lean_inc(x_1046);
lean_inc(x_1045);
lean_inc(x_1044);
lean_inc(x_1043);
lean_inc(x_1042);
lean_inc(x_1041);
lean_inc(x_1040);
lean_inc(x_1039);
lean_inc(x_1038);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_1022);
lean_inc(x_1019);
lean_inc(x_1008);
x_1048 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1037, x_1008, x_1019);
x_1049 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1049, 0, x_1036);
lean_ctor_set(x_1049, 1, x_1048);
lean_ctor_set(x_1049, 2, x_1038);
lean_ctor_set(x_1049, 3, x_1039);
lean_ctor_set(x_1049, 4, x_1040);
lean_ctor_set(x_1049, 5, x_1041);
lean_ctor_set(x_1049, 6, x_1042);
lean_ctor_set(x_1049, 7, x_1043);
lean_ctor_set(x_1049, 8, x_1044);
lean_ctor_set(x_1049, 9, x_1045);
lean_ctor_set(x_1049, 10, x_1046);
lean_ctor_set(x_1049, 11, x_1047);
x_1050 = lean_st_ref_set(x_3, x_1049, x_1023);
x_1051 = lean_ctor_get(x_1050, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_1050)) {
 lean_ctor_release(x_1050, 0);
 lean_ctor_release(x_1050, 1);
 x_1052 = x_1050;
} else {
 lean_dec_ref(x_1050);
 x_1052 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1053 = lean_alloc_ctor(11, 3, 8);
} else {
 x_1053 = x_1010;
}
lean_ctor_set(x_1053, 0, x_1006);
lean_ctor_set(x_1053, 1, x_1007);
lean_ctor_set(x_1053, 2, x_1008);
lean_ctor_set_uint64(x_1053, sizeof(void*)*3, x_1009);
x_1054 = lean_expr_update_proj(x_1053, x_1019);
if (lean_is_scalar(x_1052)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1052;
}
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1051);
return x_1055;
}
}
else
{
uint8_t x_1056; 
lean_dec(x_1010);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
x_1056 = !lean_is_exclusive(x_1018);
if (x_1056 == 0)
{
return x_1018;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1057 = lean_ctor_get(x_1018, 0);
x_1058 = lean_ctor_get(x_1018, 1);
lean_inc(x_1058);
lean_inc(x_1057);
lean_dec(x_1018);
x_1059 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1059, 0, x_1057);
lean_ctor_set(x_1059, 1, x_1058);
return x_1059;
}
}
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1060 = lean_ctor_get(x_1017, 0);
lean_inc(x_1060);
lean_dec(x_1017);
if (lean_is_scalar(x_1010)) {
 x_1061 = lean_alloc_ctor(11, 3, 8);
} else {
 x_1061 = x_1010;
}
lean_ctor_set(x_1061, 0, x_1006);
lean_ctor_set(x_1061, 1, x_1007);
lean_ctor_set(x_1061, 2, x_1008);
lean_ctor_set_uint64(x_1061, sizeof(void*)*3, x_1009);
x_1062 = lean_expr_update_proj(x_1061, x_1060);
lean_ctor_set(x_1012, 0, x_1062);
return x_1012;
}
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1063 = lean_ctor_get(x_1012, 0);
x_1064 = lean_ctor_get(x_1012, 1);
lean_inc(x_1064);
lean_inc(x_1063);
lean_dec(x_1012);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_1065, x_1008);
lean_dec(x_1065);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; 
lean_inc(x_1008);
x_1067 = l_Lean_Meta_Closure_collectExprAux(x_1008, x_2, x_3, x_4, x_5, x_6, x_7, x_1064);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1067, 1);
lean_inc(x_1069);
lean_dec(x_1067);
x_1070 = lean_st_ref_take(x_3, x_1069);
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
lean_dec(x_1070);
x_1073 = lean_ctor_get(x_1071, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1071, 1);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1071, 2);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1071, 3);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1071, 4);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1071, 5);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1071, 6);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1071, 7);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1071, 8);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1071, 9);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1071, 10);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1071, 11);
lean_inc(x_1084);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 lean_ctor_release(x_1071, 2);
 lean_ctor_release(x_1071, 3);
 lean_ctor_release(x_1071, 4);
 lean_ctor_release(x_1071, 5);
 lean_ctor_release(x_1071, 6);
 lean_ctor_release(x_1071, 7);
 lean_ctor_release(x_1071, 8);
 lean_ctor_release(x_1071, 9);
 lean_ctor_release(x_1071, 10);
 lean_ctor_release(x_1071, 11);
 x_1085 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1085 = lean_box(0);
}
lean_inc(x_1068);
lean_inc(x_1008);
x_1086 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_1074, x_1008, x_1068);
if (lean_is_scalar(x_1085)) {
 x_1087 = lean_alloc_ctor(0, 12, 0);
} else {
 x_1087 = x_1085;
}
lean_ctor_set(x_1087, 0, x_1073);
lean_ctor_set(x_1087, 1, x_1086);
lean_ctor_set(x_1087, 2, x_1075);
lean_ctor_set(x_1087, 3, x_1076);
lean_ctor_set(x_1087, 4, x_1077);
lean_ctor_set(x_1087, 5, x_1078);
lean_ctor_set(x_1087, 6, x_1079);
lean_ctor_set(x_1087, 7, x_1080);
lean_ctor_set(x_1087, 8, x_1081);
lean_ctor_set(x_1087, 9, x_1082);
lean_ctor_set(x_1087, 10, x_1083);
lean_ctor_set(x_1087, 11, x_1084);
x_1088 = lean_st_ref_set(x_3, x_1087, x_1072);
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1090 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1091 = lean_alloc_ctor(11, 3, 8);
} else {
 x_1091 = x_1010;
}
lean_ctor_set(x_1091, 0, x_1006);
lean_ctor_set(x_1091, 1, x_1007);
lean_ctor_set(x_1091, 2, x_1008);
lean_ctor_set_uint64(x_1091, sizeof(void*)*3, x_1009);
x_1092 = lean_expr_update_proj(x_1091, x_1068);
if (lean_is_scalar(x_1090)) {
 x_1093 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1093 = x_1090;
}
lean_ctor_set(x_1093, 0, x_1092);
lean_ctor_set(x_1093, 1, x_1089);
return x_1093;
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_1010);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
x_1094 = lean_ctor_get(x_1067, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1067, 1);
lean_inc(x_1095);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 lean_ctor_release(x_1067, 1);
 x_1096 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1096 = lean_box(0);
}
if (lean_is_scalar(x_1096)) {
 x_1097 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1097 = x_1096;
}
lean_ctor_set(x_1097, 0, x_1094);
lean_ctor_set(x_1097, 1, x_1095);
return x_1097;
}
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1098 = lean_ctor_get(x_1066, 0);
lean_inc(x_1098);
lean_dec(x_1066);
if (lean_is_scalar(x_1010)) {
 x_1099 = lean_alloc_ctor(11, 3, 8);
} else {
 x_1099 = x_1010;
}
lean_ctor_set(x_1099, 0, x_1006);
lean_ctor_set(x_1099, 1, x_1007);
lean_ctor_set(x_1099, 2, x_1008);
lean_ctor_set_uint64(x_1099, sizeof(void*)*3, x_1009);
x_1100 = lean_expr_update_proj(x_1099, x_1098);
x_1101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1101, 0, x_1100);
lean_ctor_set(x_1101, 1, x_1064);
return x_1101;
}
}
}
}
default: 
{
lean_object* x_1112; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1112, 0, x_1);
lean_ctor_set(x_1112, 1, x_8);
return x_1112;
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
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_93; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_93 = l_Lean_Expr_hasLevelParam(x_11);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Expr_hasFVar(x_11);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasMVar(x_11);
if (x_95 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_96; 
lean_free_object(x_9);
x_96 = lean_box(0);
x_13 = x_96;
goto block_92;
}
}
else
{
lean_object* x_97; 
lean_free_object(x_9);
x_97 = lean_box(0);
x_13 = x_97;
goto block_92;
}
}
else
{
lean_object* x_98; 
lean_free_object(x_9);
x_98 = lean_box(0);
x_13 = x_98;
goto block_92;
}
block_92:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_13);
x_14 = lean_st_ref_get(x_3, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_18, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_14);
lean_inc(x_11);
x_20 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_21);
x_28 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_27, x_11, x_21);
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_st_ref_set(x_3, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 2);
x_37 = lean_ctor_get(x_24, 3);
x_38 = lean_ctor_get(x_24, 4);
x_39 = lean_ctor_get(x_24, 5);
x_40 = lean_ctor_get(x_24, 6);
x_41 = lean_ctor_get(x_24, 7);
x_42 = lean_ctor_get(x_24, 8);
x_43 = lean_ctor_get(x_24, 9);
x_44 = lean_ctor_get(x_24, 10);
x_45 = lean_ctor_get(x_24, 11);
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
lean_inc(x_34);
lean_dec(x_24);
lean_inc(x_21);
x_46 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_35, x_11, x_21);
x_47 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_37);
lean_ctor_set(x_47, 4, x_38);
lean_ctor_set(x_47, 5, x_39);
lean_ctor_set(x_47, 6, x_40);
lean_ctor_set(x_47, 7, x_41);
lean_ctor_set(x_47, 8, x_42);
lean_ctor_set(x_47, 9, x_43);
lean_ctor_set(x_47, 10, x_44);
lean_ctor_set(x_47, 11, x_45);
x_48 = lean_st_ref_set(x_3, x_47, x_25);
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
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
x_52 = !lean_is_exclusive(x_20);
if (x_52 == 0)
{
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
lean_dec(x_19);
lean_ctor_set(x_14, 0, x_56);
return x_14;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_59, x_11);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_inc(x_11);
x_61 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_take(x_3, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 7);
lean_inc(x_74);
x_75 = lean_ctor_get(x_65, 8);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 9);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 10);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 11);
lean_inc(x_78);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 lean_ctor_release(x_65, 9);
 lean_ctor_release(x_65, 10);
 lean_ctor_release(x_65, 11);
 x_79 = x_65;
} else {
 lean_dec_ref(x_65);
 x_79 = lean_box(0);
}
lean_inc(x_62);
x_80 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_68, x_11, x_62);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 12, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_69);
lean_ctor_set(x_81, 3, x_70);
lean_ctor_set(x_81, 4, x_71);
lean_ctor_set(x_81, 5, x_72);
lean_ctor_set(x_81, 6, x_73);
lean_ctor_set(x_81, 7, x_74);
lean_ctor_set(x_81, 8, x_75);
lean_ctor_set(x_81, 9, x_76);
lean_ctor_set(x_81, 10, x_77);
lean_ctor_set(x_81, 11, x_78);
x_82 = lean_st_ref_set(x_3, x_81, x_66);
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
lean_ctor_set(x_85, 0, x_62);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_11);
x_86 = lean_ctor_get(x_61, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_88 = x_61;
} else {
 lean_dec_ref(x_61);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = lean_ctor_get(x_60, 0);
lean_inc(x_90);
lean_dec(x_60);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_58);
return x_91;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_140; 
x_99 = lean_ctor_get(x_9, 0);
x_100 = lean_ctor_get(x_9, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_9);
x_140 = l_Lean_Expr_hasLevelParam(x_99);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Expr_hasFVar(x_99);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_Expr_hasMVar(x_99);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_99);
lean_ctor_set(x_143, 1, x_100);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = lean_box(0);
x_101 = x_144;
goto block_139;
}
}
else
{
lean_object* x_145; 
x_145 = lean_box(0);
x_101 = x_145;
goto block_139;
}
}
else
{
lean_object* x_146; 
x_146 = lean_box(0);
x_101 = x_146;
goto block_139;
}
block_139:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_101);
x_102 = lean_st_ref_get(x_3, x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitExpr___spec__1(x_106, x_99);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_105);
lean_inc(x_99);
x_108 = l_Lean_Meta_Closure_collectExprAux(x_99, x_2, x_3, x_4, x_5, x_6, x_7, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_st_ref_take(x_3, x_110);
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
lean_inc(x_109);
x_127 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitExpr___spec__3(x_115, x_99, x_109);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 12, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_116);
lean_ctor_set(x_128, 3, x_117);
lean_ctor_set(x_128, 4, x_118);
lean_ctor_set(x_128, 5, x_119);
lean_ctor_set(x_128, 6, x_120);
lean_ctor_set(x_128, 7, x_121);
lean_ctor_set(x_128, 8, x_122);
lean_ctor_set(x_128, 9, x_123);
lean_ctor_set(x_128, 10, x_124);
lean_ctor_set(x_128, 11, x_125);
x_129 = lean_st_ref_set(x_3, x_128, x_113);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_109);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_99);
x_133 = lean_ctor_get(x_108, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_108, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_135 = x_108;
} else {
 lean_dec_ref(x_108);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_99);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_137 = lean_ctor_get(x_107, 0);
lean_inc(x_137);
lean_dec(x_107);
if (lean_is_scalar(x_105)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_105;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_104);
return x_138;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_147 = !lean_is_exclusive(x_9);
if (x_147 == 0)
{
return x_9;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_9, 0);
x_149 = lean_ctor_get(x_9, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_9);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
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
x_5 = l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1;
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
lean_object* l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_43 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg(x_4, x_5, x_6, x_36);
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
x_80 = l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_69, x_79);
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
x_98 = l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_69, x_97);
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
x_139 = l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_116, x_138);
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
x_156 = l_Lean_Meta_getZetaFVarIds___at_Lean_Meta_Closure_process___spec__1___rarg(x_4, x_5, x_6, x_36);
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
x_217 = l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2(x_19, x_175, x_193, x_216);
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
lean_object* l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___at_Lean_Meta_Closure_process___spec__2(x_1, x_2, x_3, x_4);
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
lean_object* l_Array_umapMAux___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Lean_LocalDecl_Lean_LocalContext___instance__1;
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
x_6 = l_Array_umapMAux___at_Lean_Meta_Closure_mkBinding___spec__1(x_5, x_4);
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
x_9 = l_Lean_LocalDecl_Lean_LocalContext___instance__1;
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
x_5 = l_Array_umapMAux___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_3);
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
x_9 = l_Lean_LocalDecl_Lean_LocalContext___instance__1;
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
x_5 = l_Array_umapMAux___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_3);
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
x_24 = l_Array_reverseAux___rarg(x_22, x_23);
x_25 = lean_ctor_get(x_19, 6);
lean_inc(x_25);
x_26 = l_Array_iterateMAux___at_Array_append___spec__1___rarg(x_25, x_25, x_23, x_24);
lean_dec(x_25);
x_27 = lean_ctor_get(x_19, 7);
lean_inc(x_27);
x_28 = l_Array_reverseAux___rarg(x_27, x_23);
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
x_36 = l_Array_reverseAux___rarg(x_35, x_23);
x_37 = lean_ctor_get(x_19, 9);
lean_inc(x_37);
lean_dec(x_19);
x_38 = l_Array_iterateMAux___at_Array_append___spec__1___rarg(x_37, x_37, x_23, x_36);
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
x_46 = l_Array_reverseAux___rarg(x_44, x_45);
x_47 = lean_ctor_get(x_40, 6);
lean_inc(x_47);
x_48 = l_Array_iterateMAux___at_Array_append___spec__1___rarg(x_47, x_47, x_45, x_46);
lean_dec(x_47);
x_49 = lean_ctor_get(x_40, 7);
lean_inc(x_49);
x_50 = l_Array_reverseAux___rarg(x_49, x_45);
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
x_58 = l_Array_reverseAux___rarg(x_57, x_45);
x_59 = lean_ctor_get(x_40, 9);
lean_inc(x_59);
lean_dec(x_40);
x_60 = l_Array_iterateMAux___at_Array_append___spec__1___rarg(x_59, x_59, x_45, x_58);
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
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(x_12, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(x_13, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 3);
x_10 = l_Array_toList___rarg(x_9);
x_11 = l_Lean_mkConst(x_2, x_10);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_12, x_12, x_13, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___at_Lean_ppGoal___spec__7___closed__4;
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
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint32_t x_25; uint32_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_20);
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_12, 2);
lean_inc(x_22);
lean_inc(x_22);
lean_inc(x_17);
x_23 = l_Lean_getMaxHeight(x_17, x_22);
x_24 = lean_unbox_uint32(x_23);
lean_dec(x_23);
x_25 = 1;
x_26 = x_24 + x_25;
x_27 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_27, 0, x_26);
lean_inc(x_20);
lean_inc(x_17);
x_28 = l_Lean_Environment_hasUnsafe(x_17, x_20);
x_29 = lean_st_ref_get(x_9, x_16);
if (x_28 == 0)
{
uint8_t x_82; 
lean_inc(x_22);
x_82 = l_Lean_Environment_hasUnsafe(x_17, x_22);
x_30 = x_82;
goto block_81;
}
else
{
uint8_t x_83; 
lean_dec(x_17);
x_83 = 1;
x_30 = x_83;
goto block_81;
}
block_81:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_52; lean_object* x_53; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_inc(x_22);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_70 = lean_ctor_get(x_29, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_29, 1);
lean_inc(x_73);
lean_dec(x_29);
x_74 = 0;
x_52 = x_74;
x_53 = x_73;
goto block_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_29, 1);
lean_inc(x_75);
lean_dec(x_29);
x_76 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_77 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__2(x_76, x_6, x_7, x_8, x_9, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_52 = x_80;
x_53 = x_79;
goto block_69;
}
block_51:
{
lean_object* x_34; 
lean_inc(x_8);
x_34 = l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(x_32, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
if (x_5 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___lambda__1(x_12, x_1, x_36, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
lean_inc(x_8);
x_39 = l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(x_32, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___lambda__1(x_12, x_1, x_40, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_40);
lean_dec(x_12);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_32);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
block_69:
{
if (x_52 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_33 = x_53;
goto block_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc(x_1);
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_1);
x_55 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_20);
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_22);
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_55);
x_66 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_67 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__1(x_66, x_65, x_6, x_7, x_8, x_9, x_53);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_33 = x_68;
goto block_51;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_11);
if (x_84 == 0)
{
return x_11;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_11, 0);
x_86 = lean_ctor_get(x_11, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_11);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
lean_object* l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_compileDecl___at___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_st_ref_get(x_10, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_12 = x_36;
x_13 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
lean_inc(x_6);
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__2(x_6, x_7, x_8, x_9, x_10, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_12 = x_41;
x_13 = x_40;
goto block_30;
}
block_30:
{
if (x_12 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_2);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_3);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_3);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
x_27 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__1(x_6, x_26, x_7, x_8, x_9, x_10, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_8 = lean_box(x_5);
x_9 = lean_box(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed), 11, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_8);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_7);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinition___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_mkAuxDefinition___rarg___lambda__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Meta_mkAuxDefinition___rarg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_st_ref_get(x_9, x_10);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_11 = x_36;
x_12 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_39 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__2(x_38, x_6, x_7, x_8, x_9, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
x_11 = x_42;
x_12 = x_41;
goto block_30;
}
block_30:
{
if (x_11 == 0)
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_1);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__1;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_3);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
x_26 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_517____closed__4;
x_27 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__1(x_26, x_25, x_6, x_7, x_8, x_9, x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Meta_Closure_0__Lean_Meta_mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_2, x_11, x_1, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
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
lean_object* l_Lean_Meta_mkAuxDefinitionFor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxDefinitionFor___rarg___lambda__1), 7, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
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
lean_object* l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_mkAuxDefinition___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
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
l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1___closed__1 = _init_l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1___closed__1);
l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1 = _init_l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1();
lean_mark_persistent(l_Lean_Meta_Closure_Lean_Meta_Closure___instance__1);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
