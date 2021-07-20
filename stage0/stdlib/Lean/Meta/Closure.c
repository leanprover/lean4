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
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__5;
lean_object* l_Lean_Meta_Closure_visitLevel_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__18;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__14;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__3;
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_Closure_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__1;
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__9;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__16;
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLocalDecls___default;
lean_object* l_Lean_Meta_Closure_visitExpr_match__1(lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__7;
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel_match__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
lean_object* l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4___boxed(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_auxRecExt;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__15;
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__1;
size_t l_UInt64_toUSize(uint64_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__2;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__8;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__4;
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__3;
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__6;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_levelParams___default___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_visitedLevel___default;
lean_object* l_Array_back___at_Lean_Meta_Closure_pickNextToProcess_x3f___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__1;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__17;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__8;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__5;
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4;
extern lean_object* l_Lean_instInhabitedExpr;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__11;
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
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__13;
lean_object* l_Lean_Meta_Closure_State_levelParams___default;
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__7;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__10;
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__1;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__3;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__9;
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_Closure_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_toProcess___default;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_visitedExpr___default;
static lean_object* l_Lean_Meta_Closure_State_visitedLevel___default___closed__1;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2;
lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevelAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__1;
lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__2(lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__3;
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__2(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__1;
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement;
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__19;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__6;
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__4;
lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__12;
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__5;
lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_collectExprAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_State_newLetDecls___default;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_Closure_process_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__4;
lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__10;
extern lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLevel;
lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__2;
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Meta_Closure_State_levelParams___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_levelParams___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
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
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLocalDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_newLetDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
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
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_exprFVarArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_toProcess___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
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
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_8);
lean_dec(x_8);
return x_9;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Level_hash(x_4);
x_8 = (size_t)x_7;
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Level_hash(x_13);
x_18 = (size_t)x_17;
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Level_hash(x_2);
x_9 = (size_t)x_8;
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = lean_nat_dec_le(x_14, x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(x_14, x_16);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_2, x_3, x_11);
x_20 = lean_array_uset(x_6, x_10, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Level_hash(x_2);
x_25 = (size_t)x_24;
x_26 = lean_usize_modn(x_25, x_23);
x_27 = lean_array_uget(x_22, x_26);
x_28 = l_Std_AssocList_contains___at_Lean_Meta_Closure_visitLevel___spec__4(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_27);
x_32 = lean_array_uset(x_22, x_26, x_31);
x_33 = lean_nat_dec_le(x_30, x_23);
lean_dec(x_23);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_HashMapImp_expand___at_Lean_Meta_Closure_visitLevel___spec__5(x_30, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Std_AssocList_replace___at_Lean_Meta_Closure_visitLevel___spec__8(x_2, x_3, x_27);
x_37 = lean_array_uset(x_22, x_26, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_98; 
x_98 = l_Lean_Level_hasMVar(x_2);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Level_hasParam(x_2);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_9);
return x_100;
}
else
{
lean_object* x_101; 
x_101 = lean_box(0);
x_10 = x_101;
goto block_97;
}
}
else
{
lean_object* x_102; 
x_102 = lean_box(0);
x_10 = x_102;
goto block_97;
}
block_97:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_17, x_2);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_20 = lean_apply_8(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_8, x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_21);
x_30 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_29, x_2, x_21);
lean_ctor_set(x_26, 0, x_30);
x_31 = lean_st_ref_set(x_4, x_26, x_27);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
x_38 = lean_ctor_get(x_26, 2);
x_39 = lean_ctor_get(x_26, 3);
x_40 = lean_ctor_get(x_26, 4);
x_41 = lean_ctor_get(x_26, 5);
x_42 = lean_ctor_get(x_26, 6);
x_43 = lean_ctor_get(x_26, 7);
x_44 = lean_ctor_get(x_26, 8);
x_45 = lean_ctor_get(x_26, 9);
x_46 = lean_ctor_get(x_26, 10);
x_47 = lean_ctor_get(x_26, 11);
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
lean_inc(x_36);
lean_dec(x_26);
lean_inc(x_21);
x_48 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_36, x_2, x_21);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_39);
lean_ctor_set(x_49, 4, x_40);
lean_ctor_set(x_49, 5, x_41);
lean_ctor_set(x_49, 6, x_42);
lean_ctor_set(x_49, 7, x_43);
lean_ctor_set(x_49, 8, x_44);
lean_ctor_set(x_49, 9, x_45);
lean_ctor_set(x_49, 10, x_46);
lean_ctor_set(x_49, 11, x_47);
x_50 = lean_st_ref_set(x_4, x_49, x_27);
lean_dec(x_4);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_20);
if (x_54 == 0)
{
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_58);
return x_13;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_61, x_2);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_64 = lean_apply_8(x_1, x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_8, x_66);
lean_dec(x_8);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_4, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_70, 7);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 9);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 10);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 11);
lean_inc(x_83);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 lean_ctor_release(x_70, 6);
 lean_ctor_release(x_70, 7);
 lean_ctor_release(x_70, 8);
 lean_ctor_release(x_70, 9);
 lean_ctor_release(x_70, 10);
 lean_ctor_release(x_70, 11);
 x_84 = x_70;
} else {
 lean_dec_ref(x_70);
 x_84 = lean_box(0);
}
lean_inc(x_65);
x_85 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_72, x_2, x_65);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 12, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_73);
lean_ctor_set(x_86, 2, x_74);
lean_ctor_set(x_86, 3, x_75);
lean_ctor_set(x_86, 4, x_76);
lean_ctor_set(x_86, 5, x_77);
lean_ctor_set(x_86, 6, x_78);
lean_ctor_set(x_86, 7, x_79);
lean_ctor_set(x_86, 8, x_80);
lean_ctor_set(x_86, 9, x_81);
lean_ctor_set(x_86, 10, x_82);
lean_ctor_set(x_86, 11, x_83);
x_87 = lean_st_ref_set(x_4, x_86, x_71);
lean_dec(x_4);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_65);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_91 = lean_ctor_get(x_64, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_93 = x_64;
} else {
 lean_dec_ref(x_64);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_62, 0);
lean_inc(x_95);
lean_dec(x_62);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_60);
return x_96;
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
lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_visitLevel(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_98; 
x_98 = l_Lean_Expr_hasLevelParam(x_2);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Expr_hasFVar(x_2);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Expr_hasMVar(x_2);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_9);
return x_101;
}
else
{
lean_object* x_102; 
x_102 = lean_box(0);
x_10 = x_102;
goto block_97;
}
}
else
{
lean_object* x_103; 
x_103 = lean_box(0);
x_10 = x_103;
goto block_97;
}
}
else
{
lean_object* x_104; 
x_104 = lean_box(0);
x_10 = x_104;
goto block_97;
}
block_97:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_17, x_2);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_20 = lean_apply_8(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_8, x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_21);
x_30 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_29, x_2, x_21);
lean_ctor_set(x_26, 1, x_30);
x_31 = lean_st_ref_set(x_4, x_26, x_27);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
x_38 = lean_ctor_get(x_26, 2);
x_39 = lean_ctor_get(x_26, 3);
x_40 = lean_ctor_get(x_26, 4);
x_41 = lean_ctor_get(x_26, 5);
x_42 = lean_ctor_get(x_26, 6);
x_43 = lean_ctor_get(x_26, 7);
x_44 = lean_ctor_get(x_26, 8);
x_45 = lean_ctor_get(x_26, 9);
x_46 = lean_ctor_get(x_26, 10);
x_47 = lean_ctor_get(x_26, 11);
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
lean_inc(x_36);
lean_dec(x_26);
lean_inc(x_21);
x_48 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_37, x_2, x_21);
x_49 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_39);
lean_ctor_set(x_49, 4, x_40);
lean_ctor_set(x_49, 5, x_41);
lean_ctor_set(x_49, 6, x_42);
lean_ctor_set(x_49, 7, x_43);
lean_ctor_set(x_49, 8, x_44);
lean_ctor_set(x_49, 9, x_45);
lean_ctor_set(x_49, 10, x_46);
lean_ctor_set(x_49, 11, x_47);
x_50 = lean_st_ref_set(x_4, x_49, x_27);
lean_dec(x_4);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_20);
if (x_54 == 0)
{
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_58);
return x_13;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_61, x_2);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_64 = lean_apply_8(x_1, x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_8, x_66);
lean_dec(x_8);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_4, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_70, 7);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 9);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 10);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 11);
lean_inc(x_83);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 lean_ctor_release(x_70, 6);
 lean_ctor_release(x_70, 7);
 lean_ctor_release(x_70, 8);
 lean_ctor_release(x_70, 9);
 lean_ctor_release(x_70, 10);
 lean_ctor_release(x_70, 11);
 x_84 = x_70;
} else {
 lean_dec_ref(x_70);
 x_84 = lean_box(0);
}
lean_inc(x_65);
x_85 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_73, x_2, x_65);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 12, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_72);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_74);
lean_ctor_set(x_86, 3, x_75);
lean_ctor_set(x_86, 4, x_76);
lean_ctor_set(x_86, 5, x_77);
lean_ctor_set(x_86, 6, x_78);
lean_ctor_set(x_86, 7, x_79);
lean_ctor_set(x_86, 8, x_80);
lean_ctor_set(x_86, 9, x_81);
lean_ctor_set(x_86, 10, x_82);
lean_ctor_set(x_86, 11, x_83);
x_87 = lean_st_ref_set(x_4, x_86, x_71);
lean_dec(x_4);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_65);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_91 = lean_ctor_get(x_64, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_93 = x_64;
} else {
 lean_dec_ref(x_64);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_62, 0);
lean_inc(x_95);
lean_dec(x_62);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_60);
return x_96;
}
}
}
}
}
lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_visitExpr(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_15 = l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
x_16 = lean_name_append_index_after(x_15, x_14);
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
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.updateSucc!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ level expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__2;
x_3 = lean_unsigned_to_nat(487u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_Closure_collectLevelAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.updateMax!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("max level expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__5;
x_3 = lean_unsigned_to_nat(496u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Meta_Closure_collectLevelAux___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.updateIMax!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("imax level expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectLevelAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectLevelAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectLevelAux___closed__8;
x_3 = lean_unsigned_to_nat(505u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Meta_Closure_collectLevelAux___closed__9;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
case 1:
{
lean_object* x_25; lean_object* x_26; uint8_t x_65; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_65 = l_Lean_Level_hasMVar(x_25);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Level_hasParam(x_25);
if (x_66 == 0)
{
x_9 = x_25;
x_10 = x_8;
goto block_23;
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
x_26 = x_67;
goto block_64;
}
}
else
{
lean_object* x_68; 
x_68 = lean_box(0);
x_26 = x_68;
goto block_64;
}
block_64:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_27 = lean_st_ref_get(x_7, x_8);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_3, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_32, x_25);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_inc(x_25);
x_34 = l_Lean_Meta_Closure_collectLevelAux(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_7, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_3, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_35);
x_44 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_43, x_25, x_35);
lean_ctor_set(x_40, 0, x_44);
x_45 = lean_st_ref_set(x_3, x_40, x_41);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_9 = x_35;
x_10 = x_46;
goto block_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
x_49 = lean_ctor_get(x_40, 2);
x_50 = lean_ctor_get(x_40, 3);
x_51 = lean_ctor_get(x_40, 4);
x_52 = lean_ctor_get(x_40, 5);
x_53 = lean_ctor_get(x_40, 6);
x_54 = lean_ctor_get(x_40, 7);
x_55 = lean_ctor_get(x_40, 8);
x_56 = lean_ctor_get(x_40, 9);
x_57 = lean_ctor_get(x_40, 10);
x_58 = lean_ctor_get(x_40, 11);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
lean_inc(x_35);
x_59 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_47, x_25, x_35);
x_60 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
lean_ctor_set(x_60, 2, x_49);
lean_ctor_set(x_60, 3, x_50);
lean_ctor_set(x_60, 4, x_51);
lean_ctor_set(x_60, 5, x_52);
lean_ctor_set(x_60, 6, x_53);
lean_ctor_set(x_60, 7, x_54);
lean_ctor_set(x_60, 8, x_55);
lean_ctor_set(x_60, 9, x_56);
lean_ctor_set(x_60, 10, x_57);
lean_ctor_set(x_60, 11, x_58);
x_61 = lean_st_ref_set(x_3, x_60, x_41);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_9 = x_35;
x_10 = x_62;
goto block_23;
}
}
else
{
lean_object* x_63; 
lean_dec(x_25);
x_63 = lean_ctor_get(x_33, 0);
lean_inc(x_63);
lean_dec(x_33);
x_9 = x_63;
x_10 = x_31;
goto block_23;
}
}
}
case 2:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_133; uint8_t x_172; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_172 = l_Lean_Level_hasMVar(x_69);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Level_hasParam(x_69);
if (x_173 == 0)
{
x_71 = x_69;
x_72 = x_8;
goto block_132;
}
else
{
lean_object* x_174; 
x_174 = lean_box(0);
x_133 = x_174;
goto block_171;
}
}
else
{
lean_object* x_175; 
x_175 = lean_box(0);
x_133 = x_175;
goto block_171;
}
block_132:
{
lean_object* x_73; lean_object* x_74; lean_object* x_89; uint8_t x_128; 
x_128 = l_Lean_Level_hasMVar(x_70);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = l_Lean_Level_hasParam(x_70);
if (x_129 == 0)
{
x_73 = x_70;
x_74 = x_72;
goto block_88;
}
else
{
lean_object* x_130; 
x_130 = lean_box(0);
x_89 = x_130;
goto block_127;
}
}
else
{
lean_object* x_131; 
x_131 = lean_box(0);
x_89 = x_131;
goto block_127;
}
block_88:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_1);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_level_update_max(x_1, x_71, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
x_80 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_1);
x_81 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set_uint64(x_81, sizeof(void*)*2, x_80);
x_82 = lean_level_update_max(x_81, x_71, x_73);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_1);
x_84 = l_Lean_instInhabitedLevel;
x_85 = l_Lean_Meta_Closure_collectLevelAux___closed__7;
x_86 = lean_panic_fn(x_84, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_74);
return x_87;
}
}
block_127:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_89);
x_90 = lean_st_ref_get(x_7, x_72);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_get(x_3, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_95, x_70);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_inc(x_70);
x_97 = l_Lean_Meta_Closure_collectLevelAux(x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_st_ref_get(x_7, x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_st_ref_take(x_3, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = !lean_is_exclusive(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_98);
x_107 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_106, x_70, x_98);
lean_ctor_set(x_103, 0, x_107);
x_108 = lean_st_ref_set(x_3, x_103, x_104);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_73 = x_98;
x_74 = x_109;
goto block_88;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_110 = lean_ctor_get(x_103, 0);
x_111 = lean_ctor_get(x_103, 1);
x_112 = lean_ctor_get(x_103, 2);
x_113 = lean_ctor_get(x_103, 3);
x_114 = lean_ctor_get(x_103, 4);
x_115 = lean_ctor_get(x_103, 5);
x_116 = lean_ctor_get(x_103, 6);
x_117 = lean_ctor_get(x_103, 7);
x_118 = lean_ctor_get(x_103, 8);
x_119 = lean_ctor_get(x_103, 9);
x_120 = lean_ctor_get(x_103, 10);
x_121 = lean_ctor_get(x_103, 11);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_103);
lean_inc(x_98);
x_122 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_110, x_70, x_98);
x_123 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_123, 2, x_112);
lean_ctor_set(x_123, 3, x_113);
lean_ctor_set(x_123, 4, x_114);
lean_ctor_set(x_123, 5, x_115);
lean_ctor_set(x_123, 6, x_116);
lean_ctor_set(x_123, 7, x_117);
lean_ctor_set(x_123, 8, x_118);
lean_ctor_set(x_123, 9, x_119);
lean_ctor_set(x_123, 10, x_120);
lean_ctor_set(x_123, 11, x_121);
x_124 = lean_st_ref_set(x_3, x_123, x_104);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_73 = x_98;
x_74 = x_125;
goto block_88;
}
}
else
{
lean_object* x_126; 
lean_dec(x_70);
x_126 = lean_ctor_get(x_96, 0);
lean_inc(x_126);
lean_dec(x_96);
x_73 = x_126;
x_74 = x_94;
goto block_88;
}
}
}
block_171:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_133);
x_134 = lean_st_ref_get(x_7, x_8);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_st_ref_get(x_3, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_139, x_69);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_inc(x_69);
x_141 = l_Lean_Meta_Closure_collectLevelAux(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_138);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_st_ref_get(x_7, x_143);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_take(x_3, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_142);
x_151 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_150, x_69, x_142);
lean_ctor_set(x_147, 0, x_151);
x_152 = lean_st_ref_set(x_3, x_147, x_148);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_71 = x_142;
x_72 = x_153;
goto block_132;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_154 = lean_ctor_get(x_147, 0);
x_155 = lean_ctor_get(x_147, 1);
x_156 = lean_ctor_get(x_147, 2);
x_157 = lean_ctor_get(x_147, 3);
x_158 = lean_ctor_get(x_147, 4);
x_159 = lean_ctor_get(x_147, 5);
x_160 = lean_ctor_get(x_147, 6);
x_161 = lean_ctor_get(x_147, 7);
x_162 = lean_ctor_get(x_147, 8);
x_163 = lean_ctor_get(x_147, 9);
x_164 = lean_ctor_get(x_147, 10);
x_165 = lean_ctor_get(x_147, 11);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_147);
lean_inc(x_142);
x_166 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_154, x_69, x_142);
x_167 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_155);
lean_ctor_set(x_167, 2, x_156);
lean_ctor_set(x_167, 3, x_157);
lean_ctor_set(x_167, 4, x_158);
lean_ctor_set(x_167, 5, x_159);
lean_ctor_set(x_167, 6, x_160);
lean_ctor_set(x_167, 7, x_161);
lean_ctor_set(x_167, 8, x_162);
lean_ctor_set(x_167, 9, x_163);
lean_ctor_set(x_167, 10, x_164);
lean_ctor_set(x_167, 11, x_165);
x_168 = lean_st_ref_set(x_3, x_167, x_148);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_71 = x_142;
x_72 = x_169;
goto block_132;
}
}
else
{
lean_object* x_170; 
lean_dec(x_69);
x_170 = lean_ctor_get(x_140, 0);
lean_inc(x_170);
lean_dec(x_140);
x_71 = x_170;
x_72 = x_138;
goto block_132;
}
}
}
case 3:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_240; uint8_t x_279; 
x_176 = lean_ctor_get(x_1, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_1, 1);
lean_inc(x_177);
x_279 = l_Lean_Level_hasMVar(x_176);
if (x_279 == 0)
{
uint8_t x_280; 
x_280 = l_Lean_Level_hasParam(x_176);
if (x_280 == 0)
{
x_178 = x_176;
x_179 = x_8;
goto block_239;
}
else
{
lean_object* x_281; 
x_281 = lean_box(0);
x_240 = x_281;
goto block_278;
}
}
else
{
lean_object* x_282; 
x_282 = lean_box(0);
x_240 = x_282;
goto block_278;
}
block_239:
{
lean_object* x_180; lean_object* x_181; lean_object* x_196; uint8_t x_235; 
x_235 = l_Lean_Level_hasMVar(x_177);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = l_Lean_Level_hasParam(x_177);
if (x_236 == 0)
{
x_180 = x_177;
x_181 = x_179;
goto block_195;
}
else
{
lean_object* x_237; 
x_237 = lean_box(0);
x_196 = x_237;
goto block_234;
}
}
else
{
lean_object* x_238; 
x_238 = lean_box(0);
x_196 = x_238;
goto block_234;
}
block_195:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_1);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_level_update_imax(x_1, x_178, x_180);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; uint64_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_1, 0);
x_186 = lean_ctor_get(x_1, 1);
x_187 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_1);
x_188 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
lean_ctor_set_uint64(x_188, sizeof(void*)*2, x_187);
x_189 = lean_level_update_imax(x_188, x_178, x_180);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_181);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_1);
x_191 = l_Lean_instInhabitedLevel;
x_192 = l_Lean_Meta_Closure_collectLevelAux___closed__10;
x_193 = lean_panic_fn(x_191, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_181);
return x_194;
}
}
block_234:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_196);
x_197 = lean_st_ref_get(x_7, x_179);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_st_ref_get(x_3, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_202, x_177);
lean_dec(x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_inc(x_177);
x_204 = l_Lean_Meta_Closure_collectLevelAux(x_177, x_2, x_3, x_4, x_5, x_6, x_7, x_201);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_st_ref_get(x_7, x_206);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_st_ref_take(x_3, x_208);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = !lean_is_exclusive(x_210);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_205);
x_214 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_213, x_177, x_205);
lean_ctor_set(x_210, 0, x_214);
x_215 = lean_st_ref_set(x_3, x_210, x_211);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_180 = x_205;
x_181 = x_216;
goto block_195;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_217 = lean_ctor_get(x_210, 0);
x_218 = lean_ctor_get(x_210, 1);
x_219 = lean_ctor_get(x_210, 2);
x_220 = lean_ctor_get(x_210, 3);
x_221 = lean_ctor_get(x_210, 4);
x_222 = lean_ctor_get(x_210, 5);
x_223 = lean_ctor_get(x_210, 6);
x_224 = lean_ctor_get(x_210, 7);
x_225 = lean_ctor_get(x_210, 8);
x_226 = lean_ctor_get(x_210, 9);
x_227 = lean_ctor_get(x_210, 10);
x_228 = lean_ctor_get(x_210, 11);
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
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_210);
lean_inc(x_205);
x_229 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_217, x_177, x_205);
x_230 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_218);
lean_ctor_set(x_230, 2, x_219);
lean_ctor_set(x_230, 3, x_220);
lean_ctor_set(x_230, 4, x_221);
lean_ctor_set(x_230, 5, x_222);
lean_ctor_set(x_230, 6, x_223);
lean_ctor_set(x_230, 7, x_224);
lean_ctor_set(x_230, 8, x_225);
lean_ctor_set(x_230, 9, x_226);
lean_ctor_set(x_230, 10, x_227);
lean_ctor_set(x_230, 11, x_228);
x_231 = lean_st_ref_set(x_3, x_230, x_211);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_180 = x_205;
x_181 = x_232;
goto block_195;
}
}
else
{
lean_object* x_233; 
lean_dec(x_177);
x_233 = lean_ctor_get(x_203, 0);
lean_inc(x_233);
lean_dec(x_203);
x_180 = x_233;
x_181 = x_201;
goto block_195;
}
}
}
block_278:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_240);
x_241 = lean_st_ref_get(x_7, x_8);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_st_ref_get(x_3, x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_246, x_176);
lean_dec(x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_inc(x_176);
x_248 = l_Lean_Meta_Closure_collectLevelAux(x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_245);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_st_ref_get(x_7, x_250);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_253 = lean_st_ref_take(x_3, x_252);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = !lean_is_exclusive(x_254);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_249);
x_258 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_257, x_176, x_249);
lean_ctor_set(x_254, 0, x_258);
x_259 = lean_st_ref_set(x_3, x_254, x_255);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_178 = x_249;
x_179 = x_260;
goto block_239;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_261 = lean_ctor_get(x_254, 0);
x_262 = lean_ctor_get(x_254, 1);
x_263 = lean_ctor_get(x_254, 2);
x_264 = lean_ctor_get(x_254, 3);
x_265 = lean_ctor_get(x_254, 4);
x_266 = lean_ctor_get(x_254, 5);
x_267 = lean_ctor_get(x_254, 6);
x_268 = lean_ctor_get(x_254, 7);
x_269 = lean_ctor_get(x_254, 8);
x_270 = lean_ctor_get(x_254, 9);
x_271 = lean_ctor_get(x_254, 10);
x_272 = lean_ctor_get(x_254, 11);
lean_inc(x_272);
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
lean_dec(x_254);
lean_inc(x_249);
x_273 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_261, x_176, x_249);
x_274 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_262);
lean_ctor_set(x_274, 2, x_263);
lean_ctor_set(x_274, 3, x_264);
lean_ctor_set(x_274, 4, x_265);
lean_ctor_set(x_274, 5, x_266);
lean_ctor_set(x_274, 6, x_267);
lean_ctor_set(x_274, 7, x_268);
lean_ctor_set(x_274, 8, x_269);
lean_ctor_set(x_274, 9, x_270);
lean_ctor_set(x_274, 10, x_271);
lean_ctor_set(x_274, 11, x_272);
x_275 = lean_st_ref_set(x_3, x_274, x_255);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_178 = x_249;
x_179 = x_276;
goto block_239;
}
}
else
{
lean_object* x_277; 
lean_dec(x_176);
x_277 = lean_ctor_get(x_247, 0);
lean_inc(x_277);
lean_dec(x_247);
x_178 = x_277;
x_179 = x_245;
goto block_239;
}
}
}
default: 
{
lean_object* x_283; 
x_283 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_283;
}
}
block_23:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_level_update_succ(x_1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_15);
x_17 = lean_level_update_succ(x_16, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_1);
x_19 = l_Lean_instInhabitedLevel;
x_20 = l_Lean_Meta_Closure_collectLevelAux___closed__4;
x_21 = lean_panic_fn(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_87; 
x_87 = l_Lean_Level_hasMVar(x_1);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Level_hasParam(x_1);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_8);
return x_89;
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_9 = x_90;
goto block_86;
}
}
else
{
lean_object* x_91; 
x_91 = lean_box(0);
x_9 = x_91;
goto block_86;
}
block_86:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_9);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_16, x_1);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_12);
lean_inc(x_1);
x_18 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_7, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
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
lean_inc(x_19);
x_28 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_27, x_1, x_19);
lean_ctor_set(x_24, 0, x_28);
x_29 = lean_st_ref_set(x_3, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_19);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
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
lean_inc(x_19);
x_46 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_34, x_1, x_19);
x_47 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
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
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_17, 0);
lean_inc(x_52);
lean_dec(x_17);
lean_ctor_set(x_12, 0, x_52);
return x_12;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_55, x_1);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_1);
x_57 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_7, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_st_ref_take(x_3, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 7);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 8);
lean_inc(x_73);
x_74 = lean_ctor_get(x_63, 9);
lean_inc(x_74);
x_75 = lean_ctor_get(x_63, 10);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 11);
lean_inc(x_76);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 lean_ctor_release(x_63, 7);
 lean_ctor_release(x_63, 8);
 lean_ctor_release(x_63, 9);
 lean_ctor_release(x_63, 10);
 lean_ctor_release(x_63, 11);
 x_77 = x_63;
} else {
 lean_dec_ref(x_63);
 x_77 = lean_box(0);
}
lean_inc(x_58);
x_78 = l_Std_HashMapImp_insert___at_Lean_Meta_Closure_visitLevel___spec__3(x_65, x_1, x_58);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 12, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_66);
lean_ctor_set(x_79, 2, x_67);
lean_ctor_set(x_79, 3, x_68);
lean_ctor_set(x_79, 4, x_69);
lean_ctor_set(x_79, 5, x_70);
lean_ctor_set(x_79, 6, x_71);
lean_ctor_set(x_79, 7, x_72);
lean_ctor_set(x_79, 8, x_73);
lean_ctor_set(x_79, 9, x_74);
lean_ctor_set(x_79, 10, x_75);
lean_ctor_set(x_79, 11, x_76);
x_80 = lean_st_ref_set(x_3, x_79, x_64);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_58);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_84 = lean_ctor_get(x_56, 0);
lean_inc(x_84);
lean_dec(x_56);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_54);
return x_85;
}
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectLevel(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_Closure_preprocess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_check(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_preprocess___lambda__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_preprocess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
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
x_14 = lean_name_append_index_after(x_13, x_12);
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
lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t x_1) {
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
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Closure_mkNextUserName(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_pushToProcess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg___boxed), 2, 0);
return x_6;
}
}
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateMData!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__2;
x_3 = lean_unsigned_to_nat(890u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateProj!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__5;
x_3 = lean_unsigned_to_nat(895u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateApp!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("application expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__8;
x_3 = lean_unsigned_to_nat(855u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__9;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateLambdaE!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lambda expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__11;
x_3 = lean_unsigned_to_nat(923u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__12;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateForallE!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forall expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__14;
x_3 = lean_unsigned_to_nat(909u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__15;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateLet!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let expression expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Closure_collectExprAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Closure_collectExprAux___closed__1;
x_2 = l_Lean_Meta_Closure_collectExprAux___closed__17;
x_3 = lean_unsigned_to_nat(932u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__18;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_25; lean_object* x_26; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_42);
x_43 = l_Lean_Meta_getLocalDecl(x_42, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
if (x_2 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_Closure_pushToProcess(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = l_Lean_mkFVar(x_46);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = l_Lean_mkFVar(x_46);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
lean_dec(x_43);
x_58 = l_Lean_LocalDecl_value_x3f(x_56);
lean_dec(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_59 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Meta_Closure_pushToProcess(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = l_Lean_mkFVar(x_60);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = l_Lean_mkFVar(x_60);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_42);
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
lean_dec(x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_71 = l_Lean_Meta_Closure_preprocess(x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_57);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_161; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_161 = l_Lean_Expr_hasLevelParam(x_73);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Expr_hasFVar(x_73);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = l_Lean_Expr_hasMVar(x_73);
if (x_163 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_71;
}
else
{
lean_object* x_164; 
lean_free_object(x_71);
x_164 = lean_box(0);
x_75 = x_164;
goto block_160;
}
}
else
{
lean_object* x_165; 
lean_free_object(x_71);
x_165 = lean_box(0);
x_75 = x_165;
goto block_160;
}
}
else
{
lean_object* x_166; 
lean_free_object(x_71);
x_166 = lean_box(0);
x_75 = x_166;
goto block_160;
}
block_160:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_75);
x_76 = lean_st_ref_get(x_7, x_74);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_3, x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_82, x_73);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
lean_free_object(x_78);
lean_inc(x_7);
lean_inc(x_73);
x_84 = l_Lean_Meta_Closure_collectExprAux(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_st_ref_get(x_7, x_86);
lean_dec(x_7);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_st_ref_take(x_3, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_85);
x_94 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_93, x_73, x_85);
lean_ctor_set(x_90, 1, x_94);
x_95 = lean_st_ref_set(x_3, x_90, x_91);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_85);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_85);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_100 = lean_ctor_get(x_90, 0);
x_101 = lean_ctor_get(x_90, 1);
x_102 = lean_ctor_get(x_90, 2);
x_103 = lean_ctor_get(x_90, 3);
x_104 = lean_ctor_get(x_90, 4);
x_105 = lean_ctor_get(x_90, 5);
x_106 = lean_ctor_get(x_90, 6);
x_107 = lean_ctor_get(x_90, 7);
x_108 = lean_ctor_get(x_90, 8);
x_109 = lean_ctor_get(x_90, 9);
x_110 = lean_ctor_get(x_90, 10);
x_111 = lean_ctor_get(x_90, 11);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_90);
lean_inc(x_85);
x_112 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_101, x_73, x_85);
x_113 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_113, 0, x_100);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_102);
lean_ctor_set(x_113, 3, x_103);
lean_ctor_set(x_113, 4, x_104);
lean_ctor_set(x_113, 5, x_105);
lean_ctor_set(x_113, 6, x_106);
lean_ctor_set(x_113, 7, x_107);
lean_ctor_set(x_113, 8, x_108);
lean_ctor_set(x_113, 9, x_109);
lean_ctor_set(x_113, 10, x_110);
lean_ctor_set(x_113, 11, x_111);
x_114 = lean_st_ref_set(x_3, x_113, x_91);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_85);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec(x_73);
lean_dec(x_7);
x_118 = !lean_is_exclusive(x_84);
if (x_118 == 0)
{
return x_84;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_84, 0);
x_120 = lean_ctor_get(x_84, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_84);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_122 = lean_ctor_get(x_83, 0);
lean_inc(x_122);
lean_dec(x_83);
lean_ctor_set(x_78, 0, x_122);
return x_78;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_78, 0);
x_124 = lean_ctor_get(x_78, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_78);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_125, x_73);
lean_dec(x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
lean_inc(x_7);
lean_inc(x_73);
x_127 = l_Lean_Meta_Closure_collectExprAux(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_get(x_7, x_129);
lean_dec(x_7);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_take(x_3, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 5);
lean_inc(x_140);
x_141 = lean_ctor_get(x_133, 6);
lean_inc(x_141);
x_142 = lean_ctor_get(x_133, 7);
lean_inc(x_142);
x_143 = lean_ctor_get(x_133, 8);
lean_inc(x_143);
x_144 = lean_ctor_get(x_133, 9);
lean_inc(x_144);
x_145 = lean_ctor_get(x_133, 10);
lean_inc(x_145);
x_146 = lean_ctor_get(x_133, 11);
lean_inc(x_146);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 lean_ctor_release(x_133, 5);
 lean_ctor_release(x_133, 6);
 lean_ctor_release(x_133, 7);
 lean_ctor_release(x_133, 8);
 lean_ctor_release(x_133, 9);
 lean_ctor_release(x_133, 10);
 lean_ctor_release(x_133, 11);
 x_147 = x_133;
} else {
 lean_dec_ref(x_133);
 x_147 = lean_box(0);
}
lean_inc(x_128);
x_148 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_136, x_73, x_128);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 12, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_137);
lean_ctor_set(x_149, 3, x_138);
lean_ctor_set(x_149, 4, x_139);
lean_ctor_set(x_149, 5, x_140);
lean_ctor_set(x_149, 6, x_141);
lean_ctor_set(x_149, 7, x_142);
lean_ctor_set(x_149, 8, x_143);
lean_ctor_set(x_149, 9, x_144);
lean_ctor_set(x_149, 10, x_145);
lean_ctor_set(x_149, 11, x_146);
x_150 = lean_st_ref_set(x_3, x_149, x_134);
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
lean_ctor_set(x_153, 0, x_128);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_73);
lean_dec(x_7);
x_154 = lean_ctor_get(x_127, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_127, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_156 = x_127;
} else {
 lean_dec_ref(x_127);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_158 = lean_ctor_get(x_126, 0);
lean_inc(x_158);
lean_dec(x_126);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_124);
return x_159;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_212; 
x_167 = lean_ctor_get(x_71, 0);
x_168 = lean_ctor_get(x_71, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_71);
x_212 = l_Lean_Expr_hasLevelParam(x_167);
if (x_212 == 0)
{
uint8_t x_213; 
x_213 = l_Lean_Expr_hasFVar(x_167);
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = l_Lean_Expr_hasMVar(x_167);
if (x_214 == 0)
{
lean_object* x_215; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_167);
lean_ctor_set(x_215, 1, x_168);
return x_215;
}
else
{
lean_object* x_216; 
x_216 = lean_box(0);
x_169 = x_216;
goto block_211;
}
}
else
{
lean_object* x_217; 
x_217 = lean_box(0);
x_169 = x_217;
goto block_211;
}
}
else
{
lean_object* x_218; 
x_218 = lean_box(0);
x_169 = x_218;
goto block_211;
}
block_211:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_169);
x_170 = lean_st_ref_get(x_7, x_168);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = lean_st_ref_get(x_3, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_176, x_167);
lean_dec(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
lean_dec(x_175);
lean_inc(x_7);
lean_inc(x_167);
x_178 = l_Lean_Meta_Closure_collectExprAux(x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_174);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_st_ref_get(x_7, x_180);
lean_dec(x_7);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_take(x_3, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 5);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 6);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 7);
lean_inc(x_193);
x_194 = lean_ctor_get(x_184, 8);
lean_inc(x_194);
x_195 = lean_ctor_get(x_184, 9);
lean_inc(x_195);
x_196 = lean_ctor_get(x_184, 10);
lean_inc(x_196);
x_197 = lean_ctor_get(x_184, 11);
lean_inc(x_197);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 lean_ctor_release(x_184, 6);
 lean_ctor_release(x_184, 7);
 lean_ctor_release(x_184, 8);
 lean_ctor_release(x_184, 9);
 lean_ctor_release(x_184, 10);
 lean_ctor_release(x_184, 11);
 x_198 = x_184;
} else {
 lean_dec_ref(x_184);
 x_198 = lean_box(0);
}
lean_inc(x_179);
x_199 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_187, x_167, x_179);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 12, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_186);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_188);
lean_ctor_set(x_200, 3, x_189);
lean_ctor_set(x_200, 4, x_190);
lean_ctor_set(x_200, 5, x_191);
lean_ctor_set(x_200, 6, x_192);
lean_ctor_set(x_200, 7, x_193);
lean_ctor_set(x_200, 8, x_194);
lean_ctor_set(x_200, 9, x_195);
lean_ctor_set(x_200, 10, x_196);
lean_ctor_set(x_200, 11, x_197);
x_201 = lean_st_ref_set(x_3, x_200, x_185);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_179);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_167);
lean_dec(x_7);
x_205 = lean_ctor_get(x_178, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_178, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_207 = x_178;
} else {
 lean_dec_ref(x_178);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_167);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_209 = lean_ctor_get(x_177, 0);
lean_inc(x_209);
lean_dec(x_177);
if (lean_is_scalar(x_175)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_175;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_174);
return x_210;
}
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_219 = !lean_is_exclusive(x_71);
if (x_219 == 0)
{
return x_71;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_71, 0);
x_221 = lean_ctor_get(x_71, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_71);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_223 = !lean_is_exclusive(x_43);
if (x_223 == 0)
{
return x_43;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_43, 0);
x_225 = lean_ctor_get(x_43, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_43);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
case 2:
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_1, 0);
lean_inc(x_227);
x_228 = l_Lean_Meta_getMVarDecl(x_227, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_ctor_get(x_229, 2);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_232 = l_Lean_Meta_Closure_preprocess(x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_287; uint8_t x_330; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_330 = l_Lean_Expr_hasLevelParam(x_233);
if (x_330 == 0)
{
uint8_t x_331; 
x_331 = l_Lean_Expr_hasFVar(x_233);
if (x_331 == 0)
{
uint8_t x_332; 
x_332 = l_Lean_Expr_hasMVar(x_233);
if (x_332 == 0)
{
x_235 = x_233;
x_236 = x_234;
goto block_286;
}
else
{
lean_object* x_333; 
x_333 = lean_box(0);
x_287 = x_333;
goto block_329;
}
}
else
{
lean_object* x_334; 
x_334 = lean_box(0);
x_287 = x_334;
goto block_329;
}
}
else
{
lean_object* x_335; 
x_335 = lean_box(0);
x_287 = x_335;
goto block_329;
}
block_286:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_237 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1___rarg(x_7, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_239);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_st_ref_get(x_7, x_242);
lean_dec(x_7);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_st_ref_take(x_3, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = !lean_is_exclusive(x_246);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_249 = lean_ctor_get(x_246, 6);
x_250 = lean_ctor_get(x_246, 9);
x_251 = lean_unsigned_to_nat(0u);
x_252 = 0;
lean_inc(x_238);
x_253 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_238);
lean_ctor_set(x_253, 2, x_241);
lean_ctor_set(x_253, 3, x_235);
lean_ctor_set_uint8(x_253, sizeof(void*)*4, x_252);
x_254 = lean_array_push(x_249, x_253);
x_255 = lean_array_push(x_250, x_1);
lean_ctor_set(x_246, 9, x_255);
lean_ctor_set(x_246, 6, x_254);
x_256 = lean_st_ref_set(x_3, x_246, x_247);
x_257 = !lean_is_exclusive(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_256, 0);
lean_dec(x_258);
x_259 = l_Lean_mkFVar(x_238);
lean_ctor_set(x_256, 0, x_259);
return x_256;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_256, 1);
lean_inc(x_260);
lean_dec(x_256);
x_261 = l_Lean_mkFVar(x_238);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_263 = lean_ctor_get(x_246, 0);
x_264 = lean_ctor_get(x_246, 1);
x_265 = lean_ctor_get(x_246, 2);
x_266 = lean_ctor_get(x_246, 3);
x_267 = lean_ctor_get(x_246, 4);
x_268 = lean_ctor_get(x_246, 5);
x_269 = lean_ctor_get(x_246, 6);
x_270 = lean_ctor_get(x_246, 7);
x_271 = lean_ctor_get(x_246, 8);
x_272 = lean_ctor_get(x_246, 9);
x_273 = lean_ctor_get(x_246, 10);
x_274 = lean_ctor_get(x_246, 11);
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
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_246);
x_275 = lean_unsigned_to_nat(0u);
x_276 = 0;
lean_inc(x_238);
x_277 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_238);
lean_ctor_set(x_277, 2, x_241);
lean_ctor_set(x_277, 3, x_235);
lean_ctor_set_uint8(x_277, sizeof(void*)*4, x_276);
x_278 = lean_array_push(x_269, x_277);
x_279 = lean_array_push(x_272, x_1);
x_280 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_280, 0, x_263);
lean_ctor_set(x_280, 1, x_264);
lean_ctor_set(x_280, 2, x_265);
lean_ctor_set(x_280, 3, x_266);
lean_ctor_set(x_280, 4, x_267);
lean_ctor_set(x_280, 5, x_268);
lean_ctor_set(x_280, 6, x_278);
lean_ctor_set(x_280, 7, x_270);
lean_ctor_set(x_280, 8, x_271);
lean_ctor_set(x_280, 9, x_279);
lean_ctor_set(x_280, 10, x_273);
lean_ctor_set(x_280, 11, x_274);
x_281 = lean_st_ref_set(x_3, x_280, x_247);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
x_284 = l_Lean_mkFVar(x_238);
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_282);
return x_285;
}
}
block_329:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_287);
x_288 = lean_st_ref_get(x_7, x_234);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
x_290 = lean_st_ref_get(x_3, x_289);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_293, x_233);
lean_dec(x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_233);
x_295 = l_Lean_Meta_Closure_collectExprAux(x_233, x_2, x_3, x_4, x_5, x_6, x_7, x_292);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_st_ref_get(x_7, x_297);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_300 = lean_st_ref_take(x_3, x_299);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = !lean_is_exclusive(x_301);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_296);
x_305 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_304, x_233, x_296);
lean_ctor_set(x_301, 1, x_305);
x_306 = lean_st_ref_set(x_3, x_301, x_302);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_235 = x_296;
x_236 = x_307;
goto block_286;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_308 = lean_ctor_get(x_301, 0);
x_309 = lean_ctor_get(x_301, 1);
x_310 = lean_ctor_get(x_301, 2);
x_311 = lean_ctor_get(x_301, 3);
x_312 = lean_ctor_get(x_301, 4);
x_313 = lean_ctor_get(x_301, 5);
x_314 = lean_ctor_get(x_301, 6);
x_315 = lean_ctor_get(x_301, 7);
x_316 = lean_ctor_get(x_301, 8);
x_317 = lean_ctor_get(x_301, 9);
x_318 = lean_ctor_get(x_301, 10);
x_319 = lean_ctor_get(x_301, 11);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_301);
lean_inc(x_296);
x_320 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_309, x_233, x_296);
x_321 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_321, 0, x_308);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set(x_321, 2, x_310);
lean_ctor_set(x_321, 3, x_311);
lean_ctor_set(x_321, 4, x_312);
lean_ctor_set(x_321, 5, x_313);
lean_ctor_set(x_321, 6, x_314);
lean_ctor_set(x_321, 7, x_315);
lean_ctor_set(x_321, 8, x_316);
lean_ctor_set(x_321, 9, x_317);
lean_ctor_set(x_321, 10, x_318);
lean_ctor_set(x_321, 11, x_319);
x_322 = lean_st_ref_set(x_3, x_321, x_302);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_235 = x_296;
x_236 = x_323;
goto block_286;
}
}
else
{
uint8_t x_324; 
lean_dec(x_233);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_295);
if (x_324 == 0)
{
return x_295;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_295, 0);
x_326 = lean_ctor_get(x_295, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_295);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
else
{
lean_object* x_328; 
lean_dec(x_233);
x_328 = lean_ctor_get(x_294, 0);
lean_inc(x_328);
lean_dec(x_294);
x_235 = x_328;
x_236 = x_292;
goto block_286;
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_336 = !lean_is_exclusive(x_232);
if (x_336 == 0)
{
return x_232;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_232, 0);
x_338 = lean_ctor_get(x_232, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_232);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_340 = !lean_is_exclusive(x_228);
if (x_340 == 0)
{
return x_228;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_228, 0);
x_342 = lean_ctor_get(x_228, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_228);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
case 3:
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_1);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_345 = lean_ctor_get(x_1, 0);
lean_inc(x_345);
x_346 = l_Lean_Meta_Closure_collectLevel(x_345, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_346, 0);
x_349 = lean_expr_update_sort(x_1, x_348);
lean_ctor_set(x_346, 0, x_349);
return x_346;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_346, 0);
x_351 = lean_ctor_get(x_346, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_346);
x_352 = lean_expr_update_sort(x_1, x_350);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; uint64_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_354 = lean_ctor_get(x_1, 0);
x_355 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_354);
lean_dec(x_1);
lean_inc(x_354);
x_356 = l_Lean_Meta_Closure_collectLevel(x_354, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_359 = x_356;
} else {
 lean_dec_ref(x_356);
 x_359 = lean_box(0);
}
x_360 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_360, 0, x_354);
lean_ctor_set_uint64(x_360, sizeof(void*)*1, x_355);
x_361 = lean_expr_update_sort(x_360, x_357);
if (lean_is_scalar(x_359)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_359;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_358);
return x_362;
}
}
case 4:
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_1);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_364 = lean_ctor_get(x_1, 1);
lean_inc(x_364);
x_365 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_364, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_365, 0);
x_368 = lean_expr_update_const(x_1, x_367);
lean_ctor_set(x_365, 0, x_368);
return x_365;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_365, 0);
x_370 = lean_ctor_get(x_365, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_365);
x_371 = lean_expr_update_const(x_1, x_369);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; uint64_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_373 = lean_ctor_get(x_1, 0);
x_374 = lean_ctor_get(x_1, 1);
x_375 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_1);
lean_inc(x_374);
x_376 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_374, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_379 = x_376;
} else {
 lean_dec_ref(x_376);
 x_379 = lean_box(0);
}
x_380 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_380, 0, x_373);
lean_ctor_set(x_380, 1, x_374);
lean_ctor_set_uint64(x_380, sizeof(void*)*2, x_375);
x_381 = lean_expr_update_const(x_380, x_377);
if (lean_is_scalar(x_379)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_379;
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_378);
return x_382;
}
}
case 5:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_453; uint8_t x_496; 
x_383 = lean_ctor_get(x_1, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_1, 1);
lean_inc(x_384);
x_496 = l_Lean_Expr_hasLevelParam(x_383);
if (x_496 == 0)
{
uint8_t x_497; 
x_497 = l_Lean_Expr_hasFVar(x_383);
if (x_497 == 0)
{
uint8_t x_498; 
x_498 = l_Lean_Expr_hasMVar(x_383);
if (x_498 == 0)
{
x_385 = x_383;
x_386 = x_8;
goto block_452;
}
else
{
lean_object* x_499; 
x_499 = lean_box(0);
x_453 = x_499;
goto block_495;
}
}
else
{
lean_object* x_500; 
x_500 = lean_box(0);
x_453 = x_500;
goto block_495;
}
}
else
{
lean_object* x_501; 
x_501 = lean_box(0);
x_453 = x_501;
goto block_495;
}
block_452:
{
lean_object* x_387; lean_object* x_388; lean_object* x_403; uint8_t x_446; 
x_446 = l_Lean_Expr_hasLevelParam(x_384);
if (x_446 == 0)
{
uint8_t x_447; 
x_447 = l_Lean_Expr_hasFVar(x_384);
if (x_447 == 0)
{
uint8_t x_448; 
x_448 = l_Lean_Expr_hasMVar(x_384);
if (x_448 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_387 = x_384;
x_388 = x_386;
goto block_402;
}
else
{
lean_object* x_449; 
x_449 = lean_box(0);
x_403 = x_449;
goto block_445;
}
}
else
{
lean_object* x_450; 
x_450 = lean_box(0);
x_403 = x_450;
goto block_445;
}
}
else
{
lean_object* x_451; 
x_451 = lean_box(0);
x_403 = x_451;
goto block_445;
}
block_402:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_389; 
x_389 = !lean_is_exclusive(x_1);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_expr_update_app(x_1, x_385, x_387);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_388);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; uint64_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_392 = lean_ctor_get(x_1, 0);
x_393 = lean_ctor_get(x_1, 1);
x_394 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_1);
x_395 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
lean_ctor_set_uint64(x_395, sizeof(void*)*2, x_394);
x_396 = lean_expr_update_app(x_395, x_385, x_387);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_388);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_1);
x_398 = l_Lean_instInhabitedExpr;
x_399 = l_Lean_Meta_Closure_collectExprAux___closed__10;
x_400 = lean_panic_fn(x_398, x_399);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_388);
return x_401;
}
}
block_445:
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_403);
x_404 = lean_st_ref_get(x_7, x_386);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_406 = lean_st_ref_get(x_3, x_405);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_409, x_384);
lean_dec(x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
lean_inc(x_7);
lean_inc(x_384);
x_411 = l_Lean_Meta_Closure_collectExprAux(x_384, x_2, x_3, x_4, x_5, x_6, x_7, x_408);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_st_ref_get(x_7, x_413);
lean_dec(x_7);
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_st_ref_take(x_3, x_415);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = !lean_is_exclusive(x_417);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_417, 1);
lean_inc(x_412);
x_421 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_420, x_384, x_412);
lean_ctor_set(x_417, 1, x_421);
x_422 = lean_st_ref_set(x_3, x_417, x_418);
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
lean_dec(x_422);
x_387 = x_412;
x_388 = x_423;
goto block_402;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_424 = lean_ctor_get(x_417, 0);
x_425 = lean_ctor_get(x_417, 1);
x_426 = lean_ctor_get(x_417, 2);
x_427 = lean_ctor_get(x_417, 3);
x_428 = lean_ctor_get(x_417, 4);
x_429 = lean_ctor_get(x_417, 5);
x_430 = lean_ctor_get(x_417, 6);
x_431 = lean_ctor_get(x_417, 7);
x_432 = lean_ctor_get(x_417, 8);
x_433 = lean_ctor_get(x_417, 9);
x_434 = lean_ctor_get(x_417, 10);
x_435 = lean_ctor_get(x_417, 11);
lean_inc(x_435);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_417);
lean_inc(x_412);
x_436 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_425, x_384, x_412);
x_437 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_437, 0, x_424);
lean_ctor_set(x_437, 1, x_436);
lean_ctor_set(x_437, 2, x_426);
lean_ctor_set(x_437, 3, x_427);
lean_ctor_set(x_437, 4, x_428);
lean_ctor_set(x_437, 5, x_429);
lean_ctor_set(x_437, 6, x_430);
lean_ctor_set(x_437, 7, x_431);
lean_ctor_set(x_437, 8, x_432);
lean_ctor_set(x_437, 9, x_433);
lean_ctor_set(x_437, 10, x_434);
lean_ctor_set(x_437, 11, x_435);
x_438 = lean_st_ref_set(x_3, x_437, x_418);
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
lean_dec(x_438);
x_387 = x_412;
x_388 = x_439;
goto block_402;
}
}
else
{
uint8_t x_440; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_7);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_411);
if (x_440 == 0)
{
return x_411;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_411, 0);
x_442 = lean_ctor_get(x_411, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_411);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
else
{
lean_object* x_444; 
lean_dec(x_384);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_444 = lean_ctor_get(x_410, 0);
lean_inc(x_444);
lean_dec(x_410);
x_387 = x_444;
x_388 = x_408;
goto block_402;
}
}
}
block_495:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_453);
x_454 = lean_st_ref_get(x_7, x_8);
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
lean_dec(x_454);
x_456 = lean_st_ref_get(x_3, x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
x_460 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_459, x_383);
lean_dec(x_459);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_383);
x_461 = l_Lean_Meta_Closure_collectExprAux(x_383, x_2, x_3, x_4, x_5, x_6, x_7, x_458);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = lean_st_ref_get(x_7, x_463);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
lean_dec(x_464);
x_466 = lean_st_ref_take(x_3, x_465);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_469 = !lean_is_exclusive(x_467);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_462);
x_471 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_470, x_383, x_462);
lean_ctor_set(x_467, 1, x_471);
x_472 = lean_st_ref_set(x_3, x_467, x_468);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_385 = x_462;
x_386 = x_473;
goto block_452;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_474 = lean_ctor_get(x_467, 0);
x_475 = lean_ctor_get(x_467, 1);
x_476 = lean_ctor_get(x_467, 2);
x_477 = lean_ctor_get(x_467, 3);
x_478 = lean_ctor_get(x_467, 4);
x_479 = lean_ctor_get(x_467, 5);
x_480 = lean_ctor_get(x_467, 6);
x_481 = lean_ctor_get(x_467, 7);
x_482 = lean_ctor_get(x_467, 8);
x_483 = lean_ctor_get(x_467, 9);
x_484 = lean_ctor_get(x_467, 10);
x_485 = lean_ctor_get(x_467, 11);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_467);
lean_inc(x_462);
x_486 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_475, x_383, x_462);
x_487 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_487, 0, x_474);
lean_ctor_set(x_487, 1, x_486);
lean_ctor_set(x_487, 2, x_476);
lean_ctor_set(x_487, 3, x_477);
lean_ctor_set(x_487, 4, x_478);
lean_ctor_set(x_487, 5, x_479);
lean_ctor_set(x_487, 6, x_480);
lean_ctor_set(x_487, 7, x_481);
lean_ctor_set(x_487, 8, x_482);
lean_ctor_set(x_487, 9, x_483);
lean_ctor_set(x_487, 10, x_484);
lean_ctor_set(x_487, 11, x_485);
x_488 = lean_st_ref_set(x_3, x_487, x_468);
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
lean_dec(x_488);
x_385 = x_462;
x_386 = x_489;
goto block_452;
}
}
else
{
uint8_t x_490; 
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_490 = !lean_is_exclusive(x_461);
if (x_490 == 0)
{
return x_461;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_461, 0);
x_492 = lean_ctor_get(x_461, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_461);
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
}
else
{
lean_object* x_494; 
lean_dec(x_383);
x_494 = lean_ctor_get(x_460, 0);
lean_inc(x_494);
lean_dec(x_460);
x_385 = x_494;
x_386 = x_458;
goto block_452;
}
}
}
case 6:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_576; uint8_t x_619; 
x_502 = lean_ctor_get(x_1, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_1, 2);
lean_inc(x_503);
x_619 = l_Lean_Expr_hasLevelParam(x_502);
if (x_619 == 0)
{
uint8_t x_620; 
x_620 = l_Lean_Expr_hasFVar(x_502);
if (x_620 == 0)
{
uint8_t x_621; 
x_621 = l_Lean_Expr_hasMVar(x_502);
if (x_621 == 0)
{
x_504 = x_502;
x_505 = x_8;
goto block_575;
}
else
{
lean_object* x_622; 
x_622 = lean_box(0);
x_576 = x_622;
goto block_618;
}
}
else
{
lean_object* x_623; 
x_623 = lean_box(0);
x_576 = x_623;
goto block_618;
}
}
else
{
lean_object* x_624; 
x_624 = lean_box(0);
x_576 = x_624;
goto block_618;
}
block_575:
{
lean_object* x_506; lean_object* x_507; lean_object* x_526; uint8_t x_569; 
x_569 = l_Lean_Expr_hasLevelParam(x_503);
if (x_569 == 0)
{
uint8_t x_570; 
x_570 = l_Lean_Expr_hasFVar(x_503);
if (x_570 == 0)
{
uint8_t x_571; 
x_571 = l_Lean_Expr_hasMVar(x_503);
if (x_571 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_506 = x_503;
x_507 = x_505;
goto block_525;
}
else
{
lean_object* x_572; 
x_572 = lean_box(0);
x_526 = x_572;
goto block_568;
}
}
else
{
lean_object* x_573; 
x_573 = lean_box(0);
x_526 = x_573;
goto block_568;
}
}
else
{
lean_object* x_574; 
x_574 = lean_box(0);
x_526 = x_574;
goto block_568;
}
block_525:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_508; 
x_508 = !lean_is_exclusive(x_1);
if (x_508 == 0)
{
uint64_t x_509; uint8_t x_510; lean_object* x_511; lean_object* x_512; 
x_509 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_510 = (uint8_t)((x_509 << 24) >> 61);
x_511 = lean_expr_update_lambda(x_1, x_510, x_504, x_506);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_507);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; uint64_t x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; lean_object* x_520; 
x_513 = lean_ctor_get(x_1, 0);
x_514 = lean_ctor_get(x_1, 1);
x_515 = lean_ctor_get(x_1, 2);
x_516 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_1);
x_517 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_517, 0, x_513);
lean_ctor_set(x_517, 1, x_514);
lean_ctor_set(x_517, 2, x_515);
lean_ctor_set_uint64(x_517, sizeof(void*)*3, x_516);
x_518 = (uint8_t)((x_516 << 24) >> 61);
x_519 = lean_expr_update_lambda(x_517, x_518, x_504, x_506);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_507);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_1);
x_521 = l_Lean_instInhabitedExpr;
x_522 = l_Lean_Meta_Closure_collectExprAux___closed__13;
x_523 = lean_panic_fn(x_521, x_522);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_507);
return x_524;
}
}
block_568:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_526);
x_527 = lean_st_ref_get(x_7, x_505);
x_528 = lean_ctor_get(x_527, 1);
lean_inc(x_528);
lean_dec(x_527);
x_529 = lean_st_ref_get(x_3, x_528);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_532, x_503);
lean_dec(x_532);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; 
lean_inc(x_7);
lean_inc(x_503);
x_534 = l_Lean_Meta_Closure_collectExprAux(x_503, x_2, x_3, x_4, x_5, x_6, x_7, x_531);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = lean_st_ref_get(x_7, x_536);
lean_dec(x_7);
x_538 = lean_ctor_get(x_537, 1);
lean_inc(x_538);
lean_dec(x_537);
x_539 = lean_st_ref_take(x_3, x_538);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = !lean_is_exclusive(x_540);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_543 = lean_ctor_get(x_540, 1);
lean_inc(x_535);
x_544 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_543, x_503, x_535);
lean_ctor_set(x_540, 1, x_544);
x_545 = lean_st_ref_set(x_3, x_540, x_541);
x_546 = lean_ctor_get(x_545, 1);
lean_inc(x_546);
lean_dec(x_545);
x_506 = x_535;
x_507 = x_546;
goto block_525;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_547 = lean_ctor_get(x_540, 0);
x_548 = lean_ctor_get(x_540, 1);
x_549 = lean_ctor_get(x_540, 2);
x_550 = lean_ctor_get(x_540, 3);
x_551 = lean_ctor_get(x_540, 4);
x_552 = lean_ctor_get(x_540, 5);
x_553 = lean_ctor_get(x_540, 6);
x_554 = lean_ctor_get(x_540, 7);
x_555 = lean_ctor_get(x_540, 8);
x_556 = lean_ctor_get(x_540, 9);
x_557 = lean_ctor_get(x_540, 10);
x_558 = lean_ctor_get(x_540, 11);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_555);
lean_inc(x_554);
lean_inc(x_553);
lean_inc(x_552);
lean_inc(x_551);
lean_inc(x_550);
lean_inc(x_549);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_540);
lean_inc(x_535);
x_559 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_548, x_503, x_535);
x_560 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_560, 0, x_547);
lean_ctor_set(x_560, 1, x_559);
lean_ctor_set(x_560, 2, x_549);
lean_ctor_set(x_560, 3, x_550);
lean_ctor_set(x_560, 4, x_551);
lean_ctor_set(x_560, 5, x_552);
lean_ctor_set(x_560, 6, x_553);
lean_ctor_set(x_560, 7, x_554);
lean_ctor_set(x_560, 8, x_555);
lean_ctor_set(x_560, 9, x_556);
lean_ctor_set(x_560, 10, x_557);
lean_ctor_set(x_560, 11, x_558);
x_561 = lean_st_ref_set(x_3, x_560, x_541);
x_562 = lean_ctor_get(x_561, 1);
lean_inc(x_562);
lean_dec(x_561);
x_506 = x_535;
x_507 = x_562;
goto block_525;
}
}
else
{
uint8_t x_563; 
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_7);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_534);
if (x_563 == 0)
{
return x_534;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_534, 0);
x_565 = lean_ctor_get(x_534, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_534);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
else
{
lean_object* x_567; 
lean_dec(x_503);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_567 = lean_ctor_get(x_533, 0);
lean_inc(x_567);
lean_dec(x_533);
x_506 = x_567;
x_507 = x_531;
goto block_525;
}
}
}
block_618:
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_576);
x_577 = lean_st_ref_get(x_7, x_8);
x_578 = lean_ctor_get(x_577, 1);
lean_inc(x_578);
lean_dec(x_577);
x_579 = lean_st_ref_get(x_3, x_578);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_582, x_502);
lean_dec(x_582);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_502);
x_584 = l_Lean_Meta_Closure_collectExprAux(x_502, x_2, x_3, x_4, x_5, x_6, x_7, x_581);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
x_587 = lean_st_ref_get(x_7, x_586);
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
lean_dec(x_587);
x_589 = lean_st_ref_take(x_3, x_588);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_592 = !lean_is_exclusive(x_590);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_593 = lean_ctor_get(x_590, 1);
lean_inc(x_585);
x_594 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_593, x_502, x_585);
lean_ctor_set(x_590, 1, x_594);
x_595 = lean_st_ref_set(x_3, x_590, x_591);
x_596 = lean_ctor_get(x_595, 1);
lean_inc(x_596);
lean_dec(x_595);
x_504 = x_585;
x_505 = x_596;
goto block_575;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_597 = lean_ctor_get(x_590, 0);
x_598 = lean_ctor_get(x_590, 1);
x_599 = lean_ctor_get(x_590, 2);
x_600 = lean_ctor_get(x_590, 3);
x_601 = lean_ctor_get(x_590, 4);
x_602 = lean_ctor_get(x_590, 5);
x_603 = lean_ctor_get(x_590, 6);
x_604 = lean_ctor_get(x_590, 7);
x_605 = lean_ctor_get(x_590, 8);
x_606 = lean_ctor_get(x_590, 9);
x_607 = lean_ctor_get(x_590, 10);
x_608 = lean_ctor_get(x_590, 11);
lean_inc(x_608);
lean_inc(x_607);
lean_inc(x_606);
lean_inc(x_605);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_590);
lean_inc(x_585);
x_609 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_598, x_502, x_585);
x_610 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_610, 0, x_597);
lean_ctor_set(x_610, 1, x_609);
lean_ctor_set(x_610, 2, x_599);
lean_ctor_set(x_610, 3, x_600);
lean_ctor_set(x_610, 4, x_601);
lean_ctor_set(x_610, 5, x_602);
lean_ctor_set(x_610, 6, x_603);
lean_ctor_set(x_610, 7, x_604);
lean_ctor_set(x_610, 8, x_605);
lean_ctor_set(x_610, 9, x_606);
lean_ctor_set(x_610, 10, x_607);
lean_ctor_set(x_610, 11, x_608);
x_611 = lean_st_ref_set(x_3, x_610, x_591);
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
lean_dec(x_611);
x_504 = x_585;
x_505 = x_612;
goto block_575;
}
}
else
{
uint8_t x_613; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_613 = !lean_is_exclusive(x_584);
if (x_613 == 0)
{
return x_584;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_584, 0);
x_615 = lean_ctor_get(x_584, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_584);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
else
{
lean_object* x_617; 
lean_dec(x_502);
x_617 = lean_ctor_get(x_583, 0);
lean_inc(x_617);
lean_dec(x_583);
x_504 = x_617;
x_505 = x_581;
goto block_575;
}
}
}
case 7:
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_699; uint8_t x_742; 
x_625 = lean_ctor_get(x_1, 1);
lean_inc(x_625);
x_626 = lean_ctor_get(x_1, 2);
lean_inc(x_626);
x_742 = l_Lean_Expr_hasLevelParam(x_625);
if (x_742 == 0)
{
uint8_t x_743; 
x_743 = l_Lean_Expr_hasFVar(x_625);
if (x_743 == 0)
{
uint8_t x_744; 
x_744 = l_Lean_Expr_hasMVar(x_625);
if (x_744 == 0)
{
x_627 = x_625;
x_628 = x_8;
goto block_698;
}
else
{
lean_object* x_745; 
x_745 = lean_box(0);
x_699 = x_745;
goto block_741;
}
}
else
{
lean_object* x_746; 
x_746 = lean_box(0);
x_699 = x_746;
goto block_741;
}
}
else
{
lean_object* x_747; 
x_747 = lean_box(0);
x_699 = x_747;
goto block_741;
}
block_698:
{
lean_object* x_629; lean_object* x_630; lean_object* x_649; uint8_t x_692; 
x_692 = l_Lean_Expr_hasLevelParam(x_626);
if (x_692 == 0)
{
uint8_t x_693; 
x_693 = l_Lean_Expr_hasFVar(x_626);
if (x_693 == 0)
{
uint8_t x_694; 
x_694 = l_Lean_Expr_hasMVar(x_626);
if (x_694 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_629 = x_626;
x_630 = x_628;
goto block_648;
}
else
{
lean_object* x_695; 
x_695 = lean_box(0);
x_649 = x_695;
goto block_691;
}
}
else
{
lean_object* x_696; 
x_696 = lean_box(0);
x_649 = x_696;
goto block_691;
}
}
else
{
lean_object* x_697; 
x_697 = lean_box(0);
x_649 = x_697;
goto block_691;
}
block_648:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_631; 
x_631 = !lean_is_exclusive(x_1);
if (x_631 == 0)
{
uint64_t x_632; uint8_t x_633; lean_object* x_634; lean_object* x_635; 
x_632 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_633 = (uint8_t)((x_632 << 24) >> 61);
x_634 = lean_expr_update_forall(x_1, x_633, x_627, x_629);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_630);
return x_635;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; uint64_t x_639; lean_object* x_640; uint8_t x_641; lean_object* x_642; lean_object* x_643; 
x_636 = lean_ctor_get(x_1, 0);
x_637 = lean_ctor_get(x_1, 1);
x_638 = lean_ctor_get(x_1, 2);
x_639 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_638);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_1);
x_640 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_640, 0, x_636);
lean_ctor_set(x_640, 1, x_637);
lean_ctor_set(x_640, 2, x_638);
lean_ctor_set_uint64(x_640, sizeof(void*)*3, x_639);
x_641 = (uint8_t)((x_639 << 24) >> 61);
x_642 = lean_expr_update_forall(x_640, x_641, x_627, x_629);
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_630);
return x_643;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_629);
lean_dec(x_627);
lean_dec(x_1);
x_644 = l_Lean_instInhabitedExpr;
x_645 = l_Lean_Meta_Closure_collectExprAux___closed__16;
x_646 = lean_panic_fn(x_644, x_645);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_630);
return x_647;
}
}
block_691:
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_649);
x_650 = lean_st_ref_get(x_7, x_628);
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
lean_dec(x_650);
x_652 = lean_st_ref_get(x_3, x_651);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_655, x_626);
lean_dec(x_655);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; 
lean_inc(x_7);
lean_inc(x_626);
x_657 = l_Lean_Meta_Closure_collectExprAux(x_626, x_2, x_3, x_4, x_5, x_6, x_7, x_654);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
x_660 = lean_st_ref_get(x_7, x_659);
lean_dec(x_7);
x_661 = lean_ctor_get(x_660, 1);
lean_inc(x_661);
lean_dec(x_660);
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
lean_inc(x_658);
x_667 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_666, x_626, x_658);
lean_ctor_set(x_663, 1, x_667);
x_668 = lean_st_ref_set(x_3, x_663, x_664);
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
lean_dec(x_668);
x_629 = x_658;
x_630 = x_669;
goto block_648;
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
lean_inc(x_658);
x_682 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_671, x_626, x_658);
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
x_629 = x_658;
x_630 = x_685;
goto block_648;
}
}
else
{
uint8_t x_686; 
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_7);
lean_dec(x_1);
x_686 = !lean_is_exclusive(x_657);
if (x_686 == 0)
{
return x_657;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_657, 0);
x_688 = lean_ctor_get(x_657, 1);
lean_inc(x_688);
lean_inc(x_687);
lean_dec(x_657);
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
lean_dec(x_626);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_690 = lean_ctor_get(x_656, 0);
lean_inc(x_690);
lean_dec(x_656);
x_629 = x_690;
x_630 = x_654;
goto block_648;
}
}
}
block_741:
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_699);
x_700 = lean_st_ref_get(x_7, x_8);
x_701 = lean_ctor_get(x_700, 1);
lean_inc(x_701);
lean_dec(x_700);
x_702 = lean_st_ref_get(x_3, x_701);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
lean_dec(x_702);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_706 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_705, x_625);
lean_dec(x_705);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_625);
x_707 = l_Lean_Meta_Closure_collectExprAux(x_625, x_2, x_3, x_4, x_5, x_6, x_7, x_704);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_710 = lean_st_ref_get(x_7, x_709);
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
lean_dec(x_710);
x_712 = lean_st_ref_take(x_3, x_711);
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = !lean_is_exclusive(x_713);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_716 = lean_ctor_get(x_713, 1);
lean_inc(x_708);
x_717 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_716, x_625, x_708);
lean_ctor_set(x_713, 1, x_717);
x_718 = lean_st_ref_set(x_3, x_713, x_714);
x_719 = lean_ctor_get(x_718, 1);
lean_inc(x_719);
lean_dec(x_718);
x_627 = x_708;
x_628 = x_719;
goto block_698;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_720 = lean_ctor_get(x_713, 0);
x_721 = lean_ctor_get(x_713, 1);
x_722 = lean_ctor_get(x_713, 2);
x_723 = lean_ctor_get(x_713, 3);
x_724 = lean_ctor_get(x_713, 4);
x_725 = lean_ctor_get(x_713, 5);
x_726 = lean_ctor_get(x_713, 6);
x_727 = lean_ctor_get(x_713, 7);
x_728 = lean_ctor_get(x_713, 8);
x_729 = lean_ctor_get(x_713, 9);
x_730 = lean_ctor_get(x_713, 10);
x_731 = lean_ctor_get(x_713, 11);
lean_inc(x_731);
lean_inc(x_730);
lean_inc(x_729);
lean_inc(x_728);
lean_inc(x_727);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_724);
lean_inc(x_723);
lean_inc(x_722);
lean_inc(x_721);
lean_inc(x_720);
lean_dec(x_713);
lean_inc(x_708);
x_732 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_721, x_625, x_708);
x_733 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_733, 0, x_720);
lean_ctor_set(x_733, 1, x_732);
lean_ctor_set(x_733, 2, x_722);
lean_ctor_set(x_733, 3, x_723);
lean_ctor_set(x_733, 4, x_724);
lean_ctor_set(x_733, 5, x_725);
lean_ctor_set(x_733, 6, x_726);
lean_ctor_set(x_733, 7, x_727);
lean_ctor_set(x_733, 8, x_728);
lean_ctor_set(x_733, 9, x_729);
lean_ctor_set(x_733, 10, x_730);
lean_ctor_set(x_733, 11, x_731);
x_734 = lean_st_ref_set(x_3, x_733, x_714);
x_735 = lean_ctor_get(x_734, 1);
lean_inc(x_735);
lean_dec(x_734);
x_627 = x_708;
x_628 = x_735;
goto block_698;
}
}
else
{
uint8_t x_736; 
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_736 = !lean_is_exclusive(x_707);
if (x_736 == 0)
{
return x_707;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_707, 0);
x_738 = lean_ctor_get(x_707, 1);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_707);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_737);
lean_ctor_set(x_739, 1, x_738);
return x_739;
}
}
}
else
{
lean_object* x_740; 
lean_dec(x_625);
x_740 = lean_ctor_get(x_706, 0);
lean_inc(x_740);
lean_dec(x_706);
x_627 = x_740;
x_628 = x_704;
goto block_698;
}
}
}
case 8:
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_873; uint8_t x_916; 
x_748 = lean_ctor_get(x_1, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_1, 2);
lean_inc(x_749);
x_750 = lean_ctor_get(x_1, 3);
lean_inc(x_750);
x_916 = l_Lean_Expr_hasLevelParam(x_748);
if (x_916 == 0)
{
uint8_t x_917; 
x_917 = l_Lean_Expr_hasFVar(x_748);
if (x_917 == 0)
{
uint8_t x_918; 
x_918 = l_Lean_Expr_hasMVar(x_748);
if (x_918 == 0)
{
x_751 = x_748;
x_752 = x_8;
goto block_872;
}
else
{
lean_object* x_919; 
x_919 = lean_box(0);
x_873 = x_919;
goto block_915;
}
}
else
{
lean_object* x_920; 
x_920 = lean_box(0);
x_873 = x_920;
goto block_915;
}
}
else
{
lean_object* x_921; 
x_921 = lean_box(0);
x_873 = x_921;
goto block_915;
}
block_872:
{
lean_object* x_753; lean_object* x_754; lean_object* x_823; uint8_t x_866; 
x_866 = l_Lean_Expr_hasLevelParam(x_749);
if (x_866 == 0)
{
uint8_t x_867; 
x_867 = l_Lean_Expr_hasFVar(x_749);
if (x_867 == 0)
{
uint8_t x_868; 
x_868 = l_Lean_Expr_hasMVar(x_749);
if (x_868 == 0)
{
x_753 = x_749;
x_754 = x_752;
goto block_822;
}
else
{
lean_object* x_869; 
x_869 = lean_box(0);
x_823 = x_869;
goto block_865;
}
}
else
{
lean_object* x_870; 
x_870 = lean_box(0);
x_823 = x_870;
goto block_865;
}
}
else
{
lean_object* x_871; 
x_871 = lean_box(0);
x_823 = x_871;
goto block_865;
}
block_822:
{
lean_object* x_755; lean_object* x_756; lean_object* x_773; uint8_t x_816; 
x_816 = l_Lean_Expr_hasLevelParam(x_750);
if (x_816 == 0)
{
uint8_t x_817; 
x_817 = l_Lean_Expr_hasFVar(x_750);
if (x_817 == 0)
{
uint8_t x_818; 
x_818 = l_Lean_Expr_hasMVar(x_750);
if (x_818 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_755 = x_750;
x_756 = x_754;
goto block_772;
}
else
{
lean_object* x_819; 
x_819 = lean_box(0);
x_773 = x_819;
goto block_815;
}
}
else
{
lean_object* x_820; 
x_820 = lean_box(0);
x_773 = x_820;
goto block_815;
}
}
else
{
lean_object* x_821; 
x_821 = lean_box(0);
x_773 = x_821;
goto block_815;
}
block_772:
{
if (lean_obj_tag(x_1) == 8)
{
uint8_t x_757; 
x_757 = !lean_is_exclusive(x_1);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; 
x_758 = lean_expr_update_let(x_1, x_751, x_753, x_755);
x_759 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_756);
return x_759;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; uint64_t x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_760 = lean_ctor_get(x_1, 0);
x_761 = lean_ctor_get(x_1, 1);
x_762 = lean_ctor_get(x_1, 2);
x_763 = lean_ctor_get(x_1, 3);
x_764 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_763);
lean_inc(x_762);
lean_inc(x_761);
lean_inc(x_760);
lean_dec(x_1);
x_765 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_765, 0, x_760);
lean_ctor_set(x_765, 1, x_761);
lean_ctor_set(x_765, 2, x_762);
lean_ctor_set(x_765, 3, x_763);
lean_ctor_set_uint64(x_765, sizeof(void*)*4, x_764);
x_766 = lean_expr_update_let(x_765, x_751, x_753, x_755);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_756);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_755);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_1);
x_768 = l_Lean_instInhabitedExpr;
x_769 = l_Lean_Meta_Closure_collectExprAux___closed__19;
x_770 = lean_panic_fn(x_768, x_769);
x_771 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set(x_771, 1, x_756);
return x_771;
}
}
block_815:
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_773);
x_774 = lean_st_ref_get(x_7, x_754);
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
lean_dec(x_774);
x_776 = lean_st_ref_get(x_3, x_775);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_780 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_779, x_750);
lean_dec(x_779);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; 
lean_inc(x_7);
lean_inc(x_750);
x_781 = l_Lean_Meta_Closure_collectExprAux(x_750, x_2, x_3, x_4, x_5, x_6, x_7, x_778);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; uint8_t x_789; 
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
lean_dec(x_781);
x_784 = lean_st_ref_get(x_7, x_783);
lean_dec(x_7);
x_785 = lean_ctor_get(x_784, 1);
lean_inc(x_785);
lean_dec(x_784);
x_786 = lean_st_ref_take(x_3, x_785);
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
x_789 = !lean_is_exclusive(x_787);
if (x_789 == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_790 = lean_ctor_get(x_787, 1);
lean_inc(x_782);
x_791 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_790, x_750, x_782);
lean_ctor_set(x_787, 1, x_791);
x_792 = lean_st_ref_set(x_3, x_787, x_788);
x_793 = lean_ctor_get(x_792, 1);
lean_inc(x_793);
lean_dec(x_792);
x_755 = x_782;
x_756 = x_793;
goto block_772;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_794 = lean_ctor_get(x_787, 0);
x_795 = lean_ctor_get(x_787, 1);
x_796 = lean_ctor_get(x_787, 2);
x_797 = lean_ctor_get(x_787, 3);
x_798 = lean_ctor_get(x_787, 4);
x_799 = lean_ctor_get(x_787, 5);
x_800 = lean_ctor_get(x_787, 6);
x_801 = lean_ctor_get(x_787, 7);
x_802 = lean_ctor_get(x_787, 8);
x_803 = lean_ctor_get(x_787, 9);
x_804 = lean_ctor_get(x_787, 10);
x_805 = lean_ctor_get(x_787, 11);
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
lean_dec(x_787);
lean_inc(x_782);
x_806 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_795, x_750, x_782);
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
x_808 = lean_st_ref_set(x_3, x_807, x_788);
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
lean_dec(x_808);
x_755 = x_782;
x_756 = x_809;
goto block_772;
}
}
else
{
uint8_t x_810; 
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_7);
lean_dec(x_1);
x_810 = !lean_is_exclusive(x_781);
if (x_810 == 0)
{
return x_781;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_811 = lean_ctor_get(x_781, 0);
x_812 = lean_ctor_get(x_781, 1);
lean_inc(x_812);
lean_inc(x_811);
lean_dec(x_781);
x_813 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_813, 0, x_811);
lean_ctor_set(x_813, 1, x_812);
return x_813;
}
}
}
else
{
lean_object* x_814; 
lean_dec(x_750);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_814 = lean_ctor_get(x_780, 0);
lean_inc(x_814);
lean_dec(x_780);
x_755 = x_814;
x_756 = x_778;
goto block_772;
}
}
}
block_865:
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
lean_dec(x_823);
x_824 = lean_st_ref_get(x_7, x_752);
x_825 = lean_ctor_get(x_824, 1);
lean_inc(x_825);
lean_dec(x_824);
x_826 = lean_st_ref_get(x_3, x_825);
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
lean_dec(x_827);
x_830 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_829, x_749);
lean_dec(x_829);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_749);
x_831 = l_Lean_Meta_Closure_collectExprAux(x_749, x_2, x_3, x_4, x_5, x_6, x_7, x_828);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; uint8_t x_839; 
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
lean_dec(x_831);
x_834 = lean_st_ref_get(x_7, x_833);
x_835 = lean_ctor_get(x_834, 1);
lean_inc(x_835);
lean_dec(x_834);
x_836 = lean_st_ref_take(x_3, x_835);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
lean_dec(x_836);
x_839 = !lean_is_exclusive(x_837);
if (x_839 == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_840 = lean_ctor_get(x_837, 1);
lean_inc(x_832);
x_841 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_840, x_749, x_832);
lean_ctor_set(x_837, 1, x_841);
x_842 = lean_st_ref_set(x_3, x_837, x_838);
x_843 = lean_ctor_get(x_842, 1);
lean_inc(x_843);
lean_dec(x_842);
x_753 = x_832;
x_754 = x_843;
goto block_822;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_844 = lean_ctor_get(x_837, 0);
x_845 = lean_ctor_get(x_837, 1);
x_846 = lean_ctor_get(x_837, 2);
x_847 = lean_ctor_get(x_837, 3);
x_848 = lean_ctor_get(x_837, 4);
x_849 = lean_ctor_get(x_837, 5);
x_850 = lean_ctor_get(x_837, 6);
x_851 = lean_ctor_get(x_837, 7);
x_852 = lean_ctor_get(x_837, 8);
x_853 = lean_ctor_get(x_837, 9);
x_854 = lean_ctor_get(x_837, 10);
x_855 = lean_ctor_get(x_837, 11);
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
lean_inc(x_845);
lean_inc(x_844);
lean_dec(x_837);
lean_inc(x_832);
x_856 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_845, x_749, x_832);
x_857 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_857, 0, x_844);
lean_ctor_set(x_857, 1, x_856);
lean_ctor_set(x_857, 2, x_846);
lean_ctor_set(x_857, 3, x_847);
lean_ctor_set(x_857, 4, x_848);
lean_ctor_set(x_857, 5, x_849);
lean_ctor_set(x_857, 6, x_850);
lean_ctor_set(x_857, 7, x_851);
lean_ctor_set(x_857, 8, x_852);
lean_ctor_set(x_857, 9, x_853);
lean_ctor_set(x_857, 10, x_854);
lean_ctor_set(x_857, 11, x_855);
x_858 = lean_st_ref_set(x_3, x_857, x_838);
x_859 = lean_ctor_get(x_858, 1);
lean_inc(x_859);
lean_dec(x_858);
x_753 = x_832;
x_754 = x_859;
goto block_822;
}
}
else
{
uint8_t x_860; 
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_860 = !lean_is_exclusive(x_831);
if (x_860 == 0)
{
return x_831;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_831, 0);
x_862 = lean_ctor_get(x_831, 1);
lean_inc(x_862);
lean_inc(x_861);
lean_dec(x_831);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_862);
return x_863;
}
}
}
else
{
lean_object* x_864; 
lean_dec(x_749);
x_864 = lean_ctor_get(x_830, 0);
lean_inc(x_864);
lean_dec(x_830);
x_753 = x_864;
x_754 = x_828;
goto block_822;
}
}
}
block_915:
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec(x_873);
x_874 = lean_st_ref_get(x_7, x_8);
x_875 = lean_ctor_get(x_874, 1);
lean_inc(x_875);
lean_dec(x_874);
x_876 = lean_st_ref_get(x_3, x_875);
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_880 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_879, x_748);
lean_dec(x_879);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_748);
x_881 = l_Lean_Meta_Closure_collectExprAux(x_748, x_2, x_3, x_4, x_5, x_6, x_7, x_878);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; uint8_t x_889; 
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_884 = lean_st_ref_get(x_7, x_883);
x_885 = lean_ctor_get(x_884, 1);
lean_inc(x_885);
lean_dec(x_884);
x_886 = lean_st_ref_take(x_3, x_885);
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
lean_dec(x_886);
x_889 = !lean_is_exclusive(x_887);
if (x_889 == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_890 = lean_ctor_get(x_887, 1);
lean_inc(x_882);
x_891 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_890, x_748, x_882);
lean_ctor_set(x_887, 1, x_891);
x_892 = lean_st_ref_set(x_3, x_887, x_888);
x_893 = lean_ctor_get(x_892, 1);
lean_inc(x_893);
lean_dec(x_892);
x_751 = x_882;
x_752 = x_893;
goto block_872;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_894 = lean_ctor_get(x_887, 0);
x_895 = lean_ctor_get(x_887, 1);
x_896 = lean_ctor_get(x_887, 2);
x_897 = lean_ctor_get(x_887, 3);
x_898 = lean_ctor_get(x_887, 4);
x_899 = lean_ctor_get(x_887, 5);
x_900 = lean_ctor_get(x_887, 6);
x_901 = lean_ctor_get(x_887, 7);
x_902 = lean_ctor_get(x_887, 8);
x_903 = lean_ctor_get(x_887, 9);
x_904 = lean_ctor_get(x_887, 10);
x_905 = lean_ctor_get(x_887, 11);
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
lean_inc(x_895);
lean_inc(x_894);
lean_dec(x_887);
lean_inc(x_882);
x_906 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_895, x_748, x_882);
x_907 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_907, 0, x_894);
lean_ctor_set(x_907, 1, x_906);
lean_ctor_set(x_907, 2, x_896);
lean_ctor_set(x_907, 3, x_897);
lean_ctor_set(x_907, 4, x_898);
lean_ctor_set(x_907, 5, x_899);
lean_ctor_set(x_907, 6, x_900);
lean_ctor_set(x_907, 7, x_901);
lean_ctor_set(x_907, 8, x_902);
lean_ctor_set(x_907, 9, x_903);
lean_ctor_set(x_907, 10, x_904);
lean_ctor_set(x_907, 11, x_905);
x_908 = lean_st_ref_set(x_3, x_907, x_888);
x_909 = lean_ctor_get(x_908, 1);
lean_inc(x_909);
lean_dec(x_908);
x_751 = x_882;
x_752 = x_909;
goto block_872;
}
}
else
{
uint8_t x_910; 
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_910 = !lean_is_exclusive(x_881);
if (x_910 == 0)
{
return x_881;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_911 = lean_ctor_get(x_881, 0);
x_912 = lean_ctor_get(x_881, 1);
lean_inc(x_912);
lean_inc(x_911);
lean_dec(x_881);
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_912);
return x_913;
}
}
}
else
{
lean_object* x_914; 
lean_dec(x_748);
x_914 = lean_ctor_get(x_880, 0);
lean_inc(x_914);
lean_dec(x_880);
x_751 = x_914;
x_752 = x_878;
goto block_872;
}
}
}
case 10:
{
lean_object* x_922; lean_object* x_923; uint8_t x_966; 
x_922 = lean_ctor_get(x_1, 1);
lean_inc(x_922);
x_966 = l_Lean_Expr_hasLevelParam(x_922);
if (x_966 == 0)
{
uint8_t x_967; 
x_967 = l_Lean_Expr_hasFVar(x_922);
if (x_967 == 0)
{
uint8_t x_968; 
x_968 = l_Lean_Expr_hasMVar(x_922);
if (x_968 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_922;
x_10 = x_8;
goto block_24;
}
else
{
lean_object* x_969; 
x_969 = lean_box(0);
x_923 = x_969;
goto block_965;
}
}
else
{
lean_object* x_970; 
x_970 = lean_box(0);
x_923 = x_970;
goto block_965;
}
}
else
{
lean_object* x_971; 
x_971 = lean_box(0);
x_923 = x_971;
goto block_965;
}
block_965:
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_923);
x_924 = lean_st_ref_get(x_7, x_8);
x_925 = lean_ctor_get(x_924, 1);
lean_inc(x_925);
lean_dec(x_924);
x_926 = lean_st_ref_get(x_3, x_925);
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
lean_dec(x_926);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_930 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_929, x_922);
lean_dec(x_929);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; 
lean_inc(x_7);
lean_inc(x_922);
x_931 = l_Lean_Meta_Closure_collectExprAux(x_922, x_2, x_3, x_4, x_5, x_6, x_7, x_928);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; uint8_t x_939; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
lean_dec(x_931);
x_934 = lean_st_ref_get(x_7, x_933);
lean_dec(x_7);
x_935 = lean_ctor_get(x_934, 1);
lean_inc(x_935);
lean_dec(x_934);
x_936 = lean_st_ref_take(x_3, x_935);
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_936, 1);
lean_inc(x_938);
lean_dec(x_936);
x_939 = !lean_is_exclusive(x_937);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_940 = lean_ctor_get(x_937, 1);
lean_inc(x_932);
x_941 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_940, x_922, x_932);
lean_ctor_set(x_937, 1, x_941);
x_942 = lean_st_ref_set(x_3, x_937, x_938);
x_943 = lean_ctor_get(x_942, 1);
lean_inc(x_943);
lean_dec(x_942);
x_9 = x_932;
x_10 = x_943;
goto block_24;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_944 = lean_ctor_get(x_937, 0);
x_945 = lean_ctor_get(x_937, 1);
x_946 = lean_ctor_get(x_937, 2);
x_947 = lean_ctor_get(x_937, 3);
x_948 = lean_ctor_get(x_937, 4);
x_949 = lean_ctor_get(x_937, 5);
x_950 = lean_ctor_get(x_937, 6);
x_951 = lean_ctor_get(x_937, 7);
x_952 = lean_ctor_get(x_937, 8);
x_953 = lean_ctor_get(x_937, 9);
x_954 = lean_ctor_get(x_937, 10);
x_955 = lean_ctor_get(x_937, 11);
lean_inc(x_955);
lean_inc(x_954);
lean_inc(x_953);
lean_inc(x_952);
lean_inc(x_951);
lean_inc(x_950);
lean_inc(x_949);
lean_inc(x_948);
lean_inc(x_947);
lean_inc(x_946);
lean_inc(x_945);
lean_inc(x_944);
lean_dec(x_937);
lean_inc(x_932);
x_956 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_945, x_922, x_932);
x_957 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_957, 0, x_944);
lean_ctor_set(x_957, 1, x_956);
lean_ctor_set(x_957, 2, x_946);
lean_ctor_set(x_957, 3, x_947);
lean_ctor_set(x_957, 4, x_948);
lean_ctor_set(x_957, 5, x_949);
lean_ctor_set(x_957, 6, x_950);
lean_ctor_set(x_957, 7, x_951);
lean_ctor_set(x_957, 8, x_952);
lean_ctor_set(x_957, 9, x_953);
lean_ctor_set(x_957, 10, x_954);
lean_ctor_set(x_957, 11, x_955);
x_958 = lean_st_ref_set(x_3, x_957, x_938);
x_959 = lean_ctor_get(x_958, 1);
lean_inc(x_959);
lean_dec(x_958);
x_9 = x_932;
x_10 = x_959;
goto block_24;
}
}
else
{
uint8_t x_960; 
lean_dec(x_922);
lean_dec(x_7);
lean_dec(x_1);
x_960 = !lean_is_exclusive(x_931);
if (x_960 == 0)
{
return x_931;
}
else
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_961 = lean_ctor_get(x_931, 0);
x_962 = lean_ctor_get(x_931, 1);
lean_inc(x_962);
lean_inc(x_961);
lean_dec(x_931);
x_963 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_963, 0, x_961);
lean_ctor_set(x_963, 1, x_962);
return x_963;
}
}
}
else
{
lean_object* x_964; 
lean_dec(x_922);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_964 = lean_ctor_get(x_930, 0);
lean_inc(x_964);
lean_dec(x_930);
x_9 = x_964;
x_10 = x_928;
goto block_24;
}
}
}
case 11:
{
lean_object* x_972; lean_object* x_973; uint8_t x_1016; 
x_972 = lean_ctor_get(x_1, 2);
lean_inc(x_972);
x_1016 = l_Lean_Expr_hasLevelParam(x_972);
if (x_1016 == 0)
{
uint8_t x_1017; 
x_1017 = l_Lean_Expr_hasFVar(x_972);
if (x_1017 == 0)
{
uint8_t x_1018; 
x_1018 = l_Lean_Expr_hasMVar(x_972);
if (x_1018 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = x_972;
x_26 = x_8;
goto block_41;
}
else
{
lean_object* x_1019; 
x_1019 = lean_box(0);
x_973 = x_1019;
goto block_1015;
}
}
else
{
lean_object* x_1020; 
x_1020 = lean_box(0);
x_973 = x_1020;
goto block_1015;
}
}
else
{
lean_object* x_1021; 
x_1021 = lean_box(0);
x_973 = x_1021;
goto block_1015;
}
block_1015:
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_973);
x_974 = lean_st_ref_get(x_7, x_8);
x_975 = lean_ctor_get(x_974, 1);
lean_inc(x_975);
lean_dec(x_974);
x_976 = lean_st_ref_get(x_3, x_975);
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec(x_976);
x_979 = lean_ctor_get(x_977, 1);
lean_inc(x_979);
lean_dec(x_977);
x_980 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_979, x_972);
lean_dec(x_979);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; 
lean_inc(x_7);
lean_inc(x_972);
x_981 = l_Lean_Meta_Closure_collectExprAux(x_972, x_2, x_3, x_4, x_5, x_6, x_7, x_978);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; uint8_t x_989; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
lean_dec(x_981);
x_984 = lean_st_ref_get(x_7, x_983);
lean_dec(x_7);
x_985 = lean_ctor_get(x_984, 1);
lean_inc(x_985);
lean_dec(x_984);
x_986 = lean_st_ref_take(x_3, x_985);
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
lean_dec(x_986);
x_989 = !lean_is_exclusive(x_987);
if (x_989 == 0)
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_990 = lean_ctor_get(x_987, 1);
lean_inc(x_982);
x_991 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_990, x_972, x_982);
lean_ctor_set(x_987, 1, x_991);
x_992 = lean_st_ref_set(x_3, x_987, x_988);
x_993 = lean_ctor_get(x_992, 1);
lean_inc(x_993);
lean_dec(x_992);
x_25 = x_982;
x_26 = x_993;
goto block_41;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_994 = lean_ctor_get(x_987, 0);
x_995 = lean_ctor_get(x_987, 1);
x_996 = lean_ctor_get(x_987, 2);
x_997 = lean_ctor_get(x_987, 3);
x_998 = lean_ctor_get(x_987, 4);
x_999 = lean_ctor_get(x_987, 5);
x_1000 = lean_ctor_get(x_987, 6);
x_1001 = lean_ctor_get(x_987, 7);
x_1002 = lean_ctor_get(x_987, 8);
x_1003 = lean_ctor_get(x_987, 9);
x_1004 = lean_ctor_get(x_987, 10);
x_1005 = lean_ctor_get(x_987, 11);
lean_inc(x_1005);
lean_inc(x_1004);
lean_inc(x_1003);
lean_inc(x_1002);
lean_inc(x_1001);
lean_inc(x_1000);
lean_inc(x_999);
lean_inc(x_998);
lean_inc(x_997);
lean_inc(x_996);
lean_inc(x_995);
lean_inc(x_994);
lean_dec(x_987);
lean_inc(x_982);
x_1006 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_995, x_972, x_982);
x_1007 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1007, 0, x_994);
lean_ctor_set(x_1007, 1, x_1006);
lean_ctor_set(x_1007, 2, x_996);
lean_ctor_set(x_1007, 3, x_997);
lean_ctor_set(x_1007, 4, x_998);
lean_ctor_set(x_1007, 5, x_999);
lean_ctor_set(x_1007, 6, x_1000);
lean_ctor_set(x_1007, 7, x_1001);
lean_ctor_set(x_1007, 8, x_1002);
lean_ctor_set(x_1007, 9, x_1003);
lean_ctor_set(x_1007, 10, x_1004);
lean_ctor_set(x_1007, 11, x_1005);
x_1008 = lean_st_ref_set(x_3, x_1007, x_988);
x_1009 = lean_ctor_get(x_1008, 1);
lean_inc(x_1009);
lean_dec(x_1008);
x_25 = x_982;
x_26 = x_1009;
goto block_41;
}
}
else
{
uint8_t x_1010; 
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_1);
x_1010 = !lean_is_exclusive(x_981);
if (x_1010 == 0)
{
return x_981;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_981, 0);
x_1012 = lean_ctor_get(x_981, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_981);
x_1013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
return x_1013;
}
}
}
else
{
lean_object* x_1014; 
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1014 = lean_ctor_get(x_980, 0);
lean_inc(x_1014);
lean_dec(x_980);
x_25 = x_1014;
x_26 = x_978;
goto block_41;
}
}
}
default: 
{
lean_object* x_1022; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1022 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1022, 0, x_1);
lean_ctor_set(x_1022, 1, x_8);
return x_1022;
}
}
block_24:
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_expr_update_mdata(x_1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint64(x_17, sizeof(void*)*2, x_16);
x_18 = lean_expr_update_mdata(x_17, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_1);
x_20 = l_Lean_instInhabitedExpr;
x_21 = l_Lean_Meta_Closure_collectExprAux___closed__4;
x_22 = lean_panic_fn(x_20, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
block_41:
{
if (lean_obj_tag(x_1) == 11)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_expr_update_proj(x_1, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
x_34 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_33);
x_35 = lean_expr_update_proj(x_34, x_25);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
lean_dec(x_1);
x_37 = l_Lean_instInhabitedExpr;
x_38 = l_Lean_Meta_Closure_collectExprAux___closed__7;
x_39 = lean_panic_fn(x_37, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_26);
return x_40;
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
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectExprAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_99; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_99 = l_Lean_Expr_hasLevelParam(x_11);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Expr_hasFVar(x_11);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Expr_hasMVar(x_11);
if (x_101 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_102; 
lean_free_object(x_9);
x_102 = lean_box(0);
x_13 = x_102;
goto block_98;
}
}
else
{
lean_object* x_103; 
lean_free_object(x_9);
x_103 = lean_box(0);
x_13 = x_103;
goto block_98;
}
}
else
{
lean_object* x_104; 
lean_free_object(x_9);
x_104 = lean_box(0);
x_13 = x_104;
goto block_98;
}
block_98:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_13);
x_14 = lean_st_ref_get(x_7, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_3, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_20, x_11);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_free_object(x_16);
lean_inc(x_7);
lean_inc(x_11);
x_22 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_7, x_24);
lean_dec(x_7);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_23);
x_32 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_31, x_11, x_23);
lean_ctor_set(x_28, 1, x_32);
x_33 = lean_st_ref_set(x_3, x_28, x_29);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_23);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
x_40 = lean_ctor_get(x_28, 2);
x_41 = lean_ctor_get(x_28, 3);
x_42 = lean_ctor_get(x_28, 4);
x_43 = lean_ctor_get(x_28, 5);
x_44 = lean_ctor_get(x_28, 6);
x_45 = lean_ctor_get(x_28, 7);
x_46 = lean_ctor_get(x_28, 8);
x_47 = lean_ctor_get(x_28, 9);
x_48 = lean_ctor_get(x_28, 10);
x_49 = lean_ctor_get(x_28, 11);
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
lean_dec(x_28);
lean_inc(x_23);
x_50 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_39, x_11, x_23);
x_51 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_50);
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
x_52 = lean_st_ref_set(x_3, x_51, x_29);
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
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_23);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_11);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = lean_ctor_get(x_21, 0);
lean_inc(x_60);
lean_dec(x_21);
lean_ctor_set(x_16, 0, x_60);
return x_16;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_63, x_11);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_inc(x_7);
lean_inc(x_11);
x_65 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_st_ref_get(x_7, x_67);
lean_dec(x_7);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_take(x_3, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_71, 7);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 8);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 9);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 10);
lean_inc(x_83);
x_84 = lean_ctor_get(x_71, 11);
lean_inc(x_84);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 lean_ctor_release(x_71, 6);
 lean_ctor_release(x_71, 7);
 lean_ctor_release(x_71, 8);
 lean_ctor_release(x_71, 9);
 lean_ctor_release(x_71, 10);
 lean_ctor_release(x_71, 11);
 x_85 = x_71;
} else {
 lean_dec_ref(x_71);
 x_85 = lean_box(0);
}
lean_inc(x_66);
x_86 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_74, x_11, x_66);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 12, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_75);
lean_ctor_set(x_87, 3, x_76);
lean_ctor_set(x_87, 4, x_77);
lean_ctor_set(x_87, 5, x_78);
lean_ctor_set(x_87, 6, x_79);
lean_ctor_set(x_87, 7, x_80);
lean_ctor_set(x_87, 8, x_81);
lean_ctor_set(x_87, 9, x_82);
lean_ctor_set(x_87, 10, x_83);
lean_ctor_set(x_87, 11, x_84);
x_88 = lean_st_ref_set(x_3, x_87, x_72);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_66);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_11);
lean_dec(x_7);
x_92 = lean_ctor_get(x_65, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_65, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_94 = x_65;
} else {
 lean_dec_ref(x_65);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = lean_ctor_get(x_64, 0);
lean_inc(x_96);
lean_dec(x_64);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_62);
return x_97;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_150; 
x_105 = lean_ctor_get(x_9, 0);
x_106 = lean_ctor_get(x_9, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_9);
x_150 = l_Lean_Expr_hasLevelParam(x_105);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = l_Lean_Expr_hasFVar(x_105);
if (x_151 == 0)
{
uint8_t x_152; 
x_152 = l_Lean_Expr_hasMVar(x_105);
if (x_152 == 0)
{
lean_object* x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_105);
lean_ctor_set(x_153, 1, x_106);
return x_153;
}
else
{
lean_object* x_154; 
x_154 = lean_box(0);
x_107 = x_154;
goto block_149;
}
}
else
{
lean_object* x_155; 
x_155 = lean_box(0);
x_107 = x_155;
goto block_149;
}
}
else
{
lean_object* x_156; 
x_156 = lean_box(0);
x_107 = x_156;
goto block_149;
}
block_149:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
x_108 = lean_st_ref_get(x_7, x_106);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_st_ref_get(x_3, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_114, x_105);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_inc(x_7);
lean_inc(x_105);
x_116 = l_Lean_Meta_Closure_collectExprAux(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_get(x_7, x_118);
lean_dec(x_7);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_st_ref_take(x_3, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_122, 5);
lean_inc(x_129);
x_130 = lean_ctor_get(x_122, 6);
lean_inc(x_130);
x_131 = lean_ctor_get(x_122, 7);
lean_inc(x_131);
x_132 = lean_ctor_get(x_122, 8);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 9);
lean_inc(x_133);
x_134 = lean_ctor_get(x_122, 10);
lean_inc(x_134);
x_135 = lean_ctor_get(x_122, 11);
lean_inc(x_135);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 lean_ctor_release(x_122, 6);
 lean_ctor_release(x_122, 7);
 lean_ctor_release(x_122, 8);
 lean_ctor_release(x_122, 9);
 lean_ctor_release(x_122, 10);
 lean_ctor_release(x_122, 11);
 x_136 = x_122;
} else {
 lean_dec_ref(x_122);
 x_136 = lean_box(0);
}
lean_inc(x_117);
x_137 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_125, x_105, x_117);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 12, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_126);
lean_ctor_set(x_138, 3, x_127);
lean_ctor_set(x_138, 4, x_128);
lean_ctor_set(x_138, 5, x_129);
lean_ctor_set(x_138, 6, x_130);
lean_ctor_set(x_138, 7, x_131);
lean_ctor_set(x_138, 8, x_132);
lean_ctor_set(x_138, 9, x_133);
lean_ctor_set(x_138, 10, x_134);
lean_ctor_set(x_138, 11, x_135);
x_139 = lean_st_ref_set(x_3, x_138, x_123);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_117);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_105);
lean_dec(x_7);
x_143 = lean_ctor_get(x_116, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_116, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_145 = x_116;
} else {
 lean_dec_ref(x_116);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_105);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_147 = lean_ctor_get(x_115, 0);
lean_inc(x_147);
lean_dec(x_115);
if (lean_is_scalar(x_113)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_113;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_112);
return x_148;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = !lean_is_exclusive(x_9);
if (x_157 == 0)
{
return x_9;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_9, 0);
x_159 = lean_ctor_get(x_9, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_9);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectExpr(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
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
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t x_1) {
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
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Closure_pickNextToProcess_x3f(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_pushFVarArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_Closure_pushLocalDecl(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_14;
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
lean_object* l_Lean_Meta_Closure_process(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Closure_process(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
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
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get_uint8(x_11, 0);
x_43 = lean_ctor_get_uint8(x_11, 1);
x_44 = lean_ctor_get_uint8(x_11, 2);
x_45 = lean_ctor_get_uint8(x_11, 3);
x_46 = lean_ctor_get_uint8(x_11, 4);
x_47 = lean_ctor_get_uint8(x_11, 5);
x_48 = lean_ctor_get_uint8(x_11, 6);
x_49 = lean_ctor_get_uint8(x_11, 8);
x_50 = lean_ctor_get_uint8(x_11, 9);
lean_dec(x_11);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 0, 10);
lean_ctor_set_uint8(x_52, 0, x_42);
lean_ctor_set_uint8(x_52, 1, x_43);
lean_ctor_set_uint8(x_52, 2, x_44);
lean_ctor_set_uint8(x_52, 3, x_45);
lean_ctor_set_uint8(x_52, 4, x_46);
lean_ctor_set_uint8(x_52, 5, x_47);
lean_ctor_set_uint8(x_52, 6, x_48);
lean_ctor_set_uint8(x_52, 7, x_51);
lean_ctor_set_uint8(x_52, 8, x_49);
lean_ctor_set_uint8(x_52, 9, x_50);
lean_ctor_set(x_5, 0, x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_57);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_57);
lean_dec(x_54);
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_54);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_70 = x_56;
} else {
 lean_dec_ref(x_56);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_72 = lean_ctor_get(x_53, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_74 = x_53;
} else {
 lean_dec_ref(x_53);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_ctor_get(x_5, 2);
x_78 = lean_ctor_get(x_5, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_5);
x_79 = lean_ctor_get_uint8(x_11, 0);
x_80 = lean_ctor_get_uint8(x_11, 1);
x_81 = lean_ctor_get_uint8(x_11, 2);
x_82 = lean_ctor_get_uint8(x_11, 3);
x_83 = lean_ctor_get_uint8(x_11, 4);
x_84 = lean_ctor_get_uint8(x_11, 5);
x_85 = lean_ctor_get_uint8(x_11, 6);
x_86 = lean_ctor_get_uint8(x_11, 8);
x_87 = lean_ctor_get_uint8(x_11, 9);
if (lean_is_exclusive(x_11)) {
 x_88 = x_11;
} else {
 lean_dec_ref(x_11);
 x_88 = lean_box(0);
}
x_89 = 1;
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 0, 10);
} else {
 x_90 = x_88;
}
lean_ctor_set_uint8(x_90, 0, x_79);
lean_ctor_set_uint8(x_90, 1, x_80);
lean_ctor_set_uint8(x_90, 2, x_81);
lean_ctor_set_uint8(x_90, 3, x_82);
lean_ctor_set_uint8(x_90, 4, x_83);
lean_ctor_set_uint8(x_90, 5, x_84);
lean_ctor_set_uint8(x_90, 6, x_85);
lean_ctor_set_uint8(x_90, 7, x_89);
lean_ctor_set_uint8(x_90, 8, x_86);
lean_ctor_set_uint8(x_90, 9, x_87);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_76);
lean_ctor_set(x_91, 2, x_77);
lean_ctor_set(x_91, 3, x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_91);
x_92 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_91, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_91);
x_95 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_91, x_6, x_7, x_8, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Meta_Closure_process(x_3, x_4, x_91, x_6, x_7, x_8, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_96);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_96);
lean_dec(x_93);
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_105 = x_98;
} else {
 lean_dec_ref(x_98);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_107 = lean_ctor_get(x_95, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_95, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_109 = x_95;
} else {
 lean_dec_ref(x_95);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_111 = lean_ctor_get(x_92, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_113 = x_92;
} else {
 lean_dec_ref(x_92);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
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
x_1 = l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
x_2 = l_Lean_Meta_Closure_State_levelParams___default___closed__1;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
lean_inc(x_7);
x_15 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_22, 5);
lean_inc(x_25);
x_26 = l_Array_reverse___rarg(x_25);
x_27 = lean_ctor_get(x_22, 6);
lean_inc(x_27);
x_28 = l_Array_append___rarg(x_26, x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_22, 7);
lean_inc(x_29);
x_30 = l_Array_reverse___rarg(x_29);
lean_inc(x_30);
x_31 = l_Lean_Meta_Closure_mkForall(x_30, x_23);
lean_dec(x_23);
lean_inc(x_28);
x_32 = l_Lean_Meta_Closure_mkForall(x_28, x_31);
lean_dec(x_31);
x_33 = l_Lean_Meta_Closure_mkLambda(x_30, x_24);
lean_dec(x_24);
x_34 = l_Lean_Meta_Closure_mkLambda(x_28, x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_22, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 10);
lean_inc(x_37);
x_38 = l_Array_reverse___rarg(x_37);
x_39 = lean_ctor_get(x_22, 9);
lean_inc(x_39);
lean_dec(x_22);
x_40 = l_Array_append___rarg(x_38, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_20, 0, x_41);
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_ctor_get(x_42, 5);
lean_inc(x_46);
x_47 = l_Array_reverse___rarg(x_46);
x_48 = lean_ctor_get(x_42, 6);
lean_inc(x_48);
x_49 = l_Array_append___rarg(x_47, x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_42, 7);
lean_inc(x_50);
x_51 = l_Array_reverse___rarg(x_50);
lean_inc(x_51);
x_52 = l_Lean_Meta_Closure_mkForall(x_51, x_44);
lean_dec(x_44);
lean_inc(x_49);
x_53 = l_Lean_Meta_Closure_mkForall(x_49, x_52);
lean_dec(x_52);
x_54 = l_Lean_Meta_Closure_mkLambda(x_51, x_45);
lean_dec(x_45);
x_55 = l_Lean_Meta_Closure_mkLambda(x_49, x_54);
lean_dec(x_54);
x_56 = lean_ctor_get(x_42, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 10);
lean_inc(x_58);
x_59 = l_Array_reverse___rarg(x_58);
x_60 = lean_ctor_get(x_42, 9);
lean_inc(x_60);
lean_dec(x_42);
x_61 = l_Array_append___rarg(x_59, x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_57);
lean_ctor_set(x_62, 4, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_43);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_13);
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
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
uint8_t l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_auxRecExt;
x_5 = l_Lean_TagDeclarationExtension_isTagged(x_4, x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_3);
x_6 = l_Lean_isRecCore(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_9 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_8, x_3);
lean_dec(x_3);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
else
{
uint8_t x_12; 
x_12 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_14 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_13, x_3);
lean_dec(x_3);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_inc(x_3);
x_17 = l_Lean_isRecCore(x_1, x_3);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = 0;
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_20 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_19, x_3);
lean_dec(x_3);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = 0;
return x_23;
}
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("code generator does not support recursor '");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' yet, consider using 'match ... with' and/or structural recursion");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_36 = lean_ctor_get(x_10, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_1);
x_38 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_38, 0, x_1);
x_39 = 8192;
x_40 = l_Lean_Expr_FindImpl_initCache;
x_41 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_38, x_39, x_37, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
x_12 = x_8;
goto block_35;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 4)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_49, x_4, x_5, x_6, x_7, x_8);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_dec(x_43);
x_12 = x_8;
goto block_35;
}
}
block_35:
{
lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = 8192;
x_16 = l_Lean_Expr_FindImpl_initCache;
x_17 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_14, x_15, x_13, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_2 = x_19;
x_3 = x_11;
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 4)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_27, x_4, x_5, x_6, x_7, x_12);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_21);
x_33 = lean_box(0);
x_2 = x_33;
x_3 = x_11;
x_8 = x_12;
goto _start;
}
}
}
}
}
}
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = 8192;
x_15 = l_Lean_Expr_FindImpl_initCache;
x_16 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_13, x_14, x_12, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_2 = x_18;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_26, x_4, x_5, x_6, x_7, x_8);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_20);
x_32 = lean_box(0);
x_2 = x_32;
x_3 = x_11;
goto _start;
}
}
}
}
}
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_22, 0, x_1);
x_23 = 8192;
x_24 = l_Lean_Expr_FindImpl_initCache;
x_25 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_22, x_23, x_21, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 2);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_box(0);
lean_inc(x_1);
x_29 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7(x_1, x_28, x_27, x_4, x_5, x_6, x_7, x_8);
x_12 = x_29;
goto block_20;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_36, x_4, x_5, x_6, x_7, x_8);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
x_12 = x_37;
goto block_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_12 = x_41;
goto block_20;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_42 = lean_ctor_get(x_10, 2);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_box(0);
lean_inc(x_1);
x_44 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7(x_1, x_43, x_42, x_4, x_5, x_6, x_7, x_8);
x_12 = x_44;
goto block_20;
}
}
block_20:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_2 = x_13;
x_3 = x_11;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = 8192;
x_14 = l_Lean_Expr_FindImpl_initCache;
x_15 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_12, x_13, x_11, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_25, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_1);
x_52 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_52, 0, x_1);
x_53 = 8192;
x_54 = l_Lean_Expr_FindImpl_initCache;
x_55 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_52, x_53, x_32, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
x_33 = x_8;
goto block_51;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 4)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_31);
lean_dec(x_1);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_63, x_4, x_5, x_6, x_7, x_8);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_dec(x_57);
x_33 = x_8;
goto block_51;
}
}
block_51:
{
lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_34, 0, x_1);
x_35 = 8192;
x_36 = l_Lean_Expr_FindImpl_initCache;
x_37 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_34, x_35, x_31, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
if (lean_obj_tag(x_41) == 4)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_47, x_4, x_5, x_6, x_7, x_33);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_33);
return x_50;
}
}
}
}
case 2:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_92; size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_3);
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
lean_dec(x_2);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 2);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_1);
x_92 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_92, 0, x_1);
x_93 = 8192;
x_94 = l_Lean_Expr_FindImpl_initCache;
x_95 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_92, x_93, x_72, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
x_73 = x_8;
goto block_91;
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
if (lean_obj_tag(x_97) == 4)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_71);
lean_dec(x_1);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_103, x_4, x_5, x_6, x_7, x_8);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
return x_104;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_104);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
else
{
lean_dec(x_97);
x_73 = x_8;
goto block_91;
}
}
block_91:
{
lean_object* x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_74, 0, x_1);
x_75 = 8192;
x_76 = l_Lean_Expr_FindImpl_initCache;
x_77 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_74, x_75, x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
if (lean_obj_tag(x_81) == 4)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_87, x_4, x_5, x_6, x_7, x_73);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_81);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_73);
return x_90;
}
}
}
}
case 3:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_3);
x_109 = lean_ctor_get(x_2, 0);
lean_inc(x_109);
lean_dec(x_2);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 2);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_1);
x_132 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_132, 0, x_1);
x_133 = 8192;
x_134 = l_Lean_Expr_FindImpl_initCache;
x_135 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_132, x_133, x_112, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
x_113 = x_8;
goto block_131;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
if (lean_obj_tag(x_137) == 4)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_111);
lean_dec(x_1);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_143, x_4, x_5, x_6, x_7, x_8);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_dec(x_137);
x_113 = x_8;
goto block_131;
}
}
block_131:
{
lean_object* x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed), 2, 1);
lean_closure_set(x_114, 0, x_1);
x_115 = 8192;
x_116 = l_Lean_Expr_FindImpl_initCache;
x_117 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_114, x_115, x_111, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec(x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
return x_120;
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec(x_118);
if (lean_obj_tag(x_121) == 4)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_127, x_4, x_5, x_6, x_7, x_113);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_121);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_113);
return x_130;
}
}
}
}
case 4:
{
lean_object* x_149; 
lean_dec(x_1);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_3);
lean_ctor_set(x_149, 1, x_8);
return x_149;
}
case 5:
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_2, 0);
lean_inc(x_150);
lean_dec(x_2);
x_151 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6(x_1, x_3, x_150, x_4, x_5, x_6, x_7, x_8);
return x_151;
}
default: 
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_2, 2);
lean_inc(x_152);
lean_dec(x_2);
x_153 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8(x_1, x_3, x_152, x_4, x_5, x_6, x_7, x_8);
return x_153;
}
}
}
}
lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = lean_box(0);
x_12 = l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5(x_10, x_1, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
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
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 11)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_18, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_4);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(x_13, x_2, x_3, x_4, x_5, x_9);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_25, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_26;
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
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_8);
x_11 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
if (x_4 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_2, x_3, x_13, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_8);
x_16 = l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(x_1, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkAuxDefinition___lambda__1(x_2, x_3, x_17, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_8);
lean_dec(x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint32_t x_27; uint32_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_array_to_list(lean_box(0), x_20);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_22);
lean_inc(x_4);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_ctor_get(x_14, 2);
lean_inc(x_24);
lean_inc(x_24);
lean_inc(x_19);
x_25 = l_Lean_getMaxHeight(x_19, x_24);
x_26 = lean_unbox_uint32(x_25);
lean_dec(x_25);
x_27 = 1;
x_28 = x_26 + x_27;
x_29 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_29, 0, x_28);
lean_inc(x_22);
lean_inc(x_19);
x_30 = l_Lean_Environment_hasUnsafe(x_19, x_22);
x_31 = lean_st_ref_get(x_11, x_18);
if (x_30 == 0)
{
uint8_t x_67; 
lean_inc(x_24);
x_67 = l_Lean_Environment_hasUnsafe(x_19, x_24);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = 1;
x_32 = x_68;
goto block_66;
}
else
{
uint8_t x_69; 
x_69 = 0;
x_32 = x_69;
goto block_66;
}
}
else
{
uint8_t x_70; 
lean_dec(x_19);
x_70 = 0;
x_32 = x_70;
goto block_66;
}
block_66:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_24);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_56 = lean_ctor_get(x_31, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*1);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
lean_dec(x_31);
x_60 = 0;
x_35 = x_60;
x_36 = x_59;
goto block_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_31, 1);
lean_inc(x_61);
lean_dec(x_31);
lean_inc(x_6);
x_62 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_6, x_8, x_9, x_10, x_11, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_35 = x_65;
x_36 = x_64;
goto block_55;
}
block_55:
{
if (x_35 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_6);
x_37 = lean_box(0);
x_38 = l_Lean_Meta_mkAuxDefinition___lambda__2(x_34, x_14, x_4, x_5, x_37, x_8, x_9, x_10, x_11, x_36);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_4);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_4);
x_40 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_22);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_24);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
x_51 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_6, x_50, x_8, x_9, x_10, x_11, x_36);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_mkAuxDefinition___lambda__2(x_34, x_14, x_4, x_5, x_52, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_52);
return x_54;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
return x_13;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_13, 0);
x_73 = lean_ctor_get(x_13, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_13);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkAuxDefinition___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("debug");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxDefinition___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkAuxDefinition___closed__2;
x_2 = l_Lean_Meta_mkAuxDefinition___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_11 = l_Lean_Meta_mkAuxDefinition___closed__4;
x_33 = lean_st_ref_get(x_9, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = 0;
x_12 = x_38;
x_13 = x_37;
goto block_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_11, x_6, x_7, x_8, x_9, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_12 = x_43;
x_13 = x_42;
goto block_32;
}
block_32:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_mkAuxDefinition___lambda__3(x_2, x_3, x_4, x_1, x_5, x_11, x_14, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_1);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_2);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_3);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_3);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
x_28 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_11, x_27, x_6, x_7, x_8, x_9, x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_mkAuxDefinition___lambda__3(x_2, x_3, x_4, x_1, x_5, x_11, x_29, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_29);
return x_31;
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
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkAuxDefinition___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_mkAuxDefinition___lambda__3(x_1, x_2, x_13, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
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
l_Lean_Meta_Closure_State_levelParams___default___closed__1 = _init_l_Lean_Meta_Closure_State_levelParams___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_State_levelParams___default___closed__1);
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
l_Lean_Meta_Closure_mkNewLevelParam___closed__1 = _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___closed__1);
l_Lean_Meta_Closure_mkNewLevelParam___closed__2 = _init_l_Lean_Meta_Closure_mkNewLevelParam___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkNewLevelParam___closed__2);
l_Lean_Meta_Closure_collectLevelAux___closed__1 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__1);
l_Lean_Meta_Closure_collectLevelAux___closed__2 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__2);
l_Lean_Meta_Closure_collectLevelAux___closed__3 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__3);
l_Lean_Meta_Closure_collectLevelAux___closed__4 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__4();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__4);
l_Lean_Meta_Closure_collectLevelAux___closed__5 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__5();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__5);
l_Lean_Meta_Closure_collectLevelAux___closed__6 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__6();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__6);
l_Lean_Meta_Closure_collectLevelAux___closed__7 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__7();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__7);
l_Lean_Meta_Closure_collectLevelAux___closed__8 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__8();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__8);
l_Lean_Meta_Closure_collectLevelAux___closed__9 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__9();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__9);
l_Lean_Meta_Closure_collectLevelAux___closed__10 = _init_l_Lean_Meta_Closure_collectLevelAux___closed__10();
lean_mark_persistent(l_Lean_Meta_Closure_collectLevelAux___closed__10);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1);
l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2 = _init_l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2);
l_Lean_Meta_Closure_collectExprAux___closed__1 = _init_l_Lean_Meta_Closure_collectExprAux___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__1);
l_Lean_Meta_Closure_collectExprAux___closed__2 = _init_l_Lean_Meta_Closure_collectExprAux___closed__2();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__2);
l_Lean_Meta_Closure_collectExprAux___closed__3 = _init_l_Lean_Meta_Closure_collectExprAux___closed__3();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__3);
l_Lean_Meta_Closure_collectExprAux___closed__4 = _init_l_Lean_Meta_Closure_collectExprAux___closed__4();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__4);
l_Lean_Meta_Closure_collectExprAux___closed__5 = _init_l_Lean_Meta_Closure_collectExprAux___closed__5();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__5);
l_Lean_Meta_Closure_collectExprAux___closed__6 = _init_l_Lean_Meta_Closure_collectExprAux___closed__6();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__6);
l_Lean_Meta_Closure_collectExprAux___closed__7 = _init_l_Lean_Meta_Closure_collectExprAux___closed__7();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__7);
l_Lean_Meta_Closure_collectExprAux___closed__8 = _init_l_Lean_Meta_Closure_collectExprAux___closed__8();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__8);
l_Lean_Meta_Closure_collectExprAux___closed__9 = _init_l_Lean_Meta_Closure_collectExprAux___closed__9();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__9);
l_Lean_Meta_Closure_collectExprAux___closed__10 = _init_l_Lean_Meta_Closure_collectExprAux___closed__10();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__10);
l_Lean_Meta_Closure_collectExprAux___closed__11 = _init_l_Lean_Meta_Closure_collectExprAux___closed__11();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__11);
l_Lean_Meta_Closure_collectExprAux___closed__12 = _init_l_Lean_Meta_Closure_collectExprAux___closed__12();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__12);
l_Lean_Meta_Closure_collectExprAux___closed__13 = _init_l_Lean_Meta_Closure_collectExprAux___closed__13();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__13);
l_Lean_Meta_Closure_collectExprAux___closed__14 = _init_l_Lean_Meta_Closure_collectExprAux___closed__14();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__14);
l_Lean_Meta_Closure_collectExprAux___closed__15 = _init_l_Lean_Meta_Closure_collectExprAux___closed__15();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__15);
l_Lean_Meta_Closure_collectExprAux___closed__16 = _init_l_Lean_Meta_Closure_collectExprAux___closed__16();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__16);
l_Lean_Meta_Closure_collectExprAux___closed__17 = _init_l_Lean_Meta_Closure_collectExprAux___closed__17();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__17);
l_Lean_Meta_Closure_collectExprAux___closed__18 = _init_l_Lean_Meta_Closure_collectExprAux___closed__18();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__18);
l_Lean_Meta_Closure_collectExprAux___closed__19 = _init_l_Lean_Meta_Closure_collectExprAux___closed__19();
lean_mark_persistent(l_Lean_Meta_Closure_collectExprAux___closed__19);
l_Lean_Meta_Closure_mkValueTypeClosure___closed__1 = _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1();
lean_mark_persistent(l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__1 = _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__1);
l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2 = _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2);
l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__3 = _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__3();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__3);
l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4 = _init_l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4);
l_Lean_Meta_mkAuxDefinition___lambda__3___closed__1 = _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___lambda__3___closed__1);
l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2 = _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2);
l_Lean_Meta_mkAuxDefinition___lambda__3___closed__3 = _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___lambda__3___closed__3);
l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4 = _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4);
l_Lean_Meta_mkAuxDefinition___lambda__3___closed__5 = _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___lambda__3___closed__5);
l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6 = _init_l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6);
l_Lean_Meta_mkAuxDefinition___closed__1 = _init_l_Lean_Meta_mkAuxDefinition___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___closed__1);
l_Lean_Meta_mkAuxDefinition___closed__2 = _init_l_Lean_Meta_mkAuxDefinition___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___closed__2);
l_Lean_Meta_mkAuxDefinition___closed__3 = _init_l_Lean_Meta_mkAuxDefinition___closed__3();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___closed__3);
l_Lean_Meta_mkAuxDefinition___closed__4 = _init_l_Lean_Meta_mkAuxDefinition___closed__4();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
