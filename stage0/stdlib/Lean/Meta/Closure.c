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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__5;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__18;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__14;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__2;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__2;
extern lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDecls___default;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__7;
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_instBEqLevel;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprFVarArgs___default;
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextLevelIdx___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_nextExprIdx___default;
uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelArgs___default;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__3;
extern lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1___boxed(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__1;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__2;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__8;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__4;
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_instHashableLevel;
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__3;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLocalDeclsForMVars___default;
LEAN_EXPORT lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__6;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_levelParams___default___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedLevel___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__1;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__17;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__8;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__4;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__6;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_exprMVarArgs___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkNewLevelParam___closed__2;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_levelParams___default;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__7;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__10;
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__1;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__3;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__9;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_toProcess___default;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_visitedExpr___default;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__1;
static lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___closed__3;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement;
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__19;
static lean_object* l_Lean_Meta_Closure_collectLevelAux___closed__6;
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__4;
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__12;
static lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_State_visitedExpr___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_State_newLetDecls___default;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__4;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Closure_collectExprAux___closed__10;
extern lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
lean_object* lean_expr_update_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxDefinition___closed__2;
lean_object* lean_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedLevel___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Meta_Closure_State_visitedLevel___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Closure_State_visitedExpr___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_104; 
x_104 = l_Lean_Level_hasMVar(x_2);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Level_hasParam(x_2);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_2);
lean_ctor_set(x_106, 1, x_9);
return x_106;
}
else
{
lean_object* x_107; 
x_107 = lean_box(0);
x_10 = x_107;
goto block_103;
}
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_10 = x_108;
goto block_103;
}
block_103:
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
lean_inc(x_2);
x_18 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_17, x_2);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Lean_Level_instBEqLevel;
x_31 = l_Lean_Level_instHashableLevel;
lean_inc(x_21);
x_32 = l_Std_HashMap_insert___rarg(x_30, x_31, x_29, x_2, x_21);
lean_ctor_set(x_26, 0, x_32);
x_33 = lean_st_ref_set(x_4, x_26, x_27);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_21);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
x_40 = lean_ctor_get(x_26, 2);
x_41 = lean_ctor_get(x_26, 3);
x_42 = lean_ctor_get(x_26, 4);
x_43 = lean_ctor_get(x_26, 5);
x_44 = lean_ctor_get(x_26, 6);
x_45 = lean_ctor_get(x_26, 7);
x_46 = lean_ctor_get(x_26, 8);
x_47 = lean_ctor_get(x_26, 9);
x_48 = lean_ctor_get(x_26, 10);
x_49 = lean_ctor_get(x_26, 11);
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
lean_dec(x_26);
x_50 = l_Lean_Level_instBEqLevel;
x_51 = l_Lean_Level_instHashableLevel;
lean_inc(x_21);
x_52 = l_Std_HashMap_insert___rarg(x_50, x_51, x_38, x_2, x_21);
x_53 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_39);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_41);
lean_ctor_set(x_53, 4, x_42);
lean_ctor_set(x_53, 5, x_43);
lean_ctor_set(x_53, 6, x_44);
lean_ctor_set(x_53, 7, x_45);
lean_ctor_set(x_53, 8, x_46);
lean_ctor_set(x_53, 9, x_47);
lean_ctor_set(x_53, 10, x_48);
lean_ctor_set(x_53, 11, x_49);
x_54 = lean_st_ref_set(x_4, x_53, x_27);
lean_dec(x_4);
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
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_20);
if (x_58 == 0)
{
return x_20;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_20, 0);
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_20);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_2);
x_66 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_65, x_2);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_68 = lean_apply_8(x_1, x_2, x_67, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_get(x_8, x_70);
lean_dec(x_8);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_take(x_4, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_74, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 8);
lean_inc(x_84);
x_85 = lean_ctor_get(x_74, 9);
lean_inc(x_85);
x_86 = lean_ctor_get(x_74, 10);
lean_inc(x_86);
x_87 = lean_ctor_get(x_74, 11);
lean_inc(x_87);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 lean_ctor_release(x_74, 6);
 lean_ctor_release(x_74, 7);
 lean_ctor_release(x_74, 8);
 lean_ctor_release(x_74, 9);
 lean_ctor_release(x_74, 10);
 lean_ctor_release(x_74, 11);
 x_88 = x_74;
} else {
 lean_dec_ref(x_74);
 x_88 = lean_box(0);
}
x_89 = l_Lean_Level_instBEqLevel;
x_90 = l_Lean_Level_instHashableLevel;
lean_inc(x_69);
x_91 = l_Std_HashMap_insert___rarg(x_89, x_90, x_76, x_2, x_69);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 12, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_77);
lean_ctor_set(x_92, 2, x_78);
lean_ctor_set(x_92, 3, x_79);
lean_ctor_set(x_92, 4, x_80);
lean_ctor_set(x_92, 5, x_81);
lean_ctor_set(x_92, 6, x_82);
lean_ctor_set(x_92, 7, x_83);
lean_ctor_set(x_92, 8, x_84);
lean_ctor_set(x_92, 9, x_85);
lean_ctor_set(x_92, 10, x_86);
lean_ctor_set(x_92, 11, x_87);
x_93 = lean_st_ref_set(x_4, x_92, x_75);
lean_dec(x_4);
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
lean_ctor_set(x_96, 0, x_69);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_97 = lean_ctor_get(x_68, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_68, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_99 = x_68;
} else {
 lean_dec_ref(x_68);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_66, 0);
lean_inc(x_101);
lean_dec(x_66);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_64);
return x_102;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_visitLevel(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_104; 
x_104 = l_Lean_Expr_hasLevelParam(x_2);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Expr_hasFVar(x_2);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_hasMVar(x_2);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_2);
lean_ctor_set(x_107, 1, x_9);
return x_107;
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_10 = x_108;
goto block_103;
}
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_10 = x_109;
goto block_103;
}
}
else
{
lean_object* x_110; 
x_110 = lean_box(0);
x_10 = x_110;
goto block_103;
}
block_103:
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
lean_inc(x_2);
x_18 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_17, x_2);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_31 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_21);
x_32 = l_Std_HashMap_insert___rarg(x_30, x_31, x_29, x_2, x_21);
lean_ctor_set(x_26, 1, x_32);
x_33 = lean_st_ref_set(x_4, x_26, x_27);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_21);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
x_40 = lean_ctor_get(x_26, 2);
x_41 = lean_ctor_get(x_26, 3);
x_42 = lean_ctor_get(x_26, 4);
x_43 = lean_ctor_get(x_26, 5);
x_44 = lean_ctor_get(x_26, 6);
x_45 = lean_ctor_get(x_26, 7);
x_46 = lean_ctor_get(x_26, 8);
x_47 = lean_ctor_get(x_26, 9);
x_48 = lean_ctor_get(x_26, 10);
x_49 = lean_ctor_get(x_26, 11);
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
lean_dec(x_26);
x_50 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_51 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_21);
x_52 = l_Std_HashMap_insert___rarg(x_50, x_51, x_39, x_2, x_21);
x_53 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_41);
lean_ctor_set(x_53, 4, x_42);
lean_ctor_set(x_53, 5, x_43);
lean_ctor_set(x_53, 6, x_44);
lean_ctor_set(x_53, 7, x_45);
lean_ctor_set(x_53, 8, x_46);
lean_ctor_set(x_53, 9, x_47);
lean_ctor_set(x_53, 10, x_48);
lean_ctor_set(x_53, 11, x_49);
x_54 = lean_st_ref_set(x_4, x_53, x_27);
lean_dec(x_4);
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
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_20);
if (x_58 == 0)
{
return x_20;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_20, 0);
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_20);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_2);
x_66 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_65, x_2);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_68 = lean_apply_8(x_1, x_2, x_67, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_get(x_8, x_70);
lean_dec(x_8);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_take(x_4, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_74, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 8);
lean_inc(x_84);
x_85 = lean_ctor_get(x_74, 9);
lean_inc(x_85);
x_86 = lean_ctor_get(x_74, 10);
lean_inc(x_86);
x_87 = lean_ctor_get(x_74, 11);
lean_inc(x_87);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 lean_ctor_release(x_74, 6);
 lean_ctor_release(x_74, 7);
 lean_ctor_release(x_74, 8);
 lean_ctor_release(x_74, 9);
 lean_ctor_release(x_74, 10);
 lean_ctor_release(x_74, 11);
 x_88 = x_74;
} else {
 lean_dec_ref(x_74);
 x_88 = lean_box(0);
}
x_89 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_90 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_69);
x_91 = l_Std_HashMap_insert___rarg(x_89, x_90, x_77, x_2, x_69);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 12, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_78);
lean_ctor_set(x_92, 3, x_79);
lean_ctor_set(x_92, 4, x_80);
lean_ctor_set(x_92, 5, x_81);
lean_ctor_set(x_92, 6, x_82);
lean_ctor_set(x_92, 7, x_83);
lean_ctor_set(x_92, 8, x_84);
lean_ctor_set(x_92, 9, x_85);
lean_ctor_set(x_92, 10, x_86);
lean_ctor_set(x_92, 11, x_87);
x_93 = lean_st_ref_set(x_4, x_92, x_75);
lean_dec(x_4);
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
lean_ctor_set(x_96, 0, x_69);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_97 = lean_ctor_get(x_68, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_68, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_99 = x_68;
} else {
 lean_dec_ref(x_68);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_66, 0);
lean_inc(x_101);
lean_dec(x_66);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_64);
return x_102;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_3 = lean_unsigned_to_nat(508u);
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
x_3 = lean_unsigned_to_nat(517u);
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
x_3 = lean_unsigned_to_nat(526u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Meta_Closure_collectLevelAux___closed__9;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; uint8_t x_68; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_68 = l_Lean_Level_hasMVar(x_24);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = l_Lean_Level_hasParam(x_24);
if (x_69 == 0)
{
x_9 = x_24;
x_10 = x_8;
goto block_22;
}
else
{
lean_object* x_70; 
x_70 = lean_box(0);
x_25 = x_70;
goto block_67;
}
}
else
{
lean_object* x_71; 
x_71 = lean_box(0);
x_25 = x_71;
goto block_67;
}
block_67:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
x_26 = lean_st_ref_get(x_7, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_24);
x_32 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_31, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_inc(x_24);
x_33 = l_Lean_Meta_Closure_collectLevelAux(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_7, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_take(x_3, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = l_Lean_Level_instBEqLevel;
x_44 = l_Lean_Level_instHashableLevel;
lean_inc(x_34);
x_45 = l_Std_HashMap_insert___rarg(x_43, x_44, x_42, x_24, x_34);
lean_ctor_set(x_39, 0, x_45);
x_46 = lean_st_ref_set(x_3, x_39, x_40);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_9 = x_34;
x_10 = x_47;
goto block_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
x_50 = lean_ctor_get(x_39, 2);
x_51 = lean_ctor_get(x_39, 3);
x_52 = lean_ctor_get(x_39, 4);
x_53 = lean_ctor_get(x_39, 5);
x_54 = lean_ctor_get(x_39, 6);
x_55 = lean_ctor_get(x_39, 7);
x_56 = lean_ctor_get(x_39, 8);
x_57 = lean_ctor_get(x_39, 9);
x_58 = lean_ctor_get(x_39, 10);
x_59 = lean_ctor_get(x_39, 11);
lean_inc(x_59);
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
lean_dec(x_39);
x_60 = l_Lean_Level_instBEqLevel;
x_61 = l_Lean_Level_instHashableLevel;
lean_inc(x_34);
x_62 = l_Std_HashMap_insert___rarg(x_60, x_61, x_48, x_24, x_34);
x_63 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_49);
lean_ctor_set(x_63, 2, x_50);
lean_ctor_set(x_63, 3, x_51);
lean_ctor_set(x_63, 4, x_52);
lean_ctor_set(x_63, 5, x_53);
lean_ctor_set(x_63, 6, x_54);
lean_ctor_set(x_63, 7, x_55);
lean_ctor_set(x_63, 8, x_56);
lean_ctor_set(x_63, 9, x_57);
lean_ctor_set(x_63, 10, x_58);
lean_ctor_set(x_63, 11, x_59);
x_64 = lean_st_ref_set(x_3, x_63, x_40);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_9 = x_34;
x_10 = x_65;
goto block_22;
}
}
else
{
lean_object* x_66; 
lean_dec(x_24);
x_66 = lean_ctor_get(x_32, 0);
lean_inc(x_66);
lean_dec(x_32);
x_9 = x_66;
x_10 = x_30;
goto block_22;
}
}
}
case 2:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_139; uint8_t x_182; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_182 = l_Lean_Level_hasMVar(x_72);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = l_Lean_Level_hasParam(x_72);
if (x_183 == 0)
{
x_74 = x_72;
x_75 = x_8;
goto block_138;
}
else
{
lean_object* x_184; 
x_184 = lean_box(0);
x_139 = x_184;
goto block_181;
}
}
else
{
lean_object* x_185; 
x_185 = lean_box(0);
x_139 = x_185;
goto block_181;
}
block_138:
{
lean_object* x_76; lean_object* x_77; lean_object* x_91; uint8_t x_134; 
x_134 = l_Lean_Level_hasMVar(x_73);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = l_Lean_Level_hasParam(x_73);
if (x_135 == 0)
{
x_76 = x_73;
x_77 = x_75;
goto block_90;
}
else
{
lean_object* x_136; 
x_136 = lean_box(0);
x_91 = x_136;
goto block_133;
}
}
else
{
lean_object* x_137; 
x_137 = lean_box(0);
x_91 = x_137;
goto block_133;
}
block_90:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_level_update_max(x_1, x_74, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_1, 0);
x_82 = lean_ctor_get(x_1, 1);
x_83 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_1);
x_84 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set_uint64(x_84, sizeof(void*)*2, x_83);
x_85 = lean_level_update_max(x_84, x_74, x_76);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_1);
x_87 = l_Lean_Meta_Closure_collectLevelAux___closed__7;
x_88 = l_panic___at_Lean_Level_normalize___spec__1(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_77);
return x_89;
}
}
block_133:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_91);
x_92 = lean_st_ref_get(x_7, x_75);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_st_ref_get(x_3, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_73);
x_98 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_97, x_73);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_inc(x_73);
x_99 = l_Lean_Meta_Closure_collectLevelAux(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_96);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_st_ref_get(x_7, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_st_ref_take(x_3, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = l_Lean_Level_instBEqLevel;
x_110 = l_Lean_Level_instHashableLevel;
lean_inc(x_100);
x_111 = l_Std_HashMap_insert___rarg(x_109, x_110, x_108, x_73, x_100);
lean_ctor_set(x_105, 0, x_111);
x_112 = lean_st_ref_set(x_3, x_105, x_106);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_76 = x_100;
x_77 = x_113;
goto block_90;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_114 = lean_ctor_get(x_105, 0);
x_115 = lean_ctor_get(x_105, 1);
x_116 = lean_ctor_get(x_105, 2);
x_117 = lean_ctor_get(x_105, 3);
x_118 = lean_ctor_get(x_105, 4);
x_119 = lean_ctor_get(x_105, 5);
x_120 = lean_ctor_get(x_105, 6);
x_121 = lean_ctor_get(x_105, 7);
x_122 = lean_ctor_get(x_105, 8);
x_123 = lean_ctor_get(x_105, 9);
x_124 = lean_ctor_get(x_105, 10);
x_125 = lean_ctor_get(x_105, 11);
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
lean_dec(x_105);
x_126 = l_Lean_Level_instBEqLevel;
x_127 = l_Lean_Level_instHashableLevel;
lean_inc(x_100);
x_128 = l_Std_HashMap_insert___rarg(x_126, x_127, x_114, x_73, x_100);
x_129 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_115);
lean_ctor_set(x_129, 2, x_116);
lean_ctor_set(x_129, 3, x_117);
lean_ctor_set(x_129, 4, x_118);
lean_ctor_set(x_129, 5, x_119);
lean_ctor_set(x_129, 6, x_120);
lean_ctor_set(x_129, 7, x_121);
lean_ctor_set(x_129, 8, x_122);
lean_ctor_set(x_129, 9, x_123);
lean_ctor_set(x_129, 10, x_124);
lean_ctor_set(x_129, 11, x_125);
x_130 = lean_st_ref_set(x_3, x_129, x_106);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_76 = x_100;
x_77 = x_131;
goto block_90;
}
}
else
{
lean_object* x_132; 
lean_dec(x_73);
x_132 = lean_ctor_get(x_98, 0);
lean_inc(x_132);
lean_dec(x_98);
x_76 = x_132;
x_77 = x_96;
goto block_90;
}
}
}
block_181:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_139);
x_140 = lean_st_ref_get(x_7, x_8);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_get(x_3, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_72);
x_146 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_145, x_72);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_inc(x_72);
x_147 = l_Lean_Meta_Closure_collectLevelAux(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_144);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_st_ref_get(x_7, x_149);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_st_ref_take(x_3, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = !lean_is_exclusive(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_153, 0);
x_157 = l_Lean_Level_instBEqLevel;
x_158 = l_Lean_Level_instHashableLevel;
lean_inc(x_148);
x_159 = l_Std_HashMap_insert___rarg(x_157, x_158, x_156, x_72, x_148);
lean_ctor_set(x_153, 0, x_159);
x_160 = lean_st_ref_set(x_3, x_153, x_154);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_74 = x_148;
x_75 = x_161;
goto block_138;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_162 = lean_ctor_get(x_153, 0);
x_163 = lean_ctor_get(x_153, 1);
x_164 = lean_ctor_get(x_153, 2);
x_165 = lean_ctor_get(x_153, 3);
x_166 = lean_ctor_get(x_153, 4);
x_167 = lean_ctor_get(x_153, 5);
x_168 = lean_ctor_get(x_153, 6);
x_169 = lean_ctor_get(x_153, 7);
x_170 = lean_ctor_get(x_153, 8);
x_171 = lean_ctor_get(x_153, 9);
x_172 = lean_ctor_get(x_153, 10);
x_173 = lean_ctor_get(x_153, 11);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_153);
x_174 = l_Lean_Level_instBEqLevel;
x_175 = l_Lean_Level_instHashableLevel;
lean_inc(x_148);
x_176 = l_Std_HashMap_insert___rarg(x_174, x_175, x_162, x_72, x_148);
x_177 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_163);
lean_ctor_set(x_177, 2, x_164);
lean_ctor_set(x_177, 3, x_165);
lean_ctor_set(x_177, 4, x_166);
lean_ctor_set(x_177, 5, x_167);
lean_ctor_set(x_177, 6, x_168);
lean_ctor_set(x_177, 7, x_169);
lean_ctor_set(x_177, 8, x_170);
lean_ctor_set(x_177, 9, x_171);
lean_ctor_set(x_177, 10, x_172);
lean_ctor_set(x_177, 11, x_173);
x_178 = lean_st_ref_set(x_3, x_177, x_154);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_74 = x_148;
x_75 = x_179;
goto block_138;
}
}
else
{
lean_object* x_180; 
lean_dec(x_72);
x_180 = lean_ctor_get(x_146, 0);
lean_inc(x_180);
lean_dec(x_146);
x_74 = x_180;
x_75 = x_144;
goto block_138;
}
}
}
case 3:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_253; uint8_t x_296; 
x_186 = lean_ctor_get(x_1, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_1, 1);
lean_inc(x_187);
x_296 = l_Lean_Level_hasMVar(x_186);
if (x_296 == 0)
{
uint8_t x_297; 
x_297 = l_Lean_Level_hasParam(x_186);
if (x_297 == 0)
{
x_188 = x_186;
x_189 = x_8;
goto block_252;
}
else
{
lean_object* x_298; 
x_298 = lean_box(0);
x_253 = x_298;
goto block_295;
}
}
else
{
lean_object* x_299; 
x_299 = lean_box(0);
x_253 = x_299;
goto block_295;
}
block_252:
{
lean_object* x_190; lean_object* x_191; lean_object* x_205; uint8_t x_248; 
x_248 = l_Lean_Level_hasMVar(x_187);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Level_hasParam(x_187);
if (x_249 == 0)
{
x_190 = x_187;
x_191 = x_189;
goto block_204;
}
else
{
lean_object* x_250; 
x_250 = lean_box(0);
x_205 = x_250;
goto block_247;
}
}
else
{
lean_object* x_251; 
x_251 = lean_box(0);
x_205 = x_251;
goto block_247;
}
block_204:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_1);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_level_update_imax(x_1, x_188, x_190);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; uint64_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_1, 0);
x_196 = lean_ctor_get(x_1, 1);
x_197 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_1);
x_198 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set_uint64(x_198, sizeof(void*)*2, x_197);
x_199 = lean_level_update_imax(x_198, x_188, x_190);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_191);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_1);
x_201 = l_Lean_Meta_Closure_collectLevelAux___closed__10;
x_202 = l_panic___at_Lean_Level_normalize___spec__1(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_191);
return x_203;
}
}
block_247:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_205);
x_206 = lean_st_ref_get(x_7, x_189);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_st_ref_get(x_3, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
lean_dec(x_209);
lean_inc(x_187);
x_212 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_211, x_187);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
lean_inc(x_187);
x_213 = l_Lean_Meta_Closure_collectLevelAux(x_187, x_2, x_3, x_4, x_5, x_6, x_7, x_210);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_st_ref_get(x_7, x_215);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_st_ref_take(x_3, x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = !lean_is_exclusive(x_219);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_219, 0);
x_223 = l_Lean_Level_instBEqLevel;
x_224 = l_Lean_Level_instHashableLevel;
lean_inc(x_214);
x_225 = l_Std_HashMap_insert___rarg(x_223, x_224, x_222, x_187, x_214);
lean_ctor_set(x_219, 0, x_225);
x_226 = lean_st_ref_set(x_3, x_219, x_220);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_190 = x_214;
x_191 = x_227;
goto block_204;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_228 = lean_ctor_get(x_219, 0);
x_229 = lean_ctor_get(x_219, 1);
x_230 = lean_ctor_get(x_219, 2);
x_231 = lean_ctor_get(x_219, 3);
x_232 = lean_ctor_get(x_219, 4);
x_233 = lean_ctor_get(x_219, 5);
x_234 = lean_ctor_get(x_219, 6);
x_235 = lean_ctor_get(x_219, 7);
x_236 = lean_ctor_get(x_219, 8);
x_237 = lean_ctor_get(x_219, 9);
x_238 = lean_ctor_get(x_219, 10);
x_239 = lean_ctor_get(x_219, 11);
lean_inc(x_239);
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
lean_dec(x_219);
x_240 = l_Lean_Level_instBEqLevel;
x_241 = l_Lean_Level_instHashableLevel;
lean_inc(x_214);
x_242 = l_Std_HashMap_insert___rarg(x_240, x_241, x_228, x_187, x_214);
x_243 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_229);
lean_ctor_set(x_243, 2, x_230);
lean_ctor_set(x_243, 3, x_231);
lean_ctor_set(x_243, 4, x_232);
lean_ctor_set(x_243, 5, x_233);
lean_ctor_set(x_243, 6, x_234);
lean_ctor_set(x_243, 7, x_235);
lean_ctor_set(x_243, 8, x_236);
lean_ctor_set(x_243, 9, x_237);
lean_ctor_set(x_243, 10, x_238);
lean_ctor_set(x_243, 11, x_239);
x_244 = lean_st_ref_set(x_3, x_243, x_220);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_190 = x_214;
x_191 = x_245;
goto block_204;
}
}
else
{
lean_object* x_246; 
lean_dec(x_187);
x_246 = lean_ctor_get(x_212, 0);
lean_inc(x_246);
lean_dec(x_212);
x_190 = x_246;
x_191 = x_210;
goto block_204;
}
}
}
block_295:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_253);
x_254 = lean_st_ref_get(x_7, x_8);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_st_ref_get(x_3, x_255);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
lean_dec(x_257);
lean_inc(x_186);
x_260 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_259, x_186);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_inc(x_186);
x_261 = l_Lean_Meta_Closure_collectLevelAux(x_186, x_2, x_3, x_4, x_5, x_6, x_7, x_258);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_st_ref_get(x_7, x_263);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = lean_st_ref_take(x_3, x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = !lean_is_exclusive(x_267);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_270 = lean_ctor_get(x_267, 0);
x_271 = l_Lean_Level_instBEqLevel;
x_272 = l_Lean_Level_instHashableLevel;
lean_inc(x_262);
x_273 = l_Std_HashMap_insert___rarg(x_271, x_272, x_270, x_186, x_262);
lean_ctor_set(x_267, 0, x_273);
x_274 = lean_st_ref_set(x_3, x_267, x_268);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_188 = x_262;
x_189 = x_275;
goto block_252;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_276 = lean_ctor_get(x_267, 0);
x_277 = lean_ctor_get(x_267, 1);
x_278 = lean_ctor_get(x_267, 2);
x_279 = lean_ctor_get(x_267, 3);
x_280 = lean_ctor_get(x_267, 4);
x_281 = lean_ctor_get(x_267, 5);
x_282 = lean_ctor_get(x_267, 6);
x_283 = lean_ctor_get(x_267, 7);
x_284 = lean_ctor_get(x_267, 8);
x_285 = lean_ctor_get(x_267, 9);
x_286 = lean_ctor_get(x_267, 10);
x_287 = lean_ctor_get(x_267, 11);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_267);
x_288 = l_Lean_Level_instBEqLevel;
x_289 = l_Lean_Level_instHashableLevel;
lean_inc(x_262);
x_290 = l_Std_HashMap_insert___rarg(x_288, x_289, x_276, x_186, x_262);
x_291 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_277);
lean_ctor_set(x_291, 2, x_278);
lean_ctor_set(x_291, 3, x_279);
lean_ctor_set(x_291, 4, x_280);
lean_ctor_set(x_291, 5, x_281);
lean_ctor_set(x_291, 6, x_282);
lean_ctor_set(x_291, 7, x_283);
lean_ctor_set(x_291, 8, x_284);
lean_ctor_set(x_291, 9, x_285);
lean_ctor_set(x_291, 10, x_286);
lean_ctor_set(x_291, 11, x_287);
x_292 = lean_st_ref_set(x_3, x_291, x_268);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_188 = x_262;
x_189 = x_293;
goto block_252;
}
}
else
{
lean_object* x_294; 
lean_dec(x_186);
x_294 = lean_ctor_get(x_260, 0);
lean_inc(x_294);
lean_dec(x_260);
x_188 = x_294;
x_189 = x_258;
goto block_252;
}
}
}
default: 
{
lean_object* x_300; 
x_300 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_300;
}
}
block_22:
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_1);
x_19 = l_Lean_Meta_Closure_collectLevelAux___closed__4;
x_20 = l_panic___at_Lean_Level_normalize___spec__1(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_93; 
x_93 = l_Lean_Level_hasMVar(x_1);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Level_hasParam(x_1);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_8);
return x_95;
}
else
{
lean_object* x_96; 
x_96 = lean_box(0);
x_9 = x_96;
goto block_92;
}
}
else
{
lean_object* x_97; 
x_97 = lean_box(0);
x_9 = x_97;
goto block_92;
}
block_92:
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
lean_inc(x_1);
x_17 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_16, x_1);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = l_Lean_Level_instBEqLevel;
x_29 = l_Lean_Level_instHashableLevel;
lean_inc(x_19);
x_30 = l_Std_HashMap_insert___rarg(x_28, x_29, x_27, x_1, x_19);
lean_ctor_set(x_24, 0, x_30);
x_31 = lean_st_ref_set(x_3, x_24, x_25);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_19);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_24, 2);
x_39 = lean_ctor_get(x_24, 3);
x_40 = lean_ctor_get(x_24, 4);
x_41 = lean_ctor_get(x_24, 5);
x_42 = lean_ctor_get(x_24, 6);
x_43 = lean_ctor_get(x_24, 7);
x_44 = lean_ctor_get(x_24, 8);
x_45 = lean_ctor_get(x_24, 9);
x_46 = lean_ctor_get(x_24, 10);
x_47 = lean_ctor_get(x_24, 11);
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
lean_dec(x_24);
x_48 = l_Lean_Level_instBEqLevel;
x_49 = l_Lean_Level_instHashableLevel;
lean_inc(x_19);
x_50 = l_Std_HashMap_insert___rarg(x_48, x_49, x_36, x_1, x_19);
x_51 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
lean_ctor_set(x_51, 2, x_38);
lean_ctor_set(x_51, 3, x_39);
lean_ctor_set(x_51, 4, x_40);
lean_ctor_set(x_51, 5, x_41);
lean_ctor_set(x_51, 6, x_42);
lean_ctor_set(x_51, 7, x_43);
lean_ctor_set(x_51, 8, x_44);
lean_ctor_set(x_51, 9, x_45);
lean_ctor_set(x_51, 10, x_46);
lean_ctor_set(x_51, 11, x_47);
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
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_19);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_1);
x_56 = lean_ctor_get(x_17, 0);
lean_inc(x_56);
lean_dec(x_17);
lean_ctor_set(x_12, 0, x_56);
return x_12;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_1);
x_60 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_Closure_visitLevel___spec__1(x_59, x_1);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_1);
x_61 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_7, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_3, x_65);
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
x_82 = l_Lean_Level_instBEqLevel;
x_83 = l_Lean_Level_instHashableLevel;
lean_inc(x_62);
x_84 = l_Std_HashMap_insert___rarg(x_82, x_83, x_69, x_1, x_62);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 12, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_70);
lean_ctor_set(x_85, 2, x_71);
lean_ctor_set(x_85, 3, x_72);
lean_ctor_set(x_85, 4, x_73);
lean_ctor_set(x_85, 5, x_74);
lean_ctor_set(x_85, 6, x_75);
lean_ctor_set(x_85, 7, x_76);
lean_ctor_set(x_85, 8, x_77);
lean_ctor_set(x_85, 9, x_78);
lean_ctor_set(x_85, 10, x_79);
lean_ctor_set(x_85, 11, x_80);
x_86 = lean_st_ref_set(x_3, x_85, x_68);
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
lean_ctor_set(x_89, 0, x_62);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_5, x_6, x_7, x_8);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkNextUserName___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Closure_mkNextUserName(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
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
x_28 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
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
x_3 = lean_unsigned_to_nat(956u);
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
x_3 = lean_unsigned_to_nat(961u);
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
x_3 = lean_unsigned_to_nat(921u);
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
x_3 = lean_unsigned_to_nat(989u);
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
x_3 = lean_unsigned_to_nat(975u);
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
x_3 = lean_unsigned_to_nat(998u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Meta_Closure_collectExprAux___closed__18;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_24; lean_object* x_25; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_40);
x_41 = l_Lean_Meta_getLocalDecl(x_40, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
if (x_2 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Meta_Closure_pushToProcess(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = l_Lean_mkFVar(x_44);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Lean_mkFVar(x_44);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_dec(x_41);
x_56 = l_Lean_LocalDecl_value_x3f(x_54);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_40);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Meta_Closure_pushToProcess(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = l_Lean_mkFVar(x_58);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = l_Lean_mkFVar(x_58);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_40);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
lean_dec(x_56);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_Meta_Closure_preprocess(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_165; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_165 = l_Lean_Expr_hasLevelParam(x_71);
if (x_165 == 0)
{
uint8_t x_166; 
x_166 = l_Lean_Expr_hasFVar(x_71);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = l_Lean_Expr_hasMVar(x_71);
if (x_167 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_69;
}
else
{
lean_object* x_168; 
lean_free_object(x_69);
x_168 = lean_box(0);
x_73 = x_168;
goto block_164;
}
}
else
{
lean_object* x_169; 
lean_free_object(x_69);
x_169 = lean_box(0);
x_73 = x_169;
goto block_164;
}
}
else
{
lean_object* x_170; 
lean_free_object(x_69);
x_170 = lean_box(0);
x_73 = x_170;
goto block_164;
}
block_164:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_73);
x_74 = lean_st_ref_get(x_7, x_72);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_st_ref_get(x_3, x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_71);
x_81 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_80, x_71);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_free_object(x_76);
lean_inc(x_7);
lean_inc(x_71);
x_82 = l_Lean_Meta_Closure_collectExprAux(x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_get(x_7, x_84);
lean_dec(x_7);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_st_ref_take(x_3, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_91 = lean_ctor_get(x_88, 1);
x_92 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_93 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_83);
x_94 = l_Std_HashMap_insert___rarg(x_92, x_93, x_91, x_71, x_83);
lean_ctor_set(x_88, 1, x_94);
x_95 = lean_st_ref_set(x_3, x_88, x_89);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_83);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_83);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_100 = lean_ctor_get(x_88, 0);
x_101 = lean_ctor_get(x_88, 1);
x_102 = lean_ctor_get(x_88, 2);
x_103 = lean_ctor_get(x_88, 3);
x_104 = lean_ctor_get(x_88, 4);
x_105 = lean_ctor_get(x_88, 5);
x_106 = lean_ctor_get(x_88, 6);
x_107 = lean_ctor_get(x_88, 7);
x_108 = lean_ctor_get(x_88, 8);
x_109 = lean_ctor_get(x_88, 9);
x_110 = lean_ctor_get(x_88, 10);
x_111 = lean_ctor_get(x_88, 11);
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
lean_dec(x_88);
x_112 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_113 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_83);
x_114 = l_Std_HashMap_insert___rarg(x_112, x_113, x_101, x_71, x_83);
x_115 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_102);
lean_ctor_set(x_115, 3, x_103);
lean_ctor_set(x_115, 4, x_104);
lean_ctor_set(x_115, 5, x_105);
lean_ctor_set(x_115, 6, x_106);
lean_ctor_set(x_115, 7, x_107);
lean_ctor_set(x_115, 8, x_108);
lean_ctor_set(x_115, 9, x_109);
lean_ctor_set(x_115, 10, x_110);
lean_ctor_set(x_115, 11, x_111);
x_116 = lean_st_ref_set(x_3, x_115, x_89);
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
lean_ctor_set(x_119, 0, x_83);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_71);
lean_dec(x_7);
x_120 = !lean_is_exclusive(x_82);
if (x_120 == 0)
{
return x_82;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_82, 0);
x_122 = lean_ctor_get(x_82, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_82);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; 
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_124 = lean_ctor_get(x_81, 0);
lean_inc(x_124);
lean_dec(x_81);
lean_ctor_set(x_76, 0, x_124);
return x_76;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_76, 0);
x_126 = lean_ctor_get(x_76, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_76);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_71);
x_128 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_127, x_71);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_inc(x_7);
lean_inc(x_71);
x_129 = l_Lean_Meta_Closure_collectExprAux(x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_126);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_st_ref_get(x_7, x_131);
lean_dec(x_7);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_take(x_3, x_133);
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
x_150 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_151 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_130);
x_152 = l_Std_HashMap_insert___rarg(x_150, x_151, x_138, x_71, x_130);
if (lean_is_scalar(x_149)) {
 x_153 = lean_alloc_ctor(0, 12, 0);
} else {
 x_153 = x_149;
}
lean_ctor_set(x_153, 0, x_137);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_139);
lean_ctor_set(x_153, 3, x_140);
lean_ctor_set(x_153, 4, x_141);
lean_ctor_set(x_153, 5, x_142);
lean_ctor_set(x_153, 6, x_143);
lean_ctor_set(x_153, 7, x_144);
lean_ctor_set(x_153, 8, x_145);
lean_ctor_set(x_153, 9, x_146);
lean_ctor_set(x_153, 10, x_147);
lean_ctor_set(x_153, 11, x_148);
x_154 = lean_st_ref_set(x_3, x_153, x_136);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_130);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_71);
lean_dec(x_7);
x_158 = lean_ctor_get(x_129, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_129, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_160 = x_129;
} else {
 lean_dec_ref(x_129);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_162 = lean_ctor_get(x_128, 0);
lean_inc(x_162);
lean_dec(x_128);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_126);
return x_163;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_218; 
x_171 = lean_ctor_get(x_69, 0);
x_172 = lean_ctor_get(x_69, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_69);
x_218 = l_Lean_Expr_hasLevelParam(x_171);
if (x_218 == 0)
{
uint8_t x_219; 
x_219 = l_Lean_Expr_hasFVar(x_171);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = l_Lean_Expr_hasMVar(x_171);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_171);
lean_ctor_set(x_221, 1, x_172);
return x_221;
}
else
{
lean_object* x_222; 
x_222 = lean_box(0);
x_173 = x_222;
goto block_217;
}
}
else
{
lean_object* x_223; 
x_223 = lean_box(0);
x_173 = x_223;
goto block_217;
}
}
else
{
lean_object* x_224; 
x_224 = lean_box(0);
x_173 = x_224;
goto block_217;
}
block_217:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_173);
x_174 = lean_st_ref_get(x_7, x_172);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_st_ref_get(x_3, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
lean_inc(x_171);
x_181 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_180, x_171);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
lean_dec(x_179);
lean_inc(x_7);
lean_inc(x_171);
x_182 = l_Lean_Meta_Closure_collectExprAux(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_178);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_st_ref_get(x_7, x_184);
lean_dec(x_7);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_st_ref_take(x_3, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 5);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 6);
lean_inc(x_196);
x_197 = lean_ctor_get(x_188, 7);
lean_inc(x_197);
x_198 = lean_ctor_get(x_188, 8);
lean_inc(x_198);
x_199 = lean_ctor_get(x_188, 9);
lean_inc(x_199);
x_200 = lean_ctor_get(x_188, 10);
lean_inc(x_200);
x_201 = lean_ctor_get(x_188, 11);
lean_inc(x_201);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 lean_ctor_release(x_188, 6);
 lean_ctor_release(x_188, 7);
 lean_ctor_release(x_188, 8);
 lean_ctor_release(x_188, 9);
 lean_ctor_release(x_188, 10);
 lean_ctor_release(x_188, 11);
 x_202 = x_188;
} else {
 lean_dec_ref(x_188);
 x_202 = lean_box(0);
}
x_203 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_204 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_183);
x_205 = l_Std_HashMap_insert___rarg(x_203, x_204, x_191, x_171, x_183);
if (lean_is_scalar(x_202)) {
 x_206 = lean_alloc_ctor(0, 12, 0);
} else {
 x_206 = x_202;
}
lean_ctor_set(x_206, 0, x_190);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_193);
lean_ctor_set(x_206, 4, x_194);
lean_ctor_set(x_206, 5, x_195);
lean_ctor_set(x_206, 6, x_196);
lean_ctor_set(x_206, 7, x_197);
lean_ctor_set(x_206, 8, x_198);
lean_ctor_set(x_206, 9, x_199);
lean_ctor_set(x_206, 10, x_200);
lean_ctor_set(x_206, 11, x_201);
x_207 = lean_st_ref_set(x_3, x_206, x_189);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_183);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_171);
lean_dec(x_7);
x_211 = lean_ctor_get(x_182, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_182, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_213 = x_182;
} else {
 lean_dec_ref(x_182);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_215 = lean_ctor_get(x_181, 0);
lean_inc(x_215);
lean_dec(x_181);
if (lean_is_scalar(x_179)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_179;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_178);
return x_216;
}
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_225 = !lean_is_exclusive(x_69);
if (x_225 == 0)
{
return x_69;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_69, 0);
x_227 = lean_ctor_get(x_69, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_69);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_229 = !lean_is_exclusive(x_41);
if (x_229 == 0)
{
return x_41;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_41, 0);
x_231 = lean_ctor_get(x_41, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_41);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
case 2:
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_1, 0);
lean_inc(x_233);
x_234 = l_Lean_Meta_getMVarDecl(x_233, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 2);
lean_inc(x_237);
lean_dec(x_235);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_238 = l_Lean_Meta_Closure_preprocess(x_237, x_2, x_3, x_4, x_5, x_6, x_7, x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_293; uint8_t x_340; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_340 = l_Lean_Expr_hasLevelParam(x_239);
if (x_340 == 0)
{
uint8_t x_341; 
x_341 = l_Lean_Expr_hasFVar(x_239);
if (x_341 == 0)
{
uint8_t x_342; 
x_342 = l_Lean_Expr_hasMVar(x_239);
if (x_342 == 0)
{
x_241 = x_239;
x_242 = x_240;
goto block_292;
}
else
{
lean_object* x_343; 
x_343 = lean_box(0);
x_293 = x_343;
goto block_339;
}
}
else
{
lean_object* x_344; 
x_344 = lean_box(0);
x_293 = x_344;
goto block_339;
}
}
else
{
lean_object* x_345; 
x_345 = lean_box(0);
x_293 = x_345;
goto block_339;
}
block_292:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_243 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = l_Lean_Meta_Closure_mkNextUserName___rarg(x_3, x_4, x_5, x_6, x_7, x_245);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_st_ref_get(x_7, x_248);
lean_dec(x_7);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_st_ref_take(x_3, x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = !lean_is_exclusive(x_252);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_255 = lean_ctor_get(x_252, 6);
x_256 = lean_ctor_get(x_252, 9);
x_257 = lean_unsigned_to_nat(0u);
x_258 = 0;
lean_inc(x_244);
x_259 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_244);
lean_ctor_set(x_259, 2, x_247);
lean_ctor_set(x_259, 3, x_241);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
x_260 = lean_array_push(x_255, x_259);
x_261 = lean_array_push(x_256, x_1);
lean_ctor_set(x_252, 9, x_261);
lean_ctor_set(x_252, 6, x_260);
x_262 = lean_st_ref_set(x_3, x_252, x_253);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 0);
lean_dec(x_264);
x_265 = l_Lean_mkFVar(x_244);
lean_ctor_set(x_262, 0, x_265);
return x_262;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
lean_dec(x_262);
x_267 = l_Lean_mkFVar(x_244);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_269 = lean_ctor_get(x_252, 0);
x_270 = lean_ctor_get(x_252, 1);
x_271 = lean_ctor_get(x_252, 2);
x_272 = lean_ctor_get(x_252, 3);
x_273 = lean_ctor_get(x_252, 4);
x_274 = lean_ctor_get(x_252, 5);
x_275 = lean_ctor_get(x_252, 6);
x_276 = lean_ctor_get(x_252, 7);
x_277 = lean_ctor_get(x_252, 8);
x_278 = lean_ctor_get(x_252, 9);
x_279 = lean_ctor_get(x_252, 10);
x_280 = lean_ctor_get(x_252, 11);
lean_inc(x_280);
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
lean_dec(x_252);
x_281 = lean_unsigned_to_nat(0u);
x_282 = 0;
lean_inc(x_244);
x_283 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_244);
lean_ctor_set(x_283, 2, x_247);
lean_ctor_set(x_283, 3, x_241);
lean_ctor_set_uint8(x_283, sizeof(void*)*4, x_282);
x_284 = lean_array_push(x_275, x_283);
x_285 = lean_array_push(x_278, x_1);
x_286 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_286, 0, x_269);
lean_ctor_set(x_286, 1, x_270);
lean_ctor_set(x_286, 2, x_271);
lean_ctor_set(x_286, 3, x_272);
lean_ctor_set(x_286, 4, x_273);
lean_ctor_set(x_286, 5, x_274);
lean_ctor_set(x_286, 6, x_284);
lean_ctor_set(x_286, 7, x_276);
lean_ctor_set(x_286, 8, x_277);
lean_ctor_set(x_286, 9, x_285);
lean_ctor_set(x_286, 10, x_279);
lean_ctor_set(x_286, 11, x_280);
x_287 = lean_st_ref_set(x_3, x_286, x_253);
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_289 = x_287;
} else {
 lean_dec_ref(x_287);
 x_289 = lean_box(0);
}
x_290 = l_Lean_mkFVar(x_244);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_288);
return x_291;
}
}
block_339:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_293);
x_294 = lean_st_ref_get(x_7, x_240);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_st_ref_get(x_3, x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
lean_inc(x_239);
x_300 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_299, x_239);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_239);
x_301 = l_Lean_Meta_Closure_collectExprAux(x_239, x_2, x_3, x_4, x_5, x_6, x_7, x_298);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_st_ref_get(x_7, x_303);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_306 = lean_st_ref_take(x_3, x_305);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = !lean_is_exclusive(x_307);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_307, 1);
x_311 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_312 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_302);
x_313 = l_Std_HashMap_insert___rarg(x_311, x_312, x_310, x_239, x_302);
lean_ctor_set(x_307, 1, x_313);
x_314 = lean_st_ref_set(x_3, x_307, x_308);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
x_241 = x_302;
x_242 = x_315;
goto block_292;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_316 = lean_ctor_get(x_307, 0);
x_317 = lean_ctor_get(x_307, 1);
x_318 = lean_ctor_get(x_307, 2);
x_319 = lean_ctor_get(x_307, 3);
x_320 = lean_ctor_get(x_307, 4);
x_321 = lean_ctor_get(x_307, 5);
x_322 = lean_ctor_get(x_307, 6);
x_323 = lean_ctor_get(x_307, 7);
x_324 = lean_ctor_get(x_307, 8);
x_325 = lean_ctor_get(x_307, 9);
x_326 = lean_ctor_get(x_307, 10);
x_327 = lean_ctor_get(x_307, 11);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_307);
x_328 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_329 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_302);
x_330 = l_Std_HashMap_insert___rarg(x_328, x_329, x_317, x_239, x_302);
x_331 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_331, 0, x_316);
lean_ctor_set(x_331, 1, x_330);
lean_ctor_set(x_331, 2, x_318);
lean_ctor_set(x_331, 3, x_319);
lean_ctor_set(x_331, 4, x_320);
lean_ctor_set(x_331, 5, x_321);
lean_ctor_set(x_331, 6, x_322);
lean_ctor_set(x_331, 7, x_323);
lean_ctor_set(x_331, 8, x_324);
lean_ctor_set(x_331, 9, x_325);
lean_ctor_set(x_331, 10, x_326);
lean_ctor_set(x_331, 11, x_327);
x_332 = lean_st_ref_set(x_3, x_331, x_308);
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec(x_332);
x_241 = x_302;
x_242 = x_333;
goto block_292;
}
}
else
{
uint8_t x_334; 
lean_dec(x_239);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_334 = !lean_is_exclusive(x_301);
if (x_334 == 0)
{
return x_301;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_301, 0);
x_336 = lean_ctor_get(x_301, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_301);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
lean_object* x_338; 
lean_dec(x_239);
x_338 = lean_ctor_get(x_300, 0);
lean_inc(x_338);
lean_dec(x_300);
x_241 = x_338;
x_242 = x_298;
goto block_292;
}
}
}
else
{
uint8_t x_346; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_346 = !lean_is_exclusive(x_238);
if (x_346 == 0)
{
return x_238;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_238, 0);
x_348 = lean_ctor_get(x_238, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_238);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_350 = !lean_is_exclusive(x_234);
if (x_350 == 0)
{
return x_234;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_234, 0);
x_352 = lean_ctor_get(x_234, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_234);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
case 3:
{
uint8_t x_354; 
x_354 = !lean_is_exclusive(x_1);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_355 = lean_ctor_get(x_1, 0);
lean_inc(x_355);
x_356 = l_Lean_Meta_Closure_collectLevel(x_355, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_357 = !lean_is_exclusive(x_356);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_356, 0);
x_359 = lean_expr_update_sort(x_1, x_358);
lean_ctor_set(x_356, 0, x_359);
return x_356;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_360 = lean_ctor_get(x_356, 0);
x_361 = lean_ctor_get(x_356, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_356);
x_362 = lean_expr_update_sort(x_1, x_360);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; uint64_t x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_364 = lean_ctor_get(x_1, 0);
x_365 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_364);
lean_dec(x_1);
lean_inc(x_364);
x_366 = l_Lean_Meta_Closure_collectLevel(x_364, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
x_370 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_370, 0, x_364);
lean_ctor_set_uint64(x_370, sizeof(void*)*1, x_365);
x_371 = lean_expr_update_sort(x_370, x_367);
if (lean_is_scalar(x_369)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_369;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_368);
return x_372;
}
}
case 4:
{
uint8_t x_373; 
x_373 = !lean_is_exclusive(x_1);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_374 = lean_ctor_get(x_1, 1);
lean_inc(x_374);
x_375 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3(x_374, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_376 = !lean_is_exclusive(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_375, 0);
x_378 = lean_expr_update_const(x_1, x_377);
lean_ctor_set(x_375, 0, x_378);
return x_375;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_379 = lean_ctor_get(x_375, 0);
x_380 = lean_ctor_get(x_375, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_375);
x_381 = lean_expr_update_const(x_1, x_379);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
}
else
{
lean_object* x_383; lean_object* x_384; uint64_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_383 = lean_ctor_get(x_1, 0);
x_384 = lean_ctor_get(x_1, 1);
x_385 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_1);
lean_inc(x_384);
x_386 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3(x_384, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_389 = x_386;
} else {
 lean_dec_ref(x_386);
 x_389 = lean_box(0);
}
x_390 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_390, 0, x_383);
lean_ctor_set(x_390, 1, x_384);
lean_ctor_set_uint64(x_390, sizeof(void*)*2, x_385);
x_391 = lean_expr_update_const(x_390, x_387);
if (lean_is_scalar(x_389)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_389;
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_388);
return x_392;
}
}
case 5:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_466; uint8_t x_513; 
x_393 = lean_ctor_get(x_1, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_1, 1);
lean_inc(x_394);
x_513 = l_Lean_Expr_hasLevelParam(x_393);
if (x_513 == 0)
{
uint8_t x_514; 
x_514 = l_Lean_Expr_hasFVar(x_393);
if (x_514 == 0)
{
uint8_t x_515; 
x_515 = l_Lean_Expr_hasMVar(x_393);
if (x_515 == 0)
{
x_395 = x_393;
x_396 = x_8;
goto block_465;
}
else
{
lean_object* x_516; 
x_516 = lean_box(0);
x_466 = x_516;
goto block_512;
}
}
else
{
lean_object* x_517; 
x_517 = lean_box(0);
x_466 = x_517;
goto block_512;
}
}
else
{
lean_object* x_518; 
x_518 = lean_box(0);
x_466 = x_518;
goto block_512;
}
block_465:
{
lean_object* x_397; lean_object* x_398; lean_object* x_412; uint8_t x_459; 
x_459 = l_Lean_Expr_hasLevelParam(x_394);
if (x_459 == 0)
{
uint8_t x_460; 
x_460 = l_Lean_Expr_hasFVar(x_394);
if (x_460 == 0)
{
uint8_t x_461; 
x_461 = l_Lean_Expr_hasMVar(x_394);
if (x_461 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_397 = x_394;
x_398 = x_396;
goto block_411;
}
else
{
lean_object* x_462; 
x_462 = lean_box(0);
x_412 = x_462;
goto block_458;
}
}
else
{
lean_object* x_463; 
x_463 = lean_box(0);
x_412 = x_463;
goto block_458;
}
}
else
{
lean_object* x_464; 
x_464 = lean_box(0);
x_412 = x_464;
goto block_458;
}
block_411:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_399; 
x_399 = !lean_is_exclusive(x_1);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_expr_update_app(x_1, x_395, x_397);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_398);
return x_401;
}
else
{
lean_object* x_402; lean_object* x_403; uint64_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_402 = lean_ctor_get(x_1, 0);
x_403 = lean_ctor_get(x_1, 1);
x_404 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_1);
x_405 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_403);
lean_ctor_set_uint64(x_405, sizeof(void*)*2, x_404);
x_406 = lean_expr_update_app(x_405, x_395, x_397);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_398);
return x_407;
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_1);
x_408 = l_Lean_Meta_Closure_collectExprAux___closed__10;
x_409 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_408);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_398);
return x_410;
}
}
block_458:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_412);
x_413 = lean_st_ref_get(x_7, x_396);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_st_ref_get(x_3, x_414);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
lean_inc(x_394);
x_419 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_418, x_394);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
lean_inc(x_7);
lean_inc(x_394);
x_420 = l_Lean_Meta_Closure_collectExprAux(x_394, x_2, x_3, x_4, x_5, x_6, x_7, x_417);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_st_ref_get(x_7, x_422);
lean_dec(x_7);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_st_ref_take(x_3, x_424);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = !lean_is_exclusive(x_426);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_429 = lean_ctor_get(x_426, 1);
x_430 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_431 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_421);
x_432 = l_Std_HashMap_insert___rarg(x_430, x_431, x_429, x_394, x_421);
lean_ctor_set(x_426, 1, x_432);
x_433 = lean_st_ref_set(x_3, x_426, x_427);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
lean_dec(x_433);
x_397 = x_421;
x_398 = x_434;
goto block_411;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_435 = lean_ctor_get(x_426, 0);
x_436 = lean_ctor_get(x_426, 1);
x_437 = lean_ctor_get(x_426, 2);
x_438 = lean_ctor_get(x_426, 3);
x_439 = lean_ctor_get(x_426, 4);
x_440 = lean_ctor_get(x_426, 5);
x_441 = lean_ctor_get(x_426, 6);
x_442 = lean_ctor_get(x_426, 7);
x_443 = lean_ctor_get(x_426, 8);
x_444 = lean_ctor_get(x_426, 9);
x_445 = lean_ctor_get(x_426, 10);
x_446 = lean_ctor_get(x_426, 11);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_426);
x_447 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_448 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_421);
x_449 = l_Std_HashMap_insert___rarg(x_447, x_448, x_436, x_394, x_421);
x_450 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_450, 0, x_435);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set(x_450, 2, x_437);
lean_ctor_set(x_450, 3, x_438);
lean_ctor_set(x_450, 4, x_439);
lean_ctor_set(x_450, 5, x_440);
lean_ctor_set(x_450, 6, x_441);
lean_ctor_set(x_450, 7, x_442);
lean_ctor_set(x_450, 8, x_443);
lean_ctor_set(x_450, 9, x_444);
lean_ctor_set(x_450, 10, x_445);
lean_ctor_set(x_450, 11, x_446);
x_451 = lean_st_ref_set(x_3, x_450, x_427);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_397 = x_421;
x_398 = x_452;
goto block_411;
}
}
else
{
uint8_t x_453; 
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_7);
lean_dec(x_1);
x_453 = !lean_is_exclusive(x_420);
if (x_453 == 0)
{
return x_420;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_420, 0);
x_455 = lean_ctor_get(x_420, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_420);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
lean_object* x_457; 
lean_dec(x_394);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_457 = lean_ctor_get(x_419, 0);
lean_inc(x_457);
lean_dec(x_419);
x_397 = x_457;
x_398 = x_417;
goto block_411;
}
}
}
block_512:
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_466);
x_467 = lean_st_ref_get(x_7, x_8);
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
lean_dec(x_467);
x_469 = lean_st_ref_get(x_3, x_468);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
lean_inc(x_393);
x_473 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_472, x_393);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_393);
x_474 = l_Lean_Meta_Closure_collectExprAux(x_393, x_2, x_3, x_4, x_5, x_6, x_7, x_471);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
x_477 = lean_st_ref_get(x_7, x_476);
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
lean_dec(x_477);
x_479 = lean_st_ref_take(x_3, x_478);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_482 = !lean_is_exclusive(x_480);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_483 = lean_ctor_get(x_480, 1);
x_484 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_485 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_475);
x_486 = l_Std_HashMap_insert___rarg(x_484, x_485, x_483, x_393, x_475);
lean_ctor_set(x_480, 1, x_486);
x_487 = lean_st_ref_set(x_3, x_480, x_481);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec(x_487);
x_395 = x_475;
x_396 = x_488;
goto block_465;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_489 = lean_ctor_get(x_480, 0);
x_490 = lean_ctor_get(x_480, 1);
x_491 = lean_ctor_get(x_480, 2);
x_492 = lean_ctor_get(x_480, 3);
x_493 = lean_ctor_get(x_480, 4);
x_494 = lean_ctor_get(x_480, 5);
x_495 = lean_ctor_get(x_480, 6);
x_496 = lean_ctor_get(x_480, 7);
x_497 = lean_ctor_get(x_480, 8);
x_498 = lean_ctor_get(x_480, 9);
x_499 = lean_ctor_get(x_480, 10);
x_500 = lean_ctor_get(x_480, 11);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_inc(x_497);
lean_inc(x_496);
lean_inc(x_495);
lean_inc(x_494);
lean_inc(x_493);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_480);
x_501 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_502 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_475);
x_503 = l_Std_HashMap_insert___rarg(x_501, x_502, x_490, x_393, x_475);
x_504 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_504, 0, x_489);
lean_ctor_set(x_504, 1, x_503);
lean_ctor_set(x_504, 2, x_491);
lean_ctor_set(x_504, 3, x_492);
lean_ctor_set(x_504, 4, x_493);
lean_ctor_set(x_504, 5, x_494);
lean_ctor_set(x_504, 6, x_495);
lean_ctor_set(x_504, 7, x_496);
lean_ctor_set(x_504, 8, x_497);
lean_ctor_set(x_504, 9, x_498);
lean_ctor_set(x_504, 10, x_499);
lean_ctor_set(x_504, 11, x_500);
x_505 = lean_st_ref_set(x_3, x_504, x_481);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
x_395 = x_475;
x_396 = x_506;
goto block_465;
}
}
else
{
uint8_t x_507; 
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_507 = !lean_is_exclusive(x_474);
if (x_507 == 0)
{
return x_474;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_474, 0);
x_509 = lean_ctor_get(x_474, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_474);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
else
{
lean_object* x_511; 
lean_dec(x_393);
x_511 = lean_ctor_get(x_473, 0);
lean_inc(x_511);
lean_dec(x_473);
x_395 = x_511;
x_396 = x_471;
goto block_465;
}
}
}
case 6:
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_596; uint8_t x_643; 
x_519 = lean_ctor_get(x_1, 1);
lean_inc(x_519);
x_520 = lean_ctor_get(x_1, 2);
lean_inc(x_520);
x_643 = l_Lean_Expr_hasLevelParam(x_519);
if (x_643 == 0)
{
uint8_t x_644; 
x_644 = l_Lean_Expr_hasFVar(x_519);
if (x_644 == 0)
{
uint8_t x_645; 
x_645 = l_Lean_Expr_hasMVar(x_519);
if (x_645 == 0)
{
x_521 = x_519;
x_522 = x_8;
goto block_595;
}
else
{
lean_object* x_646; 
x_646 = lean_box(0);
x_596 = x_646;
goto block_642;
}
}
else
{
lean_object* x_647; 
x_647 = lean_box(0);
x_596 = x_647;
goto block_642;
}
}
else
{
lean_object* x_648; 
x_648 = lean_box(0);
x_596 = x_648;
goto block_642;
}
block_595:
{
lean_object* x_523; lean_object* x_524; lean_object* x_542; uint8_t x_589; 
x_589 = l_Lean_Expr_hasLevelParam(x_520);
if (x_589 == 0)
{
uint8_t x_590; 
x_590 = l_Lean_Expr_hasFVar(x_520);
if (x_590 == 0)
{
uint8_t x_591; 
x_591 = l_Lean_Expr_hasMVar(x_520);
if (x_591 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_523 = x_520;
x_524 = x_522;
goto block_541;
}
else
{
lean_object* x_592; 
x_592 = lean_box(0);
x_542 = x_592;
goto block_588;
}
}
else
{
lean_object* x_593; 
x_593 = lean_box(0);
x_542 = x_593;
goto block_588;
}
}
else
{
lean_object* x_594; 
x_594 = lean_box(0);
x_542 = x_594;
goto block_588;
}
block_541:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_525; 
x_525 = !lean_is_exclusive(x_1);
if (x_525 == 0)
{
uint64_t x_526; uint8_t x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_527 = (uint8_t)((x_526 << 24) >> 61);
x_528 = lean_expr_update_lambda(x_1, x_527, x_521, x_523);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_524);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; uint64_t x_533; lean_object* x_534; uint8_t x_535; lean_object* x_536; lean_object* x_537; 
x_530 = lean_ctor_get(x_1, 0);
x_531 = lean_ctor_get(x_1, 1);
x_532 = lean_ctor_get(x_1, 2);
x_533 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_532);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_1);
x_534 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_534, 0, x_530);
lean_ctor_set(x_534, 1, x_531);
lean_ctor_set(x_534, 2, x_532);
lean_ctor_set_uint64(x_534, sizeof(void*)*3, x_533);
x_535 = (uint8_t)((x_533 << 24) >> 61);
x_536 = lean_expr_update_lambda(x_534, x_535, x_521, x_523);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_524);
return x_537;
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_1);
x_538 = l_Lean_Meta_Closure_collectExprAux___closed__13;
x_539 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_538);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_524);
return x_540;
}
}
block_588:
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_542);
x_543 = lean_st_ref_get(x_7, x_522);
x_544 = lean_ctor_get(x_543, 1);
lean_inc(x_544);
lean_dec(x_543);
x_545 = lean_st_ref_get(x_3, x_544);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
lean_inc(x_520);
x_549 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_548, x_520);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; 
lean_inc(x_7);
lean_inc(x_520);
x_550 = l_Lean_Meta_Closure_collectExprAux(x_520, x_2, x_3, x_4, x_5, x_6, x_7, x_547);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = lean_st_ref_get(x_7, x_552);
lean_dec(x_7);
x_554 = lean_ctor_get(x_553, 1);
lean_inc(x_554);
lean_dec(x_553);
x_555 = lean_st_ref_take(x_3, x_554);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = !lean_is_exclusive(x_556);
if (x_558 == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_559 = lean_ctor_get(x_556, 1);
x_560 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_561 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_551);
x_562 = l_Std_HashMap_insert___rarg(x_560, x_561, x_559, x_520, x_551);
lean_ctor_set(x_556, 1, x_562);
x_563 = lean_st_ref_set(x_3, x_556, x_557);
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
lean_dec(x_563);
x_523 = x_551;
x_524 = x_564;
goto block_541;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_565 = lean_ctor_get(x_556, 0);
x_566 = lean_ctor_get(x_556, 1);
x_567 = lean_ctor_get(x_556, 2);
x_568 = lean_ctor_get(x_556, 3);
x_569 = lean_ctor_get(x_556, 4);
x_570 = lean_ctor_get(x_556, 5);
x_571 = lean_ctor_get(x_556, 6);
x_572 = lean_ctor_get(x_556, 7);
x_573 = lean_ctor_get(x_556, 8);
x_574 = lean_ctor_get(x_556, 9);
x_575 = lean_ctor_get(x_556, 10);
x_576 = lean_ctor_get(x_556, 11);
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
lean_dec(x_556);
x_577 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_578 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_551);
x_579 = l_Std_HashMap_insert___rarg(x_577, x_578, x_566, x_520, x_551);
x_580 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_580, 0, x_565);
lean_ctor_set(x_580, 1, x_579);
lean_ctor_set(x_580, 2, x_567);
lean_ctor_set(x_580, 3, x_568);
lean_ctor_set(x_580, 4, x_569);
lean_ctor_set(x_580, 5, x_570);
lean_ctor_set(x_580, 6, x_571);
lean_ctor_set(x_580, 7, x_572);
lean_ctor_set(x_580, 8, x_573);
lean_ctor_set(x_580, 9, x_574);
lean_ctor_set(x_580, 10, x_575);
lean_ctor_set(x_580, 11, x_576);
x_581 = lean_st_ref_set(x_3, x_580, x_557);
x_582 = lean_ctor_get(x_581, 1);
lean_inc(x_582);
lean_dec(x_581);
x_523 = x_551;
x_524 = x_582;
goto block_541;
}
}
else
{
uint8_t x_583; 
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_7);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_550);
if (x_583 == 0)
{
return x_550;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_550, 0);
x_585 = lean_ctor_get(x_550, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_550);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; 
lean_dec(x_520);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_587 = lean_ctor_get(x_549, 0);
lean_inc(x_587);
lean_dec(x_549);
x_523 = x_587;
x_524 = x_547;
goto block_541;
}
}
}
block_642:
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_596);
x_597 = lean_st_ref_get(x_7, x_8);
x_598 = lean_ctor_get(x_597, 1);
lean_inc(x_598);
lean_dec(x_597);
x_599 = lean_st_ref_get(x_3, x_598);
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
lean_inc(x_519);
x_603 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_602, x_519);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_519);
x_604 = l_Lean_Meta_Closure_collectExprAux(x_519, x_2, x_3, x_4, x_5, x_6, x_7, x_601);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec(x_604);
x_607 = lean_st_ref_get(x_7, x_606);
x_608 = lean_ctor_get(x_607, 1);
lean_inc(x_608);
lean_dec(x_607);
x_609 = lean_st_ref_take(x_3, x_608);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = !lean_is_exclusive(x_610);
if (x_612 == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_613 = lean_ctor_get(x_610, 1);
x_614 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_615 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_605);
x_616 = l_Std_HashMap_insert___rarg(x_614, x_615, x_613, x_519, x_605);
lean_ctor_set(x_610, 1, x_616);
x_617 = lean_st_ref_set(x_3, x_610, x_611);
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
x_521 = x_605;
x_522 = x_618;
goto block_595;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_619 = lean_ctor_get(x_610, 0);
x_620 = lean_ctor_get(x_610, 1);
x_621 = lean_ctor_get(x_610, 2);
x_622 = lean_ctor_get(x_610, 3);
x_623 = lean_ctor_get(x_610, 4);
x_624 = lean_ctor_get(x_610, 5);
x_625 = lean_ctor_get(x_610, 6);
x_626 = lean_ctor_get(x_610, 7);
x_627 = lean_ctor_get(x_610, 8);
x_628 = lean_ctor_get(x_610, 9);
x_629 = lean_ctor_get(x_610, 10);
x_630 = lean_ctor_get(x_610, 11);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
lean_inc(x_627);
lean_inc(x_626);
lean_inc(x_625);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_inc(x_621);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_610);
x_631 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_632 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_605);
x_633 = l_Std_HashMap_insert___rarg(x_631, x_632, x_620, x_519, x_605);
x_634 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_634, 0, x_619);
lean_ctor_set(x_634, 1, x_633);
lean_ctor_set(x_634, 2, x_621);
lean_ctor_set(x_634, 3, x_622);
lean_ctor_set(x_634, 4, x_623);
lean_ctor_set(x_634, 5, x_624);
lean_ctor_set(x_634, 6, x_625);
lean_ctor_set(x_634, 7, x_626);
lean_ctor_set(x_634, 8, x_627);
lean_ctor_set(x_634, 9, x_628);
lean_ctor_set(x_634, 10, x_629);
lean_ctor_set(x_634, 11, x_630);
x_635 = lean_st_ref_set(x_3, x_634, x_611);
x_636 = lean_ctor_get(x_635, 1);
lean_inc(x_636);
lean_dec(x_635);
x_521 = x_605;
x_522 = x_636;
goto block_595;
}
}
else
{
uint8_t x_637; 
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_637 = !lean_is_exclusive(x_604);
if (x_637 == 0)
{
return x_604;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_604, 0);
x_639 = lean_ctor_get(x_604, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_604);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
else
{
lean_object* x_641; 
lean_dec(x_519);
x_641 = lean_ctor_get(x_603, 0);
lean_inc(x_641);
lean_dec(x_603);
x_521 = x_641;
x_522 = x_601;
goto block_595;
}
}
}
case 7:
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_726; uint8_t x_773; 
x_649 = lean_ctor_get(x_1, 1);
lean_inc(x_649);
x_650 = lean_ctor_get(x_1, 2);
lean_inc(x_650);
x_773 = l_Lean_Expr_hasLevelParam(x_649);
if (x_773 == 0)
{
uint8_t x_774; 
x_774 = l_Lean_Expr_hasFVar(x_649);
if (x_774 == 0)
{
uint8_t x_775; 
x_775 = l_Lean_Expr_hasMVar(x_649);
if (x_775 == 0)
{
x_651 = x_649;
x_652 = x_8;
goto block_725;
}
else
{
lean_object* x_776; 
x_776 = lean_box(0);
x_726 = x_776;
goto block_772;
}
}
else
{
lean_object* x_777; 
x_777 = lean_box(0);
x_726 = x_777;
goto block_772;
}
}
else
{
lean_object* x_778; 
x_778 = lean_box(0);
x_726 = x_778;
goto block_772;
}
block_725:
{
lean_object* x_653; lean_object* x_654; lean_object* x_672; uint8_t x_719; 
x_719 = l_Lean_Expr_hasLevelParam(x_650);
if (x_719 == 0)
{
uint8_t x_720; 
x_720 = l_Lean_Expr_hasFVar(x_650);
if (x_720 == 0)
{
uint8_t x_721; 
x_721 = l_Lean_Expr_hasMVar(x_650);
if (x_721 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_653 = x_650;
x_654 = x_652;
goto block_671;
}
else
{
lean_object* x_722; 
x_722 = lean_box(0);
x_672 = x_722;
goto block_718;
}
}
else
{
lean_object* x_723; 
x_723 = lean_box(0);
x_672 = x_723;
goto block_718;
}
}
else
{
lean_object* x_724; 
x_724 = lean_box(0);
x_672 = x_724;
goto block_718;
}
block_671:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_655; 
x_655 = !lean_is_exclusive(x_1);
if (x_655 == 0)
{
uint64_t x_656; uint8_t x_657; lean_object* x_658; lean_object* x_659; 
x_656 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_657 = (uint8_t)((x_656 << 24) >> 61);
x_658 = lean_expr_update_forall(x_1, x_657, x_651, x_653);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_654);
return x_659;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; uint64_t x_663; lean_object* x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; 
x_660 = lean_ctor_get(x_1, 0);
x_661 = lean_ctor_get(x_1, 1);
x_662 = lean_ctor_get(x_1, 2);
x_663 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_662);
lean_inc(x_661);
lean_inc(x_660);
lean_dec(x_1);
x_664 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_664, 0, x_660);
lean_ctor_set(x_664, 1, x_661);
lean_ctor_set(x_664, 2, x_662);
lean_ctor_set_uint64(x_664, sizeof(void*)*3, x_663);
x_665 = (uint8_t)((x_663 << 24) >> 61);
x_666 = lean_expr_update_forall(x_664, x_665, x_651, x_653);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_654);
return x_667;
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_1);
x_668 = l_Lean_Meta_Closure_collectExprAux___closed__16;
x_669 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_668);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_654);
return x_670;
}
}
block_718:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_672);
x_673 = lean_st_ref_get(x_7, x_652);
x_674 = lean_ctor_get(x_673, 1);
lean_inc(x_674);
lean_dec(x_673);
x_675 = lean_st_ref_get(x_3, x_674);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
lean_inc(x_650);
x_679 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_678, x_650);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; 
lean_inc(x_7);
lean_inc(x_650);
x_680 = l_Lean_Meta_Closure_collectExprAux(x_650, x_2, x_3, x_4, x_5, x_6, x_7, x_677);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = lean_st_ref_get(x_7, x_682);
lean_dec(x_7);
x_684 = lean_ctor_get(x_683, 1);
lean_inc(x_684);
lean_dec(x_683);
x_685 = lean_st_ref_take(x_3, x_684);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
x_688 = !lean_is_exclusive(x_686);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_689 = lean_ctor_get(x_686, 1);
x_690 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_691 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_681);
x_692 = l_Std_HashMap_insert___rarg(x_690, x_691, x_689, x_650, x_681);
lean_ctor_set(x_686, 1, x_692);
x_693 = lean_st_ref_set(x_3, x_686, x_687);
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
lean_dec(x_693);
x_653 = x_681;
x_654 = x_694;
goto block_671;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_695 = lean_ctor_get(x_686, 0);
x_696 = lean_ctor_get(x_686, 1);
x_697 = lean_ctor_get(x_686, 2);
x_698 = lean_ctor_get(x_686, 3);
x_699 = lean_ctor_get(x_686, 4);
x_700 = lean_ctor_get(x_686, 5);
x_701 = lean_ctor_get(x_686, 6);
x_702 = lean_ctor_get(x_686, 7);
x_703 = lean_ctor_get(x_686, 8);
x_704 = lean_ctor_get(x_686, 9);
x_705 = lean_ctor_get(x_686, 10);
x_706 = lean_ctor_get(x_686, 11);
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
lean_inc(x_695);
lean_dec(x_686);
x_707 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_708 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_681);
x_709 = l_Std_HashMap_insert___rarg(x_707, x_708, x_696, x_650, x_681);
x_710 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_710, 0, x_695);
lean_ctor_set(x_710, 1, x_709);
lean_ctor_set(x_710, 2, x_697);
lean_ctor_set(x_710, 3, x_698);
lean_ctor_set(x_710, 4, x_699);
lean_ctor_set(x_710, 5, x_700);
lean_ctor_set(x_710, 6, x_701);
lean_ctor_set(x_710, 7, x_702);
lean_ctor_set(x_710, 8, x_703);
lean_ctor_set(x_710, 9, x_704);
lean_ctor_set(x_710, 10, x_705);
lean_ctor_set(x_710, 11, x_706);
x_711 = lean_st_ref_set(x_3, x_710, x_687);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
lean_dec(x_711);
x_653 = x_681;
x_654 = x_712;
goto block_671;
}
}
else
{
uint8_t x_713; 
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_7);
lean_dec(x_1);
x_713 = !lean_is_exclusive(x_680);
if (x_713 == 0)
{
return x_680;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_680, 0);
x_715 = lean_ctor_get(x_680, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_680);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
else
{
lean_object* x_717; 
lean_dec(x_650);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_717 = lean_ctor_get(x_679, 0);
lean_inc(x_717);
lean_dec(x_679);
x_653 = x_717;
x_654 = x_677;
goto block_671;
}
}
}
block_772:
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_726);
x_727 = lean_st_ref_get(x_7, x_8);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
lean_dec(x_727);
x_729 = lean_st_ref_get(x_3, x_728);
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
lean_inc(x_649);
x_733 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_732, x_649);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_649);
x_734 = l_Lean_Meta_Closure_collectExprAux(x_649, x_2, x_3, x_4, x_5, x_6, x_7, x_731);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; uint8_t x_742; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_st_ref_get(x_7, x_736);
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
lean_dec(x_737);
x_739 = lean_st_ref_take(x_3, x_738);
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_742 = !lean_is_exclusive(x_740);
if (x_742 == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_743 = lean_ctor_get(x_740, 1);
x_744 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_745 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_735);
x_746 = l_Std_HashMap_insert___rarg(x_744, x_745, x_743, x_649, x_735);
lean_ctor_set(x_740, 1, x_746);
x_747 = lean_st_ref_set(x_3, x_740, x_741);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
lean_dec(x_747);
x_651 = x_735;
x_652 = x_748;
goto block_725;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_749 = lean_ctor_get(x_740, 0);
x_750 = lean_ctor_get(x_740, 1);
x_751 = lean_ctor_get(x_740, 2);
x_752 = lean_ctor_get(x_740, 3);
x_753 = lean_ctor_get(x_740, 4);
x_754 = lean_ctor_get(x_740, 5);
x_755 = lean_ctor_get(x_740, 6);
x_756 = lean_ctor_get(x_740, 7);
x_757 = lean_ctor_get(x_740, 8);
x_758 = lean_ctor_get(x_740, 9);
x_759 = lean_ctor_get(x_740, 10);
x_760 = lean_ctor_get(x_740, 11);
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
lean_dec(x_740);
x_761 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_762 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_735);
x_763 = l_Std_HashMap_insert___rarg(x_761, x_762, x_750, x_649, x_735);
x_764 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_764, 0, x_749);
lean_ctor_set(x_764, 1, x_763);
lean_ctor_set(x_764, 2, x_751);
lean_ctor_set(x_764, 3, x_752);
lean_ctor_set(x_764, 4, x_753);
lean_ctor_set(x_764, 5, x_754);
lean_ctor_set(x_764, 6, x_755);
lean_ctor_set(x_764, 7, x_756);
lean_ctor_set(x_764, 8, x_757);
lean_ctor_set(x_764, 9, x_758);
lean_ctor_set(x_764, 10, x_759);
lean_ctor_set(x_764, 11, x_760);
x_765 = lean_st_ref_set(x_3, x_764, x_741);
x_766 = lean_ctor_get(x_765, 1);
lean_inc(x_766);
lean_dec(x_765);
x_651 = x_735;
x_652 = x_766;
goto block_725;
}
}
else
{
uint8_t x_767; 
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_767 = !lean_is_exclusive(x_734);
if (x_767 == 0)
{
return x_734;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_734, 0);
x_769 = lean_ctor_get(x_734, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_734);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
}
}
}
else
{
lean_object* x_771; 
lean_dec(x_649);
x_771 = lean_ctor_get(x_733, 0);
lean_inc(x_771);
lean_dec(x_733);
x_651 = x_771;
x_652 = x_731;
goto block_725;
}
}
}
case 8:
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_911; uint8_t x_958; 
x_779 = lean_ctor_get(x_1, 1);
lean_inc(x_779);
x_780 = lean_ctor_get(x_1, 2);
lean_inc(x_780);
x_781 = lean_ctor_get(x_1, 3);
lean_inc(x_781);
x_958 = l_Lean_Expr_hasLevelParam(x_779);
if (x_958 == 0)
{
uint8_t x_959; 
x_959 = l_Lean_Expr_hasFVar(x_779);
if (x_959 == 0)
{
uint8_t x_960; 
x_960 = l_Lean_Expr_hasMVar(x_779);
if (x_960 == 0)
{
x_782 = x_779;
x_783 = x_8;
goto block_910;
}
else
{
lean_object* x_961; 
x_961 = lean_box(0);
x_911 = x_961;
goto block_957;
}
}
else
{
lean_object* x_962; 
x_962 = lean_box(0);
x_911 = x_962;
goto block_957;
}
}
else
{
lean_object* x_963; 
x_963 = lean_box(0);
x_911 = x_963;
goto block_957;
}
block_910:
{
lean_object* x_784; lean_object* x_785; lean_object* x_857; uint8_t x_904; 
x_904 = l_Lean_Expr_hasLevelParam(x_780);
if (x_904 == 0)
{
uint8_t x_905; 
x_905 = l_Lean_Expr_hasFVar(x_780);
if (x_905 == 0)
{
uint8_t x_906; 
x_906 = l_Lean_Expr_hasMVar(x_780);
if (x_906 == 0)
{
x_784 = x_780;
x_785 = x_783;
goto block_856;
}
else
{
lean_object* x_907; 
x_907 = lean_box(0);
x_857 = x_907;
goto block_903;
}
}
else
{
lean_object* x_908; 
x_908 = lean_box(0);
x_857 = x_908;
goto block_903;
}
}
else
{
lean_object* x_909; 
x_909 = lean_box(0);
x_857 = x_909;
goto block_903;
}
block_856:
{
lean_object* x_786; lean_object* x_787; lean_object* x_803; uint8_t x_850; 
x_850 = l_Lean_Expr_hasLevelParam(x_781);
if (x_850 == 0)
{
uint8_t x_851; 
x_851 = l_Lean_Expr_hasFVar(x_781);
if (x_851 == 0)
{
uint8_t x_852; 
x_852 = l_Lean_Expr_hasMVar(x_781);
if (x_852 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_786 = x_781;
x_787 = x_785;
goto block_802;
}
else
{
lean_object* x_853; 
x_853 = lean_box(0);
x_803 = x_853;
goto block_849;
}
}
else
{
lean_object* x_854; 
x_854 = lean_box(0);
x_803 = x_854;
goto block_849;
}
}
else
{
lean_object* x_855; 
x_855 = lean_box(0);
x_803 = x_855;
goto block_849;
}
block_802:
{
if (lean_obj_tag(x_1) == 8)
{
uint8_t x_788; 
x_788 = !lean_is_exclusive(x_1);
if (x_788 == 0)
{
lean_object* x_789; lean_object* x_790; 
x_789 = lean_expr_update_let(x_1, x_782, x_784, x_786);
x_790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_787);
return x_790;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; uint64_t x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_791 = lean_ctor_get(x_1, 0);
x_792 = lean_ctor_get(x_1, 1);
x_793 = lean_ctor_get(x_1, 2);
x_794 = lean_ctor_get(x_1, 3);
x_795 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_794);
lean_inc(x_793);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_1);
x_796 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_796, 0, x_791);
lean_ctor_set(x_796, 1, x_792);
lean_ctor_set(x_796, 2, x_793);
lean_ctor_set(x_796, 3, x_794);
lean_ctor_set_uint64(x_796, sizeof(void*)*4, x_795);
x_797 = lean_expr_update_let(x_796, x_782, x_784, x_786);
x_798 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_787);
return x_798;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec(x_786);
lean_dec(x_784);
lean_dec(x_782);
lean_dec(x_1);
x_799 = l_Lean_Meta_Closure_collectExprAux___closed__19;
x_800 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_799);
x_801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_787);
return x_801;
}
}
block_849:
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_803);
x_804 = lean_st_ref_get(x_7, x_785);
x_805 = lean_ctor_get(x_804, 1);
lean_inc(x_805);
lean_dec(x_804);
x_806 = lean_st_ref_get(x_3, x_805);
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
lean_dec(x_806);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
lean_inc(x_781);
x_810 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_809, x_781);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; 
lean_inc(x_7);
lean_inc(x_781);
x_811 = l_Lean_Meta_Closure_collectExprAux(x_781, x_2, x_3, x_4, x_5, x_6, x_7, x_808);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; uint8_t x_819; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_814 = lean_st_ref_get(x_7, x_813);
lean_dec(x_7);
x_815 = lean_ctor_get(x_814, 1);
lean_inc(x_815);
lean_dec(x_814);
x_816 = lean_st_ref_take(x_3, x_815);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
x_819 = !lean_is_exclusive(x_817);
if (x_819 == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_820 = lean_ctor_get(x_817, 1);
x_821 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_822 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_812);
x_823 = l_Std_HashMap_insert___rarg(x_821, x_822, x_820, x_781, x_812);
lean_ctor_set(x_817, 1, x_823);
x_824 = lean_st_ref_set(x_3, x_817, x_818);
x_825 = lean_ctor_get(x_824, 1);
lean_inc(x_825);
lean_dec(x_824);
x_786 = x_812;
x_787 = x_825;
goto block_802;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_826 = lean_ctor_get(x_817, 0);
x_827 = lean_ctor_get(x_817, 1);
x_828 = lean_ctor_get(x_817, 2);
x_829 = lean_ctor_get(x_817, 3);
x_830 = lean_ctor_get(x_817, 4);
x_831 = lean_ctor_get(x_817, 5);
x_832 = lean_ctor_get(x_817, 6);
x_833 = lean_ctor_get(x_817, 7);
x_834 = lean_ctor_get(x_817, 8);
x_835 = lean_ctor_get(x_817, 9);
x_836 = lean_ctor_get(x_817, 10);
x_837 = lean_ctor_get(x_817, 11);
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
lean_inc(x_826);
lean_dec(x_817);
x_838 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_839 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_812);
x_840 = l_Std_HashMap_insert___rarg(x_838, x_839, x_827, x_781, x_812);
x_841 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_841, 0, x_826);
lean_ctor_set(x_841, 1, x_840);
lean_ctor_set(x_841, 2, x_828);
lean_ctor_set(x_841, 3, x_829);
lean_ctor_set(x_841, 4, x_830);
lean_ctor_set(x_841, 5, x_831);
lean_ctor_set(x_841, 6, x_832);
lean_ctor_set(x_841, 7, x_833);
lean_ctor_set(x_841, 8, x_834);
lean_ctor_set(x_841, 9, x_835);
lean_ctor_set(x_841, 10, x_836);
lean_ctor_set(x_841, 11, x_837);
x_842 = lean_st_ref_set(x_3, x_841, x_818);
x_843 = lean_ctor_get(x_842, 1);
lean_inc(x_843);
lean_dec(x_842);
x_786 = x_812;
x_787 = x_843;
goto block_802;
}
}
else
{
uint8_t x_844; 
lean_dec(x_784);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_7);
lean_dec(x_1);
x_844 = !lean_is_exclusive(x_811);
if (x_844 == 0)
{
return x_811;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_811, 0);
x_846 = lean_ctor_get(x_811, 1);
lean_inc(x_846);
lean_inc(x_845);
lean_dec(x_811);
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
return x_847;
}
}
}
else
{
lean_object* x_848; 
lean_dec(x_781);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_848 = lean_ctor_get(x_810, 0);
lean_inc(x_848);
lean_dec(x_810);
x_786 = x_848;
x_787 = x_808;
goto block_802;
}
}
}
block_903:
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
lean_dec(x_857);
x_858 = lean_st_ref_get(x_7, x_783);
x_859 = lean_ctor_get(x_858, 1);
lean_inc(x_859);
lean_dec(x_858);
x_860 = lean_st_ref_get(x_3, x_859);
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
lean_inc(x_780);
x_864 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_863, x_780);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_780);
x_865 = l_Lean_Meta_Closure_collectExprAux(x_780, x_2, x_3, x_4, x_5, x_6, x_7, x_862);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; 
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
x_868 = lean_st_ref_get(x_7, x_867);
x_869 = lean_ctor_get(x_868, 1);
lean_inc(x_869);
lean_dec(x_868);
x_870 = lean_st_ref_take(x_3, x_869);
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
lean_dec(x_870);
x_873 = !lean_is_exclusive(x_871);
if (x_873 == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_874 = lean_ctor_get(x_871, 1);
x_875 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_876 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_866);
x_877 = l_Std_HashMap_insert___rarg(x_875, x_876, x_874, x_780, x_866);
lean_ctor_set(x_871, 1, x_877);
x_878 = lean_st_ref_set(x_3, x_871, x_872);
x_879 = lean_ctor_get(x_878, 1);
lean_inc(x_879);
lean_dec(x_878);
x_784 = x_866;
x_785 = x_879;
goto block_856;
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_880 = lean_ctor_get(x_871, 0);
x_881 = lean_ctor_get(x_871, 1);
x_882 = lean_ctor_get(x_871, 2);
x_883 = lean_ctor_get(x_871, 3);
x_884 = lean_ctor_get(x_871, 4);
x_885 = lean_ctor_get(x_871, 5);
x_886 = lean_ctor_get(x_871, 6);
x_887 = lean_ctor_get(x_871, 7);
x_888 = lean_ctor_get(x_871, 8);
x_889 = lean_ctor_get(x_871, 9);
x_890 = lean_ctor_get(x_871, 10);
x_891 = lean_ctor_get(x_871, 11);
lean_inc(x_891);
lean_inc(x_890);
lean_inc(x_889);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
lean_inc(x_885);
lean_inc(x_884);
lean_inc(x_883);
lean_inc(x_882);
lean_inc(x_881);
lean_inc(x_880);
lean_dec(x_871);
x_892 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_893 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_866);
x_894 = l_Std_HashMap_insert___rarg(x_892, x_893, x_881, x_780, x_866);
x_895 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_895, 0, x_880);
lean_ctor_set(x_895, 1, x_894);
lean_ctor_set(x_895, 2, x_882);
lean_ctor_set(x_895, 3, x_883);
lean_ctor_set(x_895, 4, x_884);
lean_ctor_set(x_895, 5, x_885);
lean_ctor_set(x_895, 6, x_886);
lean_ctor_set(x_895, 7, x_887);
lean_ctor_set(x_895, 8, x_888);
lean_ctor_set(x_895, 9, x_889);
lean_ctor_set(x_895, 10, x_890);
lean_ctor_set(x_895, 11, x_891);
x_896 = lean_st_ref_set(x_3, x_895, x_872);
x_897 = lean_ctor_get(x_896, 1);
lean_inc(x_897);
lean_dec(x_896);
x_784 = x_866;
x_785 = x_897;
goto block_856;
}
}
else
{
uint8_t x_898; 
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_898 = !lean_is_exclusive(x_865);
if (x_898 == 0)
{
return x_865;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_899 = lean_ctor_get(x_865, 0);
x_900 = lean_ctor_get(x_865, 1);
lean_inc(x_900);
lean_inc(x_899);
lean_dec(x_865);
x_901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_901, 0, x_899);
lean_ctor_set(x_901, 1, x_900);
return x_901;
}
}
}
else
{
lean_object* x_902; 
lean_dec(x_780);
x_902 = lean_ctor_get(x_864, 0);
lean_inc(x_902);
lean_dec(x_864);
x_784 = x_902;
x_785 = x_862;
goto block_856;
}
}
}
block_957:
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_911);
x_912 = lean_st_ref_get(x_7, x_8);
x_913 = lean_ctor_get(x_912, 1);
lean_inc(x_913);
lean_dec(x_912);
x_914 = lean_st_ref_get(x_3, x_913);
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
lean_dec(x_914);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
lean_inc(x_779);
x_918 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_917, x_779);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_779);
x_919 = l_Lean_Meta_Closure_collectExprAux(x_779, x_2, x_3, x_4, x_5, x_6, x_7, x_916);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; uint8_t x_927; 
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
lean_dec(x_919);
x_922 = lean_st_ref_get(x_7, x_921);
x_923 = lean_ctor_get(x_922, 1);
lean_inc(x_923);
lean_dec(x_922);
x_924 = lean_st_ref_take(x_3, x_923);
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
lean_dec(x_924);
x_927 = !lean_is_exclusive(x_925);
if (x_927 == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_928 = lean_ctor_get(x_925, 1);
x_929 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_930 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_920);
x_931 = l_Std_HashMap_insert___rarg(x_929, x_930, x_928, x_779, x_920);
lean_ctor_set(x_925, 1, x_931);
x_932 = lean_st_ref_set(x_3, x_925, x_926);
x_933 = lean_ctor_get(x_932, 1);
lean_inc(x_933);
lean_dec(x_932);
x_782 = x_920;
x_783 = x_933;
goto block_910;
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_934 = lean_ctor_get(x_925, 0);
x_935 = lean_ctor_get(x_925, 1);
x_936 = lean_ctor_get(x_925, 2);
x_937 = lean_ctor_get(x_925, 3);
x_938 = lean_ctor_get(x_925, 4);
x_939 = lean_ctor_get(x_925, 5);
x_940 = lean_ctor_get(x_925, 6);
x_941 = lean_ctor_get(x_925, 7);
x_942 = lean_ctor_get(x_925, 8);
x_943 = lean_ctor_get(x_925, 9);
x_944 = lean_ctor_get(x_925, 10);
x_945 = lean_ctor_get(x_925, 11);
lean_inc(x_945);
lean_inc(x_944);
lean_inc(x_943);
lean_inc(x_942);
lean_inc(x_941);
lean_inc(x_940);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
lean_inc(x_936);
lean_inc(x_935);
lean_inc(x_934);
lean_dec(x_925);
x_946 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_947 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_920);
x_948 = l_Std_HashMap_insert___rarg(x_946, x_947, x_935, x_779, x_920);
x_949 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_949, 0, x_934);
lean_ctor_set(x_949, 1, x_948);
lean_ctor_set(x_949, 2, x_936);
lean_ctor_set(x_949, 3, x_937);
lean_ctor_set(x_949, 4, x_938);
lean_ctor_set(x_949, 5, x_939);
lean_ctor_set(x_949, 6, x_940);
lean_ctor_set(x_949, 7, x_941);
lean_ctor_set(x_949, 8, x_942);
lean_ctor_set(x_949, 9, x_943);
lean_ctor_set(x_949, 10, x_944);
lean_ctor_set(x_949, 11, x_945);
x_950 = lean_st_ref_set(x_3, x_949, x_926);
x_951 = lean_ctor_get(x_950, 1);
lean_inc(x_951);
lean_dec(x_950);
x_782 = x_920;
x_783 = x_951;
goto block_910;
}
}
else
{
uint8_t x_952; 
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_952 = !lean_is_exclusive(x_919);
if (x_952 == 0)
{
return x_919;
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_953 = lean_ctor_get(x_919, 0);
x_954 = lean_ctor_get(x_919, 1);
lean_inc(x_954);
lean_inc(x_953);
lean_dec(x_919);
x_955 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_955, 0, x_953);
lean_ctor_set(x_955, 1, x_954);
return x_955;
}
}
}
else
{
lean_object* x_956; 
lean_dec(x_779);
x_956 = lean_ctor_get(x_918, 0);
lean_inc(x_956);
lean_dec(x_918);
x_782 = x_956;
x_783 = x_916;
goto block_910;
}
}
}
case 10:
{
lean_object* x_964; lean_object* x_965; uint8_t x_1012; 
x_964 = lean_ctor_get(x_1, 1);
lean_inc(x_964);
x_1012 = l_Lean_Expr_hasLevelParam(x_964);
if (x_1012 == 0)
{
uint8_t x_1013; 
x_1013 = l_Lean_Expr_hasFVar(x_964);
if (x_1013 == 0)
{
uint8_t x_1014; 
x_1014 = l_Lean_Expr_hasMVar(x_964);
if (x_1014 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_964;
x_10 = x_8;
goto block_23;
}
else
{
lean_object* x_1015; 
x_1015 = lean_box(0);
x_965 = x_1015;
goto block_1011;
}
}
else
{
lean_object* x_1016; 
x_1016 = lean_box(0);
x_965 = x_1016;
goto block_1011;
}
}
else
{
lean_object* x_1017; 
x_1017 = lean_box(0);
x_965 = x_1017;
goto block_1011;
}
block_1011:
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
lean_dec(x_965);
x_966 = lean_st_ref_get(x_7, x_8);
x_967 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
lean_dec(x_966);
x_968 = lean_st_ref_get(x_3, x_967);
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_968, 1);
lean_inc(x_970);
lean_dec(x_968);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec(x_969);
lean_inc(x_964);
x_972 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_971, x_964);
if (lean_obj_tag(x_972) == 0)
{
lean_object* x_973; 
lean_inc(x_7);
lean_inc(x_964);
x_973 = l_Lean_Meta_Closure_collectExprAux(x_964, x_2, x_3, x_4, x_5, x_6, x_7, x_970);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; uint8_t x_981; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
lean_dec(x_973);
x_976 = lean_st_ref_get(x_7, x_975);
lean_dec(x_7);
x_977 = lean_ctor_get(x_976, 1);
lean_inc(x_977);
lean_dec(x_976);
x_978 = lean_st_ref_take(x_3, x_977);
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec(x_978);
x_981 = !lean_is_exclusive(x_979);
if (x_981 == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_982 = lean_ctor_get(x_979, 1);
x_983 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_984 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_974);
x_985 = l_Std_HashMap_insert___rarg(x_983, x_984, x_982, x_964, x_974);
lean_ctor_set(x_979, 1, x_985);
x_986 = lean_st_ref_set(x_3, x_979, x_980);
x_987 = lean_ctor_get(x_986, 1);
lean_inc(x_987);
lean_dec(x_986);
x_9 = x_974;
x_10 = x_987;
goto block_23;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_988 = lean_ctor_get(x_979, 0);
x_989 = lean_ctor_get(x_979, 1);
x_990 = lean_ctor_get(x_979, 2);
x_991 = lean_ctor_get(x_979, 3);
x_992 = lean_ctor_get(x_979, 4);
x_993 = lean_ctor_get(x_979, 5);
x_994 = lean_ctor_get(x_979, 6);
x_995 = lean_ctor_get(x_979, 7);
x_996 = lean_ctor_get(x_979, 8);
x_997 = lean_ctor_get(x_979, 9);
x_998 = lean_ctor_get(x_979, 10);
x_999 = lean_ctor_get(x_979, 11);
lean_inc(x_999);
lean_inc(x_998);
lean_inc(x_997);
lean_inc(x_996);
lean_inc(x_995);
lean_inc(x_994);
lean_inc(x_993);
lean_inc(x_992);
lean_inc(x_991);
lean_inc(x_990);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_979);
x_1000 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_1001 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_974);
x_1002 = l_Std_HashMap_insert___rarg(x_1000, x_1001, x_989, x_964, x_974);
x_1003 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1003, 0, x_988);
lean_ctor_set(x_1003, 1, x_1002);
lean_ctor_set(x_1003, 2, x_990);
lean_ctor_set(x_1003, 3, x_991);
lean_ctor_set(x_1003, 4, x_992);
lean_ctor_set(x_1003, 5, x_993);
lean_ctor_set(x_1003, 6, x_994);
lean_ctor_set(x_1003, 7, x_995);
lean_ctor_set(x_1003, 8, x_996);
lean_ctor_set(x_1003, 9, x_997);
lean_ctor_set(x_1003, 10, x_998);
lean_ctor_set(x_1003, 11, x_999);
x_1004 = lean_st_ref_set(x_3, x_1003, x_980);
x_1005 = lean_ctor_get(x_1004, 1);
lean_inc(x_1005);
lean_dec(x_1004);
x_9 = x_974;
x_10 = x_1005;
goto block_23;
}
}
else
{
uint8_t x_1006; 
lean_dec(x_964);
lean_dec(x_7);
lean_dec(x_1);
x_1006 = !lean_is_exclusive(x_973);
if (x_1006 == 0)
{
return x_973;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1007 = lean_ctor_get(x_973, 0);
x_1008 = lean_ctor_get(x_973, 1);
lean_inc(x_1008);
lean_inc(x_1007);
lean_dec(x_973);
x_1009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1009, 0, x_1007);
lean_ctor_set(x_1009, 1, x_1008);
return x_1009;
}
}
}
else
{
lean_object* x_1010; 
lean_dec(x_964);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1010 = lean_ctor_get(x_972, 0);
lean_inc(x_1010);
lean_dec(x_972);
x_9 = x_1010;
x_10 = x_970;
goto block_23;
}
}
}
case 11:
{
lean_object* x_1018; lean_object* x_1019; uint8_t x_1066; 
x_1018 = lean_ctor_get(x_1, 2);
lean_inc(x_1018);
x_1066 = l_Lean_Expr_hasLevelParam(x_1018);
if (x_1066 == 0)
{
uint8_t x_1067; 
x_1067 = l_Lean_Expr_hasFVar(x_1018);
if (x_1067 == 0)
{
uint8_t x_1068; 
x_1068 = l_Lean_Expr_hasMVar(x_1018);
if (x_1068 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = x_1018;
x_25 = x_8;
goto block_39;
}
else
{
lean_object* x_1069; 
x_1069 = lean_box(0);
x_1019 = x_1069;
goto block_1065;
}
}
else
{
lean_object* x_1070; 
x_1070 = lean_box(0);
x_1019 = x_1070;
goto block_1065;
}
}
else
{
lean_object* x_1071; 
x_1071 = lean_box(0);
x_1019 = x_1071;
goto block_1065;
}
block_1065:
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_1019);
x_1020 = lean_st_ref_get(x_7, x_8);
x_1021 = lean_ctor_get(x_1020, 1);
lean_inc(x_1021);
lean_dec(x_1020);
x_1022 = lean_st_ref_get(x_3, x_1021);
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
lean_dec(x_1022);
x_1025 = lean_ctor_get(x_1023, 1);
lean_inc(x_1025);
lean_dec(x_1023);
lean_inc(x_1018);
x_1026 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_1025, x_1018);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; 
lean_inc(x_7);
lean_inc(x_1018);
x_1027 = l_Lean_Meta_Closure_collectExprAux(x_1018, x_2, x_3, x_4, x_5, x_6, x_7, x_1024);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; 
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_st_ref_get(x_7, x_1029);
lean_dec(x_7);
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
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1036 = lean_ctor_get(x_1033, 1);
x_1037 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_1038 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1028);
x_1039 = l_Std_HashMap_insert___rarg(x_1037, x_1038, x_1036, x_1018, x_1028);
lean_ctor_set(x_1033, 1, x_1039);
x_1040 = lean_st_ref_set(x_3, x_1033, x_1034);
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc(x_1041);
lean_dec(x_1040);
x_24 = x_1028;
x_25 = x_1041;
goto block_39;
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1042 = lean_ctor_get(x_1033, 0);
x_1043 = lean_ctor_get(x_1033, 1);
x_1044 = lean_ctor_get(x_1033, 2);
x_1045 = lean_ctor_get(x_1033, 3);
x_1046 = lean_ctor_get(x_1033, 4);
x_1047 = lean_ctor_get(x_1033, 5);
x_1048 = lean_ctor_get(x_1033, 6);
x_1049 = lean_ctor_get(x_1033, 7);
x_1050 = lean_ctor_get(x_1033, 8);
x_1051 = lean_ctor_get(x_1033, 9);
x_1052 = lean_ctor_get(x_1033, 10);
x_1053 = lean_ctor_get(x_1033, 11);
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
lean_inc(x_1042);
lean_dec(x_1033);
x_1054 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_1055 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_1028);
x_1056 = l_Std_HashMap_insert___rarg(x_1054, x_1055, x_1043, x_1018, x_1028);
x_1057 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_1057, 0, x_1042);
lean_ctor_set(x_1057, 1, x_1056);
lean_ctor_set(x_1057, 2, x_1044);
lean_ctor_set(x_1057, 3, x_1045);
lean_ctor_set(x_1057, 4, x_1046);
lean_ctor_set(x_1057, 5, x_1047);
lean_ctor_set(x_1057, 6, x_1048);
lean_ctor_set(x_1057, 7, x_1049);
lean_ctor_set(x_1057, 8, x_1050);
lean_ctor_set(x_1057, 9, x_1051);
lean_ctor_set(x_1057, 10, x_1052);
lean_ctor_set(x_1057, 11, x_1053);
x_1058 = lean_st_ref_set(x_3, x_1057, x_1034);
x_1059 = lean_ctor_get(x_1058, 1);
lean_inc(x_1059);
lean_dec(x_1058);
x_24 = x_1028;
x_25 = x_1059;
goto block_39;
}
}
else
{
uint8_t x_1060; 
lean_dec(x_1018);
lean_dec(x_7);
lean_dec(x_1);
x_1060 = !lean_is_exclusive(x_1027);
if (x_1060 == 0)
{
return x_1027;
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1061 = lean_ctor_get(x_1027, 0);
x_1062 = lean_ctor_get(x_1027, 1);
lean_inc(x_1062);
lean_inc(x_1061);
lean_dec(x_1027);
x_1063 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1063, 0, x_1061);
lean_ctor_set(x_1063, 1, x_1062);
return x_1063;
}
}
}
else
{
lean_object* x_1064; 
lean_dec(x_1018);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1064 = lean_ctor_get(x_1026, 0);
lean_inc(x_1064);
lean_dec(x_1026);
x_24 = x_1064;
x_25 = x_1024;
goto block_39;
}
}
}
default: 
{
lean_object* x_1072; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1072 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1072, 0, x_1);
lean_ctor_set(x_1072, 1, x_8);
return x_1072;
}
}
block_23:
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_1);
x_20 = l_Lean_Meta_Closure_collectExprAux___closed__4;
x_21 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
block_39:
{
if (lean_obj_tag(x_1) == 11)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_expr_update_proj(x_1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 2);
x_32 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_33 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_32);
x_34 = lean_expr_update_proj(x_33, x_24);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_1);
x_36 = l_Lean_Meta_Closure_collectExprAux___closed__7;
x_37 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_mkFreshId___at_Lean_Meta_Closure_collectExprAux___spec__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_mkFreshFVarId___at_Lean_Meta_Closure_collectExprAux___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_List_mapM___at_Lean_Meta_Closure_collectExprAux___spec__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_105; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_105 = l_Lean_Expr_hasLevelParam(x_11);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_hasFVar(x_11);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasMVar(x_11);
if (x_107 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_108; 
lean_free_object(x_9);
x_108 = lean_box(0);
x_13 = x_108;
goto block_104;
}
}
else
{
lean_object* x_109; 
lean_free_object(x_9);
x_109 = lean_box(0);
x_13 = x_109;
goto block_104;
}
}
else
{
lean_object* x_110; 
lean_free_object(x_9);
x_110 = lean_box(0);
x_13 = x_110;
goto block_104;
}
block_104:
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
lean_inc(x_11);
x_21 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_20, x_11);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_33 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_23);
x_34 = l_Std_HashMap_insert___rarg(x_32, x_33, x_31, x_11, x_23);
lean_ctor_set(x_28, 1, x_34);
x_35 = lean_st_ref_set(x_3, x_28, x_29);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_23);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get(x_28, 2);
x_43 = lean_ctor_get(x_28, 3);
x_44 = lean_ctor_get(x_28, 4);
x_45 = lean_ctor_get(x_28, 5);
x_46 = lean_ctor_get(x_28, 6);
x_47 = lean_ctor_get(x_28, 7);
x_48 = lean_ctor_get(x_28, 8);
x_49 = lean_ctor_get(x_28, 9);
x_50 = lean_ctor_get(x_28, 10);
x_51 = lean_ctor_get(x_28, 11);
lean_inc(x_51);
lean_inc(x_50);
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
lean_dec(x_28);
x_52 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_53 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_23);
x_54 = l_Std_HashMap_insert___rarg(x_52, x_53, x_41, x_11, x_23);
x_55 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_42);
lean_ctor_set(x_55, 3, x_43);
lean_ctor_set(x_55, 4, x_44);
lean_ctor_set(x_55, 5, x_45);
lean_ctor_set(x_55, 6, x_46);
lean_ctor_set(x_55, 7, x_47);
lean_ctor_set(x_55, 8, x_48);
lean_ctor_set(x_55, 9, x_49);
lean_ctor_set(x_55, 10, x_50);
lean_ctor_set(x_55, 11, x_51);
x_56 = lean_st_ref_set(x_3, x_55, x_29);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_23);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_11);
lean_dec(x_7);
x_60 = !lean_is_exclusive(x_22);
if (x_60 == 0)
{
return x_22;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_22, 0);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_22);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_64 = lean_ctor_get(x_21, 0);
lean_inc(x_64);
lean_dec(x_21);
lean_ctor_set(x_16, 0, x_64);
return x_16;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_11);
x_68 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_67, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
lean_inc(x_7);
lean_inc(x_11);
x_69 = l_Lean_Meta_Closure_collectExprAux(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_7, x_71);
lean_dec(x_7);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_take(x_3, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_75, 6);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 7);
lean_inc(x_84);
x_85 = lean_ctor_get(x_75, 8);
lean_inc(x_85);
x_86 = lean_ctor_get(x_75, 9);
lean_inc(x_86);
x_87 = lean_ctor_get(x_75, 10);
lean_inc(x_87);
x_88 = lean_ctor_get(x_75, 11);
lean_inc(x_88);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 lean_ctor_release(x_75, 6);
 lean_ctor_release(x_75, 7);
 lean_ctor_release(x_75, 8);
 lean_ctor_release(x_75, 9);
 lean_ctor_release(x_75, 10);
 lean_ctor_release(x_75, 11);
 x_89 = x_75;
} else {
 lean_dec_ref(x_75);
 x_89 = lean_box(0);
}
x_90 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_91 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_70);
x_92 = l_Std_HashMap_insert___rarg(x_90, x_91, x_78, x_11, x_70);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(0, 12, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_79);
lean_ctor_set(x_93, 3, x_80);
lean_ctor_set(x_93, 4, x_81);
lean_ctor_set(x_93, 5, x_82);
lean_ctor_set(x_93, 6, x_83);
lean_ctor_set(x_93, 7, x_84);
lean_ctor_set(x_93, 8, x_85);
lean_ctor_set(x_93, 9, x_86);
lean_ctor_set(x_93, 10, x_87);
lean_ctor_set(x_93, 11, x_88);
x_94 = lean_st_ref_set(x_3, x_93, x_76);
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
lean_ctor_set(x_97, 0, x_70);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_11);
lean_dec(x_7);
x_98 = lean_ctor_get(x_69, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_69, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_100 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_102; lean_object* x_103; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = lean_ctor_get(x_68, 0);
lean_inc(x_102);
lean_dec(x_68);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_66);
return x_103;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_158; 
x_111 = lean_ctor_get(x_9, 0);
x_112 = lean_ctor_get(x_9, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_9);
x_158 = l_Lean_Expr_hasLevelParam(x_111);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = l_Lean_Expr_hasFVar(x_111);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasMVar(x_111);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_111);
lean_ctor_set(x_161, 1, x_112);
return x_161;
}
else
{
lean_object* x_162; 
x_162 = lean_box(0);
x_113 = x_162;
goto block_157;
}
}
else
{
lean_object* x_163; 
x_163 = lean_box(0);
x_113 = x_163;
goto block_157;
}
}
else
{
lean_object* x_164; 
x_164 = lean_box(0);
x_113 = x_164;
goto block_157;
}
block_157:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_113);
x_114 = lean_st_ref_get(x_7, x_112);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_st_ref_get(x_3, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
lean_inc(x_111);
x_121 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_120, x_111);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
lean_dec(x_119);
lean_inc(x_7);
lean_inc(x_111);
x_122 = l_Lean_Meta_Closure_collectExprAux(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_118);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_get(x_7, x_124);
lean_dec(x_7);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_take(x_3, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_128, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 5);
lean_inc(x_135);
x_136 = lean_ctor_get(x_128, 6);
lean_inc(x_136);
x_137 = lean_ctor_get(x_128, 7);
lean_inc(x_137);
x_138 = lean_ctor_get(x_128, 8);
lean_inc(x_138);
x_139 = lean_ctor_get(x_128, 9);
lean_inc(x_139);
x_140 = lean_ctor_get(x_128, 10);
lean_inc(x_140);
x_141 = lean_ctor_get(x_128, 11);
lean_inc(x_141);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 lean_ctor_release(x_128, 5);
 lean_ctor_release(x_128, 6);
 lean_ctor_release(x_128, 7);
 lean_ctor_release(x_128, 8);
 lean_ctor_release(x_128, 9);
 lean_ctor_release(x_128, 10);
 lean_ctor_release(x_128, 11);
 x_142 = x_128;
} else {
 lean_dec_ref(x_128);
 x_142 = lean_box(0);
}
x_143 = l_Lean_ExprStructEq_instBEqExprStructEq;
x_144 = l_Lean_ExprStructEq_instHashableExprStructEq;
lean_inc(x_123);
x_145 = l_Std_HashMap_insert___rarg(x_143, x_144, x_131, x_111, x_123);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 12, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_130);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_132);
lean_ctor_set(x_146, 3, x_133);
lean_ctor_set(x_146, 4, x_134);
lean_ctor_set(x_146, 5, x_135);
lean_ctor_set(x_146, 6, x_136);
lean_ctor_set(x_146, 7, x_137);
lean_ctor_set(x_146, 8, x_138);
lean_ctor_set(x_146, 9, x_139);
lean_ctor_set(x_146, 10, x_140);
lean_ctor_set(x_146, 11, x_141);
x_147 = lean_st_ref_set(x_3, x_146, x_129);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_123);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_111);
lean_dec(x_7);
x_151 = lean_ctor_get(x_122, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_122, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_153 = x_122;
} else {
 lean_dec_ref(x_122);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_155 = lean_ctor_get(x_121, 0);
lean_inc(x_155);
lean_dec(x_121);
if (lean_is_scalar(x_119)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_119;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_118);
return x_156;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_165 = !lean_is_exclusive(x_9);
if (x_165 == 0)
{
return x_9;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_9, 0);
x_167 = lean_ctor_get(x_9, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_9);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_19, 11);
x_23 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_24 = l_Array_back___rarg(x_23, x_22);
x_25 = lean_array_pop(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_26, x_25, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_19, 11, x_29);
x_31 = lean_st_ref_set(x_1, x_19, x_20);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
x_38 = lean_ctor_get(x_19, 2);
x_39 = lean_ctor_get(x_19, 3);
x_40 = lean_ctor_get(x_19, 4);
x_41 = lean_ctor_get(x_19, 5);
x_42 = lean_ctor_get(x_19, 6);
x_43 = lean_ctor_get(x_19, 7);
x_44 = lean_ctor_get(x_19, 8);
x_45 = lean_ctor_get(x_19, 9);
x_46 = lean_ctor_get(x_19, 10);
x_47 = lean_ctor_get(x_19, 11);
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
lean_dec(x_19);
x_48 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_49 = l_Array_back___rarg(x_48, x_47);
x_50 = lean_array_pop(x_47);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_51, x_50, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_38);
lean_ctor_set(x_56, 3, x_39);
lean_ctor_set(x_56, 4, x_40);
lean_ctor_set(x_56, 5, x_41);
lean_ctor_set(x_56, 6, x_42);
lean_ctor_set(x_56, 7, x_43);
lean_ctor_set(x_56, 8, x_44);
lean_ctor_set(x_56, 9, x_45);
lean_ctor_set(x_56, 10, x_46);
lean_ctor_set(x_56, 11, x_54);
x_57 = lean_st_ref_set(x_1, x_56, x_20);
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
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_7);
x_61 = lean_box(0);
lean_ctor_set(x_10, 0, x_61);
return x_10;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_10, 0);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_10);
x_64 = lean_ctor_get(x_62, 11);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Array_isEmpty___rarg(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_66 = lean_st_ref_get(x_5, x_63);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_take(x_1, x_67);
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
x_84 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_85 = l_Array_back___rarg(x_84, x_82);
x_86 = lean_array_pop(x_82);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Meta_Closure_pickNextToProcessAux(x_7, x_87, x_86, x_85);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_89);
if (lean_is_scalar(x_83)) {
 x_92 = lean_alloc_ctor(0, 12, 0);
} else {
 x_92 = x_83;
}
lean_ctor_set(x_92, 0, x_71);
lean_ctor_set(x_92, 1, x_72);
lean_ctor_set(x_92, 2, x_73);
lean_ctor_set(x_92, 3, x_74);
lean_ctor_set(x_92, 4, x_75);
lean_ctor_set(x_92, 5, x_76);
lean_ctor_set(x_92, 6, x_77);
lean_ctor_set(x_92, 7, x_78);
lean_ctor_set(x_92, 8, x_79);
lean_ctor_set(x_92, 9, x_80);
lean_ctor_set(x_92, 10, x_81);
lean_ctor_set(x_92, 11, x_90);
x_93 = lean_st_ref_set(x_1, x_92, x_70);
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
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_7);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_63);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Closure_pickNextToProcess_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_1);
x_10 = l_Lean_replaceFVarIdAtLocalDecl(x_1, x_2, x_7);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
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
x_46 = l_Std_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_44, x_18);
lean_dec(x_44);
if (lean_obj_tag(x_46) == 0)
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
lean_dec(x_46);
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
lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_79, 5);
x_83 = lean_array_get_size(x_82);
x_84 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_85 = 0;
x_86 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_84, x_85, x_82);
lean_dec(x_62);
lean_ctor_set(x_79, 5, x_86);
x_87 = lean_st_ref_set(x_2, x_79, x_80);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_7 = x_88;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_90 = lean_ctor_get(x_79, 0);
x_91 = lean_ctor_get(x_79, 1);
x_92 = lean_ctor_get(x_79, 2);
x_93 = lean_ctor_get(x_79, 3);
x_94 = lean_ctor_get(x_79, 4);
x_95 = lean_ctor_get(x_79, 5);
x_96 = lean_ctor_get(x_79, 6);
x_97 = lean_ctor_get(x_79, 7);
x_98 = lean_ctor_get(x_79, 8);
x_99 = lean_ctor_get(x_79, 9);
x_100 = lean_ctor_get(x_79, 10);
x_101 = lean_ctor_get(x_79, 11);
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
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_79);
x_102 = lean_array_get_size(x_95);
x_103 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_104 = 0;
x_105 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_103, x_104, x_95);
lean_dec(x_62);
x_106 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_106, 0, x_90);
lean_ctor_set(x_106, 1, x_91);
lean_ctor_set(x_106, 2, x_92);
lean_ctor_set(x_106, 3, x_93);
lean_ctor_set(x_106, 4, x_94);
lean_ctor_set(x_106, 5, x_105);
lean_ctor_set(x_106, 6, x_96);
lean_ctor_set(x_106, 7, x_97);
lean_ctor_set(x_106, 8, x_98);
lean_ctor_set(x_106, 9, x_99);
lean_ctor_set(x_106, 10, x_100);
lean_ctor_set(x_106, 11, x_101);
x_107 = lean_st_ref_set(x_2, x_106, x_80);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_7 = x_108;
goto _start;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; size_t x_147; size_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_110 = lean_ctor_get(x_67, 0);
x_111 = lean_ctor_get(x_67, 1);
x_112 = lean_ctor_get(x_67, 2);
x_113 = lean_ctor_get(x_67, 3);
x_114 = lean_ctor_get(x_67, 4);
x_115 = lean_ctor_get(x_67, 5);
x_116 = lean_ctor_get(x_67, 6);
x_117 = lean_ctor_get(x_67, 7);
x_118 = lean_ctor_get(x_67, 8);
x_119 = lean_ctor_get(x_67, 9);
x_120 = lean_ctor_get(x_67, 10);
x_121 = lean_ctor_get(x_67, 11);
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
lean_dec(x_67);
x_122 = lean_unsigned_to_nat(0u);
x_123 = 0;
lean_inc(x_62);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_62);
lean_ctor_set(x_21, 3, x_59);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_122);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_123);
x_124 = lean_array_push(x_117, x_21);
x_125 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_125, 0, x_110);
lean_ctor_set(x_125, 1, x_111);
lean_ctor_set(x_125, 2, x_112);
lean_ctor_set(x_125, 3, x_113);
lean_ctor_set(x_125, 4, x_114);
lean_ctor_set(x_125, 5, x_115);
lean_ctor_set(x_125, 6, x_116);
lean_ctor_set(x_125, 7, x_124);
lean_ctor_set(x_125, 8, x_118);
lean_ctor_set(x_125, 9, x_119);
lean_ctor_set(x_125, 10, x_120);
lean_ctor_set(x_125, 11, x_121);
x_126 = lean_st_ref_set(x_2, x_125, x_68);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_st_ref_get(x_6, x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_2, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_131, 6);
lean_inc(x_139);
x_140 = lean_ctor_get(x_131, 7);
lean_inc(x_140);
x_141 = lean_ctor_get(x_131, 8);
lean_inc(x_141);
x_142 = lean_ctor_get(x_131, 9);
lean_inc(x_142);
x_143 = lean_ctor_get(x_131, 10);
lean_inc(x_143);
x_144 = lean_ctor_get(x_131, 11);
lean_inc(x_144);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 lean_ctor_release(x_131, 6);
 lean_ctor_release(x_131, 7);
 lean_ctor_release(x_131, 8);
 lean_ctor_release(x_131, 9);
 lean_ctor_release(x_131, 10);
 lean_ctor_release(x_131, 11);
 x_145 = x_131;
} else {
 lean_dec_ref(x_131);
 x_145 = lean_box(0);
}
x_146 = lean_array_get_size(x_138);
x_147 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_148 = 0;
x_149 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_62, x_147, x_148, x_138);
lean_dec(x_62);
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(0, 12, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_133);
lean_ctor_set(x_150, 1, x_134);
lean_ctor_set(x_150, 2, x_135);
lean_ctor_set(x_150, 3, x_136);
lean_ctor_set(x_150, 4, x_137);
lean_ctor_set(x_150, 5, x_149);
lean_ctor_set(x_150, 6, x_139);
lean_ctor_set(x_150, 7, x_140);
lean_ctor_set(x_150, 8, x_141);
lean_ctor_set(x_150, 9, x_142);
lean_ctor_set(x_150, 10, x_143);
lean_ctor_set(x_150, 11, x_144);
x_151 = lean_st_ref_set(x_2, x_150, x_132);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_7 = x_152;
goto _start;
}
}
else
{
uint8_t x_154; 
lean_dec(x_59);
lean_free_object(x_21);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_61);
if (x_154 == 0)
{
return x_61;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_61, 0);
x_156 = lean_ctor_get(x_61, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_61);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_free_object(x_21);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = !lean_is_exclusive(x_58);
if (x_158 == 0)
{
return x_58;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_58, 0);
x_160 = lean_ctor_get(x_58, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_58);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_21, 2);
x_163 = lean_ctor_get(x_21, 3);
x_164 = lean_ctor_get(x_21, 4);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_21);
x_165 = l_Lean_Meta_getZetaFVarIds___rarg(x_4, x_5, x_6, x_36);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Std_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_166, x_18);
lean_dec(x_166);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; lean_object* x_170; 
lean_dec(x_164);
x_169 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_170 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_162, x_163, x_169, x_1, x_2, x_3, x_4, x_5, x_6, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Lean_mkFVar(x_18);
x_173 = l_Lean_Meta_Closure_pushFVarArg(x_172, x_1, x_2, x_3, x_4, x_5, x_6, x_171);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_7 = x_174;
goto _start;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_178 = x_170;
} else {
 lean_dec_ref(x_170);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; 
lean_dec(x_168);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_180 = l_Lean_Meta_Closure_collectExpr(x_163, x_1, x_2, x_3, x_4, x_5, x_6, x_167);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_183 = l_Lean_Meta_Closure_collectExpr(x_164, x_1, x_2, x_3, x_4, x_5, x_6, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; size_t x_230; size_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_st_ref_get(x_6, x_185);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_st_ref_take(x_2, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 5);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 6);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 7);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 8);
lean_inc(x_199);
x_200 = lean_ctor_get(x_189, 9);
lean_inc(x_200);
x_201 = lean_ctor_get(x_189, 10);
lean_inc(x_201);
x_202 = lean_ctor_get(x_189, 11);
lean_inc(x_202);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 lean_ctor_release(x_189, 6);
 lean_ctor_release(x_189, 7);
 lean_ctor_release(x_189, 8);
 lean_ctor_release(x_189, 9);
 lean_ctor_release(x_189, 10);
 lean_ctor_release(x_189, 11);
 x_203 = x_189;
} else {
 lean_dec_ref(x_189);
 x_203 = lean_box(0);
}
x_204 = lean_unsigned_to_nat(0u);
x_205 = 0;
lean_inc(x_184);
lean_inc(x_19);
x_206 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_19);
lean_ctor_set(x_206, 2, x_162);
lean_ctor_set(x_206, 3, x_181);
lean_ctor_set(x_206, 4, x_184);
lean_ctor_set_uint8(x_206, sizeof(void*)*5, x_205);
x_207 = lean_array_push(x_198, x_206);
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(0, 12, 0);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_191);
lean_ctor_set(x_208, 1, x_192);
lean_ctor_set(x_208, 2, x_193);
lean_ctor_set(x_208, 3, x_194);
lean_ctor_set(x_208, 4, x_195);
lean_ctor_set(x_208, 5, x_196);
lean_ctor_set(x_208, 6, x_197);
lean_ctor_set(x_208, 7, x_207);
lean_ctor_set(x_208, 8, x_199);
lean_ctor_set(x_208, 9, x_200);
lean_ctor_set(x_208, 10, x_201);
lean_ctor_set(x_208, 11, x_202);
x_209 = lean_st_ref_set(x_2, x_208, x_190);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_st_ref_get(x_6, x_210);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_st_ref_take(x_2, x_212);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_214, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 4);
lean_inc(x_220);
x_221 = lean_ctor_get(x_214, 5);
lean_inc(x_221);
x_222 = lean_ctor_get(x_214, 6);
lean_inc(x_222);
x_223 = lean_ctor_get(x_214, 7);
lean_inc(x_223);
x_224 = lean_ctor_get(x_214, 8);
lean_inc(x_224);
x_225 = lean_ctor_get(x_214, 9);
lean_inc(x_225);
x_226 = lean_ctor_get(x_214, 10);
lean_inc(x_226);
x_227 = lean_ctor_get(x_214, 11);
lean_inc(x_227);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 lean_ctor_release(x_214, 5);
 lean_ctor_release(x_214, 6);
 lean_ctor_release(x_214, 7);
 lean_ctor_release(x_214, 8);
 lean_ctor_release(x_214, 9);
 lean_ctor_release(x_214, 10);
 lean_ctor_release(x_214, 11);
 x_228 = x_214;
} else {
 lean_dec_ref(x_214);
 x_228 = lean_box(0);
}
x_229 = lean_array_get_size(x_221);
x_230 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_231 = 0;
x_232 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_19, x_184, x_230, x_231, x_221);
lean_dec(x_184);
if (lean_is_scalar(x_228)) {
 x_233 = lean_alloc_ctor(0, 12, 0);
} else {
 x_233 = x_228;
}
lean_ctor_set(x_233, 0, x_216);
lean_ctor_set(x_233, 1, x_217);
lean_ctor_set(x_233, 2, x_218);
lean_ctor_set(x_233, 3, x_219);
lean_ctor_set(x_233, 4, x_220);
lean_ctor_set(x_233, 5, x_232);
lean_ctor_set(x_233, 6, x_222);
lean_ctor_set(x_233, 7, x_223);
lean_ctor_set(x_233, 8, x_224);
lean_ctor_set(x_233, 9, x_225);
lean_ctor_set(x_233, 10, x_226);
lean_ctor_set(x_233, 11, x_227);
x_234 = lean_st_ref_set(x_2, x_233, x_215);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_7 = x_235;
goto _start;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_181);
lean_dec(x_162);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_237 = lean_ctor_get(x_183, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_183, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_239 = x_183;
} else {
 lean_dec_ref(x_183);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_241 = lean_ctor_get(x_180, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_180, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_243 = x_180;
} else {
 lean_dec_ref(x_180);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_245 = !lean_is_exclusive(x_20);
if (x_245 == 0)
{
return x_20;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_20, 0);
x_247 = lean_ctor_get(x_20, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_20);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_process___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_LocalDecl_toExpr(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_usize_of_nat(x_4);
x_6 = 0;
lean_inc(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_5, x_6, x_2);
x_8 = lean_expr_abstract(x_3, x_7);
lean_dec(x_3);
x_9 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2(x_1, x_2, x_7, x_4, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkBinding___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_Closure_mkBinding(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
x_5 = 0;
lean_inc(x_1);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_1);
x_7 = lean_expr_abstract(x_2, x_6);
lean_dec(x_2);
x_8 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_6, x_3, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkLambda___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
x_5 = 0;
lean_inc(x_1);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_4, x_5, x_1);
x_7 = lean_expr_abstract(x_2, x_6);
lean_dec(x_2);
x_8 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_6, x_3, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev_loop___at_Lean_Meta_Closure_mkForall___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get_uint8(x_11, 0);
x_43 = lean_ctor_get_uint8(x_11, 1);
x_44 = lean_ctor_get_uint8(x_11, 2);
x_45 = lean_ctor_get_uint8(x_11, 3);
x_46 = lean_ctor_get_uint8(x_11, 4);
x_47 = lean_ctor_get_uint8(x_11, 5);
x_48 = lean_ctor_get_uint8(x_11, 6);
x_49 = lean_ctor_get_uint8(x_11, 8);
x_50 = lean_ctor_get_uint8(x_11, 9);
x_51 = lean_ctor_get_uint8(x_11, 10);
x_52 = lean_ctor_get_uint8(x_11, 11);
x_53 = lean_ctor_get_uint8(x_11, 12);
x_54 = lean_ctor_get_uint8(x_11, 13);
lean_dec(x_11);
x_55 = 1;
x_56 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_56, 0, x_42);
lean_ctor_set_uint8(x_56, 1, x_43);
lean_ctor_set_uint8(x_56, 2, x_44);
lean_ctor_set_uint8(x_56, 3, x_45);
lean_ctor_set_uint8(x_56, 4, x_46);
lean_ctor_set_uint8(x_56, 5, x_47);
lean_ctor_set_uint8(x_56, 6, x_48);
lean_ctor_set_uint8(x_56, 7, x_55);
lean_ctor_set_uint8(x_56, 8, x_49);
lean_ctor_set_uint8(x_56, 9, x_50);
lean_ctor_set_uint8(x_56, 10, x_51);
lean_ctor_set_uint8(x_56, 11, x_52);
lean_ctor_set_uint8(x_56, 12, x_53);
lean_ctor_set_uint8(x_56, 13, x_54);
lean_ctor_set(x_5, 0, x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_60 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Closure_process(x_3, x_4, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_61);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
lean_dec(x_58);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_70 = x_63;
} else {
 lean_dec_ref(x_63);
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
lean_dec(x_58);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_72 = lean_ctor_get(x_60, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_74 = x_60;
} else {
 lean_dec_ref(x_60);
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
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_78 = x_57;
} else {
 lean_dec_ref(x_57);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_80 = lean_ctor_get(x_5, 1);
x_81 = lean_ctor_get(x_5, 2);
x_82 = lean_ctor_get(x_5, 3);
x_83 = lean_ctor_get(x_5, 4);
x_84 = lean_ctor_get(x_5, 5);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_5);
x_85 = lean_ctor_get_uint8(x_11, 0);
x_86 = lean_ctor_get_uint8(x_11, 1);
x_87 = lean_ctor_get_uint8(x_11, 2);
x_88 = lean_ctor_get_uint8(x_11, 3);
x_89 = lean_ctor_get_uint8(x_11, 4);
x_90 = lean_ctor_get_uint8(x_11, 5);
x_91 = lean_ctor_get_uint8(x_11, 6);
x_92 = lean_ctor_get_uint8(x_11, 8);
x_93 = lean_ctor_get_uint8(x_11, 9);
x_94 = lean_ctor_get_uint8(x_11, 10);
x_95 = lean_ctor_get_uint8(x_11, 11);
x_96 = lean_ctor_get_uint8(x_11, 12);
x_97 = lean_ctor_get_uint8(x_11, 13);
if (lean_is_exclusive(x_11)) {
 x_98 = x_11;
} else {
 lean_dec_ref(x_11);
 x_98 = lean_box(0);
}
x_99 = 1;
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 0, 14);
} else {
 x_100 = x_98;
}
lean_ctor_set_uint8(x_100, 0, x_85);
lean_ctor_set_uint8(x_100, 1, x_86);
lean_ctor_set_uint8(x_100, 2, x_87);
lean_ctor_set_uint8(x_100, 3, x_88);
lean_ctor_set_uint8(x_100, 4, x_89);
lean_ctor_set_uint8(x_100, 5, x_90);
lean_ctor_set_uint8(x_100, 6, x_91);
lean_ctor_set_uint8(x_100, 7, x_99);
lean_ctor_set_uint8(x_100, 8, x_92);
lean_ctor_set_uint8(x_100, 9, x_93);
lean_ctor_set_uint8(x_100, 10, x_94);
lean_ctor_set_uint8(x_100, 11, x_95);
lean_ctor_set_uint8(x_100, 12, x_96);
lean_ctor_set_uint8(x_100, 13, x_97);
x_101 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_80);
lean_ctor_set(x_101, 2, x_81);
lean_ctor_set(x_101, 3, x_82);
lean_ctor_set(x_101, 4, x_83);
lean_ctor_set(x_101, 5, x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_101);
x_102 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_101, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_101);
x_105 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_101, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_Closure_process(x_3, x_4, x_101, x_6, x_7, x_8, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_106);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_106);
lean_dec(x_103);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_115 = x_108;
} else {
 lean_dec_ref(x_108);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_117 = lean_ctor_get(x_105, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_119 = x_105;
} else {
 lean_dec_ref(x_105);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_123 = x_102;
} else {
 lean_dec_ref(x_102);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_29 = lean_ctor_get(x_22, 7);
lean_inc(x_29);
x_30 = l_Array_reverse___rarg(x_29);
lean_inc(x_30);
x_31 = l_Lean_Meta_Closure_mkForall(x_30, x_23);
lean_inc(x_28);
x_32 = l_Lean_Meta_Closure_mkForall(x_28, x_31);
x_33 = l_Lean_Meta_Closure_mkLambda(x_30, x_24);
x_34 = l_Lean_Meta_Closure_mkLambda(x_28, x_33);
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
x_50 = lean_ctor_get(x_42, 7);
lean_inc(x_50);
x_51 = l_Array_reverse___rarg(x_50);
lean_inc(x_51);
x_52 = l_Lean_Meta_Closure_mkForall(x_51, x_44);
lean_inc(x_49);
x_53 = l_Lean_Meta_Closure_mkForall(x_49, x_52);
x_54 = l_Lean_Meta_Closure_mkLambda(x_51, x_45);
x_55 = l_Lean_Meta_Closure_mkLambda(x_49, x_54);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_1);
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
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_is_aux_recursor(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_3);
x_5 = l_Lean_isRecCore(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_7, x_3);
lean_dec(x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
else
{
uint8_t x_11; 
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_13 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_12, x_3);
lean_dec(x_3);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_inc(x_3);
x_16 = l_Lean_isRecCore(x_1, x_3);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = 0;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_19 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_18, x_3);
lean_dec(x_3);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
return x_22;
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Meta_mkAuxDefinition___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_1);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_7);
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
x_28 = lean_uint32_add(x_26, x_27);
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
x_62 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_6, x_8, x_9, x_10, x_11, x_61);
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
x_51 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_6, x_50, x_8, x_9, x_10, x_11, x_36);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_mkAuxDefinition___lambda__2(x_34, x_14, x_4, x_5, x_52, x_8, x_9, x_10, x_11, x_53);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_40 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_11, x_6, x_7, x_8, x_9, x_39);
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
x_28 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_11, x_27, x_6, x_7, x_8, x_9, x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_mkAuxDefinition___lambda__3(x_2, x_3, x_4, x_1, x_5, x_11, x_29, x_6, x_7, x_8, x_9, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_mkAuxDefinition___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_mkAuxDefinition___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkAuxDefinition___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_mkAuxDefinition___lambda__3(x_1, x_2, x_13, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_headBeta(x_10);
x_13 = 1;
x_14 = l_Lean_Meta_mkAuxDefinition(x_1, x_12, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_mkAuxDefinitionFor(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
LEAN_EXPORT lean_object* initialize_Lean_Meta_Closure(lean_object* w) {
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
