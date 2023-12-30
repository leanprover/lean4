// Lean compiler output
// Module: Lean.Compiler.LCNF.Specialize
// Imports: Init Lean.Compiler.Specialize Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.SpecInfo Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.Level Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.MonadScope Lean.Compiler.LCNF.Closure Lean.Compiler.LCNF.FVarUtil
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
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__4;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__2;
static lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__18;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__10;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__15;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__3;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__13;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4;
static lean_object* l_Lean_Compiler_LCNF_specialize___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__1;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__12(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_FunDeclCore_toExprM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2;
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__11;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__8;
lean_object* l_Lean_Compiler_LCNF_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_LCtx_addFunDecl___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specCacheExt;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_specialize___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Context_ground___default;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabitedSMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__4;
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_specialize___closed__3;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Context_scope___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__9;
lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_saveSpecParamInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_addEntry(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4;
lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__8;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_list_to_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1;
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2;
lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__17;
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3;
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__10;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__6;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7;
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1;
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getSpecParamInfoCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__3;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__12;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__14;
lean_object* l_Lean_RBTree_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__9;
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10;
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_allFVar___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_specialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonadOptionT___rarg(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___boxed(lean_object**);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Id_instMonadId;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_State_decls___default;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__7;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__6;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__5;
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_toExpr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1(size_t, size_t, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize;
static lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__2;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_addEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__12(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_Specialize_addEntry(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__2(x_6, x_15, x_16, x_4);
lean_dec(x_6);
x_2 = x_11;
x_4 = x_17;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__3(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__1;
x_3 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__5;
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__1(x_2, x_1);
x_4 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Specialize", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("specCacheExt", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2;
x_3 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3;
x_4 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__4;
x_5 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_list_to_array), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_addEntry), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__6;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__8;
x_3 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__9;
x_4 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__10;
x_3 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specCacheExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 4);
lean_dec(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_14 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_13, x_10, x_12);
x_15 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__3;
lean_ctor_set(x_7, 4, x_15);
lean_ctor_set(x_7, 0, x_14);
x_16 = lean_st_ref_set(x_4, x_7, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
x_27 = lean_ctor_get(x_7, 5);
x_28 = lean_ctor_get(x_7, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
x_30 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_31 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_30, x_23, x_29);
x_32 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__3;
x_33 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_27);
lean_ctor_set(x_33, 6, x_28);
x_34 = lean_st_ref_set(x_4, x_33, x_8);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Specialize_cacheSpec(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = l_Lean_SMap_instInhabitedSMap___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1;
x_10 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_11 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_9, x_10, x_8);
lean_dec(x_8);
x_12 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(x_11, x_1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1;
x_17 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_18 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_16, x_17, x_15);
lean_dec(x_15);
x_19 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Context_scope___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Context_ground___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_State_decls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_apply_1(x_2, x_12);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_18 = lean_apply_1(x_2, x_15);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_apply_7(x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__2), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__1;
x_2 = l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__3;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_read___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_instMonadId;
x_2 = l_OptionT_instMonadOptionT___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_allFVar___spec__2), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), x_6, x_5, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 1;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg(x_1, x_11, x_2);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Specialize_isGround___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.FVarUtil", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Expr.forFVarM", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2;
x_2 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3;
x_3 = lean_unsigned_to_nat(42u);
x_4 = lean_unsigned_to_nat(38u);
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5;
x_6 = l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6(x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5(x_1, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_dec(x_9);
x_2 = x_8;
goto _start;
}
}
case 6:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5(x_1, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_dec(x_14);
x_2 = x_13;
goto _start;
}
}
case 7:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_dec(x_2);
lean_inc(x_1);
x_19 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5(x_1, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_1);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_dec(x_19);
x_2 = x_18;
goto _start;
}
}
case 8:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5;
x_23 = l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6(x_22);
return x_23;
}
case 11:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5;
x_25 = l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6(x_24);
return x_25;
}
default: 
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5(x_1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__4(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__4(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7(x_1, x_5, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_1);
x_18 = lean_apply_1(x_1, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_18);
x_20 = lean_array_get_size(x_17);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_1);
x_23 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_20, x_20);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_1);
x_25 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8(x_1, x_17, x_26, x_27, x_28);
lean_dec(x_17);
return x_29;
}
}
}
}
default: 
{
lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
return x_30;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_allFVar___spec__2), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__3(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_3);
x_11 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_box(0);
lean_inc(x_14);
x_19 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_16, x_14, x_18);
x_20 = lean_unbox(x_12);
lean_dec(x_12);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_19);
x_21 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_17, x_14, x_18);
lean_ctor_set(x_3, 1, x_22);
lean_ctor_set(x_3, 0, x_19);
x_23 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_box(0);
lean_inc(x_14);
x_28 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_24, x_14, x_27);
x_29 = lean_unbox(x_12);
lean_dec(x_12);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_apply_7(x_2, x_30, x_4, x_5, x_6, x_7, x_8, x_13);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_25, x_14, x_27);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_26);
x_34 = lean_apply_7(x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_13);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_withLetDecl___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_LCtx_addFunDecl___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_25; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_4);
x_16 = x_32;
x_17 = x_11;
goto block_24;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_26, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_array_fget(x_28, x_29);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_29, x_38);
lean_dec(x_29);
lean_ctor_set(x_26, 1, x_39);
x_40 = lean_box(x_15);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = lean_array_push(x_27, x_41);
lean_ctor_set(x_4, 1, x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_4);
x_16 = x_43;
x_17 = x_11;
goto block_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
lean_inc(x_37);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_37);
x_45 = lean_array_push(x_27, x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l_Lean_Compiler_LCNF_Closure_collectArg(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_ctor_set(x_4, 1, x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_4);
x_16 = x_48;
x_17 = x_47;
goto block_24;
}
else
{
uint8_t x_49; 
lean_dec(x_45);
lean_dec(x_26);
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_26);
x_53 = lean_array_fget(x_28, x_29);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_29, x_54);
lean_dec(x_29);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_28);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_30);
x_57 = lean_box(x_15);
if (lean_obj_tag(x_57) == 4)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = lean_array_push(x_27, x_58);
lean_ctor_set(x_4, 1, x_59);
lean_ctor_set(x_4, 0, x_56);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_4);
x_16 = x_60;
x_17 = x_11;
goto block_24;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
lean_inc(x_53);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_53);
x_62 = lean_array_push(x_27, x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_63 = l_Lean_Compiler_LCNF_Closure_collectArg(x_53, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_ctor_set(x_4, 1, x_62);
lean_ctor_set(x_4, 0, x_56);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_4);
x_16 = x_65;
x_17 = x_64;
goto block_24;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_56);
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
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
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_4, 0);
x_71 = lean_ctor_get(x_4, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_4);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
x_75 = lean_nat_dec_lt(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_71);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_16 = x_77;
x_17 = x_11;
goto block_24;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
x_79 = lean_array_fget(x_72, x_73);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_73, x_80);
lean_dec(x_73);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 3, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_74);
x_83 = lean_box(x_15);
if (lean_obj_tag(x_83) == 4)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_79);
x_84 = lean_box(0);
x_85 = lean_array_push(x_71, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_16 = x_87;
x_17 = x_11;
goto block_24;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_83);
lean_inc(x_79);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_79);
x_89 = lean_array_push(x_71, x_88);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_90 = l_Lean_Compiler_LCNF_Closure_collectArg(x_79, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_89);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_16 = x_93;
x_17 = x_91;
goto block_24;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_82);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_20;
x_11 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__3___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1___boxed), 3, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_3);
x_15 = lean_array_get_size(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_toSubarray___rarg(x_2, x_16, x_15);
x_18 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_get_size(x_1);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_box_usize(x_21);
x_23 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1;
x_24 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___boxed), 11, 4);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_19);
x_25 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__3___rarg), 9, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
lean_dec(x_3);
x_28 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2;
x_29 = lean_alloc_closure((void*)(l_Lean_RBTree_contains___rarg___boxed), 3, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_27);
x_30 = l_Lean_Compiler_LCNF_Closure_run___rarg(x_26, x_29, x_14, x_5, x_6, x_7, x_8, x_12);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Specialize_Collector_collect(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_allFVar___spec__2), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__4(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_26; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_5);
x_17 = x_33;
x_18 = x_12;
goto block_25;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_27, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_array_fget(x_29, x_30);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_30, x_39);
lean_dec(x_30);
lean_ctor_set(x_27, 1, x_40);
x_41 = lean_box(x_16);
switch (lean_obj_tag(x_41)) {
case 1:
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_5, 0, x_42);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_5);
x_17 = x_43;
x_18 = x_12;
goto block_25;
}
case 2:
{
lean_object* x_44; 
lean_dec(x_38);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_5);
x_17 = x_44;
x_18 = x_12;
goto block_25;
}
case 4:
{
lean_object* x_45; 
lean_dec(x_38);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_5);
x_17 = x_45;
x_18 = x_12;
goto block_25;
}
default: 
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_41);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_5);
x_17 = x_50;
x_18 = x_49;
goto block_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_5, 0, x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_5);
x_17 = x_53;
x_18 = x_51;
goto block_25;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_27);
x_54 = lean_array_fget(x_29, x_30);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_30, x_55);
lean_dec(x_30);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_29);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_31);
x_58 = lean_box(x_16);
switch (lean_obj_tag(x_58)) {
case 1:
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
x_59 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_59);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_5);
x_17 = x_60;
x_18 = x_12;
goto block_25;
}
case 2:
{
lean_object* x_61; 
lean_dec(x_54);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_1);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_5);
x_17 = x_61;
x_18 = x_12;
goto block_25;
}
case 4:
{
lean_object* x_62; 
lean_dec(x_54);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_1);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_5);
x_17 = x_62;
x_18 = x_12;
goto block_25;
}
default: 
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_58);
lean_inc(x_6);
x_63 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_1);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_5);
x_17 = x_67;
x_18 = x_66;
goto block_25;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_69);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_5);
x_17 = x_70;
x_18 = x_68;
goto block_25;
}
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
lean_dec(x_5);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 2);
lean_inc(x_74);
x_75 = lean_nat_dec_lt(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_inc(x_1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_71);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_17 = x_77;
x_18 = x_12;
goto block_25;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
x_79 = lean_array_fget(x_72, x_73);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_73, x_80);
lean_dec(x_73);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 3, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_74);
x_83 = lean_box(x_16);
switch (lean_obj_tag(x_83)) {
case 1:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_79);
x_84 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_17 = x_86;
x_18 = x_12;
goto block_25;
}
case 2:
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_79);
lean_inc(x_1);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_82);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_17 = x_88;
x_18 = x_12;
goto block_25;
}
case 4:
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_79);
lean_inc(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_82);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_17 = x_90;
x_18 = x_12;
goto block_25;
}
default: 
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_83);
lean_inc(x_6);
x_91 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(x_79, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
lean_inc(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_82);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_17 = x_96;
x_18 = x_94;
goto block_25;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_dec(x_91);
x_98 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_82);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_17 = x_100;
x_18 = x_97;
goto block_25;
}
}
}
}
}
block_25:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = 1;
x_23 = lean_usize_add(x_4, x_22);
x_4 = x_23;
x_5 = x_21;
x_12 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_toSubarray___rarg(x_2, x_11, x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_3);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(x_13, x_1, x_16, x_17, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1;
x_23 = lean_box(0);
x_24 = lean_apply_8(x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_1);
x_9 = lean_expr_abstract(x_8, x_2);
lean_dec(x_8);
x_10 = lean_expr_instantiate_rev(x_9, x_5);
lean_dec(x_5);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_expr_abstract_range(x_11, x_4, x_2);
lean_dec(x_11);
x_13 = lean_expr_instantiate_rev(x_12, x_5);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_16 = lean_array_push(x_5, x_13);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_5);
lean_dec(x_5);
x_9 = l_Lean_Expr_fvar___override(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_11);
x_13 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_9;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_17 = l_Lean_Compiler_LCNF_FunDeclCore_toExpr(x_15, x_16);
x_18 = lean_array_uset(x_7, x_2, x_17);
x_2 = x_9;
x_3 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
lean_inc(x_1);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1(x_9, x_10, x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2(x_9, x_10, x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_15 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(x_2, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed), 3, 1);
lean_closure_set(x_7, 0, x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToExpr_mkLambdaM___boxed), 4, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_ReaderT_bind___at_Lean_Compiler_LCNF_FunDeclCore_toExprM___spec__1___rarg(x_7, x_8, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
lean_inc(x_5);
x_16 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_6, x_13, x_5);
x_17 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_4 = x_15;
x_5 = x_17;
x_6 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1(x_1, x_11, x_1, x_13, x_13, x_12);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_normLevelParams(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_21 = l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1(x_1, x_17, x_1, x_20, x_20, x_19);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Compiler_LCNF_normLevelParams(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_mkKey(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_25; 
x_15 = lean_array_uget(x_3, x_5);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_6);
x_16 = x_32;
x_17 = x_12;
goto block_24;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_26, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_array_fget(x_28, x_29);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_29, x_38);
lean_dec(x_29);
lean_ctor_set(x_26, 1, x_39);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_15, 2);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_inc(x_1);
x_43 = l_Lean_Expr_instantiateLevelParamsNoCache(x_41, x_42, x_1);
lean_ctor_set(x_15, 2, x_43);
x_44 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_15, x_7, x_8, x_9, x_10, x_11, x_12);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_push(x_27, x_45);
lean_ctor_set(x_6, 1, x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_6);
x_16 = x_48;
x_17 = x_46;
goto block_24;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_15, 0);
x_50 = lean_ctor_get(x_15, 1);
x_51 = lean_ctor_get(x_15, 2);
x_52 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_15);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
lean_inc(x_1);
x_54 = l_Lean_Expr_instantiateLevelParamsNoCache(x_51, x_53, x_1);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_52);
x_56 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_55, x_7, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_push(x_27, x_57);
lean_ctor_set(x_6, 1, x_59);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_6);
x_16 = x_60;
x_17 = x_58;
goto block_24;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
lean_dec(x_37);
x_62 = lean_st_ref_get(x_7, x_12);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = 1;
x_66 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_63, x_61, x_65);
x_67 = lean_st_ref_take(x_7, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_15, 0);
lean_inc(x_70);
lean_dec(x_15);
x_71 = l_Lean_Compiler_LCNF_Arg_toExpr(x_66);
x_72 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_68, x_70, x_71);
x_73 = lean_st_ref_set(x_7, x_72, x_69);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_6);
x_16 = x_75;
x_17 = x_74;
goto block_24;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_26);
x_76 = lean_array_fget(x_28, x_29);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_29, x_77);
lean_dec(x_29);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_28);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_30);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_80 = lean_ctor_get(x_15, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_15, 2);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_84 = x_15;
} else {
 lean_dec_ref(x_15);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_inc(x_1);
x_86 = l_Lean_Expr_instantiateLevelParamsNoCache(x_82, x_85, x_1);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 3, 1);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_83);
x_88 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_87, x_7, x_8, x_9, x_10, x_11, x_12);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_array_push(x_27, x_89);
lean_ctor_set(x_6, 1, x_91);
lean_ctor_set(x_6, 0, x_79);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_6);
x_16 = x_92;
x_17 = x_90;
goto block_24;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_93 = lean_ctor_get(x_76, 0);
lean_inc(x_93);
lean_dec(x_76);
x_94 = lean_st_ref_get(x_7, x_12);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = 1;
x_98 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_95, x_93, x_97);
x_99 = lean_st_ref_take(x_7, x_96);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_15, 0);
lean_inc(x_102);
lean_dec(x_15);
x_103 = l_Lean_Compiler_LCNF_Arg_toExpr(x_98);
x_104 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_100, x_102, x_103);
x_105 = lean_st_ref_set(x_7, x_104, x_101);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_ctor_set(x_6, 0, x_79);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_6);
x_16 = x_107;
x_17 = x_106;
goto block_24;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_108 = lean_ctor_get(x_6, 0);
x_109 = lean_ctor_get(x_6, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_6);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_nat_dec_lt(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_15);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_16 = x_115;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 x_116 = x_108;
} else {
 lean_dec_ref(x_108);
 x_116 = lean_box(0);
}
x_117 = lean_array_fget(x_110, x_111);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_111, x_118);
lean_dec(x_111);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 3, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_121 = lean_ctor_get(x_15, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_15, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_15, 2);
lean_inc(x_123);
x_124 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_125 = x_15;
} else {
 lean_dec_ref(x_15);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_inc(x_1);
x_127 = l_Lean_Expr_instantiateLevelParamsNoCache(x_123, x_126, x_1);
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(0, 3, 1);
} else {
 x_128 = x_125;
}
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_122);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set_uint8(x_128, sizeof(void*)*3, x_124);
x_129 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_128, x_7, x_8, x_9, x_10, x_11, x_12);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_array_push(x_109, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_120);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_16 = x_134;
x_17 = x_131;
goto block_24;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_135 = lean_ctor_get(x_117, 0);
lean_inc(x_135);
lean_dec(x_117);
x_136 = lean_st_ref_get(x_7, x_12);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = 1;
x_140 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_137, x_135, x_139);
x_141 = lean_st_ref_take(x_7, x_138);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_15, 0);
lean_inc(x_144);
lean_dec(x_15);
x_145 = l_Lean_Compiler_LCNF_Arg_toExpr(x_140);
x_146 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_142, x_144, x_145);
x_147 = lean_st_ref_set(x_7, x_146, x_143);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_120);
lean_ctor_set(x_149, 1, x_109);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_148;
goto block_24;
}
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_5, x_21);
x_5 = x_22;
x_6 = x_20;
x_12 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_array_uget(x_15, x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_18 = lean_ctor_get(x_16, 2);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_1);
x_20 = l_Lean_Expr_instantiateLevelParamsNoCache(x_18, x_19, x_1);
lean_ctor_set(x_16, 2, x_20);
x_21 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_16, x_7, x_8, x_9, x_10, x_11, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_push(x_6, x_22);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
x_5 = x_26;
x_6 = x_24;
x_12 = x_23;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_inc(x_1);
x_33 = l_Lean_Expr_instantiateLevelParamsNoCache(x_30, x_32, x_1);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_31);
x_35 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_34, x_7, x_8, x_9, x_10, x_11, x_12);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_array_push(x_6, x_36);
x_39 = 1;
x_40 = lean_usize_add(x_5, x_39);
x_5 = x_40;
x_6 = x_38;
x_12 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_14 = lean_array_get_size(x_3);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_15, x_16, x_3, x_8, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_4);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___spec__2(x_21, x_16, x_4, x_8, x_9, x_10, x_11, x_12, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_2);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_25);
x_27 = l_Array_toSubarray___rarg(x_2, x_26, x_25);
x_28 = lean_ctor_get(x_6, 3);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_18);
x_32 = lean_array_get_size(x_28);
x_33 = lean_usize_of_nat(x_32);
lean_inc(x_6);
lean_inc(x_1);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(x_1, x_6, x_28, x_33, x_16, x_31, x_8, x_9, x_10, x_11, x_12, x_24);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Array_toSubarray___rarg(x_28, x_25, x_32);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_1);
x_43 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(x_1, x_6, x_38, x_40, x_42, x_37, x_8, x_9, x_10, x_11, x_12, x_36);
lean_dec(x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_6);
x_46 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_6, x_1);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_6, 5);
lean_dec(x_48);
x_49 = lean_ctor_get(x_6, 4);
lean_dec(x_49);
x_50 = lean_ctor_get(x_6, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_6, 2);
lean_dec(x_51);
x_52 = lean_ctor_get(x_6, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_6, 0);
lean_dec(x_53);
x_54 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_46, x_8, x_9, x_10, x_11, x_12, x_45);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Compiler_LCNF_attachCodeDecls(x_23, x_55);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_57);
x_58 = l_Lean_Compiler_LCNF_Code_inferType(x_57, x_9, x_10, x_11, x_12, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_44);
x_61 = l_Lean_Compiler_LCNF_mkForallParams(x_44, x_59, x_9, x_10, x_11, x_12, x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_box(0);
lean_ctor_set(x_6, 5, x_64);
lean_ctor_set(x_6, 4, x_57);
lean_ctor_set(x_6, 3, x_44);
lean_ctor_set(x_6, 2, x_63);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_7);
x_65 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_6);
lean_ctor_set(x_61, 0, x_65);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_box(0);
lean_ctor_set(x_6, 5, x_68);
lean_ctor_set(x_6, 4, x_57);
lean_ctor_set(x_6, 3, x_44);
lean_ctor_set(x_6, 2, x_66);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_7);
x_69 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_6);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_57);
lean_free_object(x_6);
lean_dec(x_44);
lean_dec(x_7);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_61);
if (x_71 == 0)
{
return x_61;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_61, 0);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_61);
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
lean_dec(x_57);
lean_free_object(x_6);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
return x_58;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_58);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_6);
x_79 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_46, x_8, x_9, x_10, x_11, x_12, x_45);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Compiler_LCNF_attachCodeDecls(x_23, x_80);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_82);
x_83 = l_Lean_Compiler_LCNF_Code_inferType(x_82, x_9, x_10, x_11, x_12, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_44);
x_86 = l_Lean_Compiler_LCNF_mkForallParams(x_44, x_84, x_9, x_10, x_11, x_12, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_91, 0, x_7);
lean_ctor_set(x_91, 1, x_5);
lean_ctor_set(x_91, 2, x_87);
lean_ctor_set(x_91, 3, x_44);
lean_ctor_set(x_91, 4, x_82);
lean_ctor_set(x_91, 5, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*6, x_29);
lean_ctor_set_uint8(x_91, sizeof(void*)*6 + 1, x_30);
x_92 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_91);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_88);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_82);
lean_dec(x_44);
lean_dec(x_7);
lean_dec(x_5);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_82);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_83, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_100 = x_83;
} else {
 lean_dec_ref(x_83);
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
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_at_", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("spec", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2;
x_19 = l_Lean_Name_append(x_17, x_18);
x_20 = lean_ctor_get(x_7, 2);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_erase_macro_scopes(x_20);
x_22 = l_Lean_Name_append(x_19, x_21);
x_23 = lean_array_get_size(x_15);
lean_dec(x_15);
x_24 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4;
x_25 = lean_name_append_index_after(x_24, x_23);
x_26 = l_Lean_Name_append(x_22, x_25);
x_27 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__1;
x_28 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_27, x_9, x_10, x_11, x_12, x_16);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_mk_ref(x_27, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_29);
x_34 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(x_2, x_3, x_4, x_5, x_6, x_29, x_26, x_32, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_32, x_36);
lean_dec(x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Compiler_LCNF_eraseDecl(x_29, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_35);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_32);
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = l_Lean_Compiler_LCNF_eraseDecl(x_29, x_9, x_10, x_11, x_12, x_45);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_4;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_9, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_array_fget(x_11, x_12);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_12, x_20);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_21);
x_22 = lean_box(x_7);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_array_push(x_10, x_19);
lean_ctor_set(x_4, 1, x_23);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
goto _start;
}
else
{
size_t x_27; size_t x_28; 
lean_dec(x_22);
lean_dec(x_19);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
x_30 = lean_array_fget(x_11, x_12);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_12, x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_13);
x_34 = lean_box(x_7);
if (lean_obj_tag(x_34) == 4)
{
lean_object* x_35; size_t x_36; size_t x_37; 
x_35 = lean_array_push(x_10, x_30);
lean_ctor_set(x_4, 1, x_35);
lean_ctor_set(x_4, 0, x_33);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
goto _start;
}
else
{
size_t x_39; size_t x_40; 
lean_dec(x_34);
lean_dec(x_30);
lean_ctor_set(x_4, 0, x_33);
x_39 = 1;
x_40 = lean_usize_add(x_3, x_39);
x_3 = x_40;
goto _start;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
x_50 = lean_array_fget(x_44, x_45);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_45, x_51);
lean_dec(x_45);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 3, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_46);
x_54 = lean_box(x_7);
if (lean_obj_tag(x_54) == 4)
{
lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_55 = lean_array_push(x_43, x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_3, x_57);
x_3 = x_58;
x_4 = x_56;
goto _start;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; 
lean_dec(x_54);
lean_dec(x_50);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_43);
x_61 = 1;
x_62 = lean_usize_add(x_3, x_61);
x_3 = x_62;
x_4 = x_60;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_5 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_6 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
x_10 = 0;
x_11 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(x_1, x_9, x_10, x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_toSubarray___rarg(x_2, x_8, x_13);
x_15 = l_Array_ofSubarray___rarg(x_14);
x_16 = l_Array_append___rarg(x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_getSpecParamInfoCore_x3f(x_12, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_getSpecParamInfoCore_x3f(x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___closed__1;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_6, 2);
x_14 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_6, 2);
x_19 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_16, x_18, x_1);
lean_dec(x_16);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_push(x_4, x_10);
x_2 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__1;
x_3 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__2;
x_4 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_6, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_18);
x_20 = lean_ctor_get(x_7, 2);
x_21 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__3;
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
x_23 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_st_ref_take(x_8, x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_25, 3);
x_29 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_30 = 0;
x_31 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
lean_inc(x_10);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_PersistentArray_push___rarg(x_28, x_32);
lean_ctor_set(x_25, 3, x_33);
x_34 = lean_st_ref_set(x_8, x_25, x_26);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 2);
x_44 = lean_ctor_get(x_25, 3);
x_45 = lean_ctor_get(x_25, 4);
x_46 = lean_ctor_get(x_25, 5);
x_47 = lean_ctor_get(x_25, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_48 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_49 = 0;
x_50 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_23);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
lean_inc(x_10);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_PersistentArray_push___rarg(x_44, x_51);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_45);
lean_ctor_set(x_53, 5, x_46);
lean_ctor_set(x_53, 6, x_47);
x_54 = lean_st_ref_set(x_8, x_53, x_26);
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
x_57 = lean_box(0);
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
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1;
x_3 = l_instInhabited___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
lean_ctor_set_uint8(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
lean_ctor_set_uint8(x_2, 3, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_Specialize_cacheSpec(x_2, x_14, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_Decl_saveBase(x_1, x_11, x_12, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_1, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_20);
x_22 = l_Lean_Compiler_LCNF_Decl_saveBase(x_20, x_11, x_12, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Compiler_LCNF_Decl_simp(x_20, x_24, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Compiler_LCNF_Decl_simp(x_26, x_28, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 4);
lean_inc(x_34);
x_72 = lean_box(0);
x_73 = lean_array_get_size(x_33);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_32);
lean_inc(x_8);
x_77 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_34, x_76, x_8, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_35 = x_78;
x_36 = x_79;
goto block_71;
}
else
{
uint8_t x_80; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_le(x_73, x_73);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_73);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_72);
lean_ctor_set(x_85, 2, x_32);
lean_inc(x_8);
x_86 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_34, x_85, x_8, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_35 = x_87;
x_36 = x_88;
goto block_71;
}
else
{
uint8_t x_89; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_94 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_33, x_5, x_93, x_72);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_72);
lean_ctor_set(x_95, 2, x_32);
lean_inc(x_8);
x_96 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_34, x_95, x_8, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_35 = x_97;
x_36 = x_98;
goto block_71;
}
else
{
uint8_t x_99; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_96);
if (x_99 == 0)
{
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_96, 0);
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_96);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
block_71:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 4);
lean_dec(x_39);
x_40 = lean_ctor_get(x_30, 3);
lean_dec(x_40);
lean_inc(x_38);
lean_ctor_set(x_30, 4, x_35);
x_41 = lean_st_ref_take(x_8, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_array_push(x_42, x_30);
x_45 = lean_st_ref_set(x_8, x_44, x_43);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_3);
lean_ctor_set(x_48, 2, x_4);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_3);
lean_ctor_set(x_51, 2, x_4);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_30, 0);
x_55 = lean_ctor_get(x_30, 1);
x_56 = lean_ctor_get(x_30, 2);
x_57 = lean_ctor_get_uint8(x_30, sizeof(void*)*6);
x_58 = lean_ctor_get_uint8(x_30, sizeof(void*)*6 + 1);
x_59 = lean_ctor_get(x_30, 5);
lean_inc(x_59);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_30);
lean_inc(x_54);
x_60 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_33);
lean_ctor_set(x_60, 4, x_35);
lean_ctor_set(x_60, 5, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*6, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*6 + 1, x_58);
x_61 = lean_st_ref_take(x_8, x_36);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_array_push(x_62, x_60);
x_65 = lean_st_ref_set(x_8, x_64, x_63);
lean_dec(x_8);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_3);
lean_ctor_set(x_68, 2, x_4);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_29);
if (x_103 == 0)
{
return x_29;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_29, 0);
x_105 = lean_ctor_get(x_29, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_29);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_25);
if (x_107 == 0)
{
return x_25;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_25, 0);
x_109 = lean_ctor_get(x_25, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_25);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_19);
if (x_111 == 0)
{
return x_19;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_19, 0);
x_113 = lean_ctor_get(x_19, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_19);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("specialize", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("step", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("new: ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cached: ", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!key.hasFVar\n    ", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Specialize", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Specialize.specializeApp\?", 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14;
x_3 = lean_unsigned_to_nat(276u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!key.hasLooseBVars\n    ", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14;
x_3 = lean_unsigned_to_nat(275u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__17;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
lean_dec(x_10);
x_18 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasFVar(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_box(0);
lean_inc(x_2);
x_21 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_2, x_20);
x_22 = lean_array_get_size(x_3);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
lean_inc(x_3);
x_25 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_23, x_24, x_3);
x_26 = l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(x_4, x_5);
lean_dec(x_4);
x_27 = l_Array_append___rarg(x_25, x_26);
lean_inc(x_1);
x_28 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(x_1, x_15, x_16, x_17);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_31 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_6, x_7, x_8, x_3, x_9, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
x_35 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_32, x_1, x_21, x_27, x_24, x_39, x_11, x_12, x_13, x_14, x_15, x_16, x_38);
lean_dec(x_11);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
x_43 = l_Lean_MessageData_ofName(x_42);
x_44 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_34, x_47, x_11, x_12, x_13, x_14, x_15, x_16, x_41);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_32, x_1, x_21, x_27, x_24, x_49, x_11, x_12, x_13, x_14, x_15, x_16, x_50);
lean_dec(x_11);
lean_dec(x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_31);
if (x_52 == 0)
{
return x_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_31, 0);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_31);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_28, 1);
lean_inc(x_56);
lean_dec(x_28);
x_57 = lean_ctor_get(x_29, 0);
lean_inc(x_57);
lean_dec(x_29);
x_58 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
x_59 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_58, x_11, x_12, x_13, x_14, x_15, x_16, x_56);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_box(0);
x_64 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_57, x_21, x_27, x_63, x_11, x_12, x_13, x_14, x_15, x_16, x_62);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_inc(x_57);
x_66 = l_Lean_MessageData_ofName(x_57);
x_67 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_58, x_70, x_11, x_12, x_13, x_14, x_15, x_16, x_65);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_57, x_21, x_27, x_72, x_11, x_12, x_13, x_14, x_15, x_16, x_73);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15;
x_76 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_75, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__18;
x_78 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_77, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_78;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("key: ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Specialize_Collector_collect(x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_array_get_size(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3(x_19, x_23, x_22);
lean_inc(x_4);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_21);
lean_inc(x_20);
x_26 = l_Lean_Compiler_LCNF_Specialize_mkKey(x_20, x_21, x_25, x_10, x_11, x_12, x_13, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_5);
x_31 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_29, x_30, x_20, x_1, x_2, x_6, x_4, x_19, x_21, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
lean_inc(x_29);
x_38 = l_Lean_MessageData_ofExpr(x_29);
x_39 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_5, x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_29, x_30, x_20, x_1, x_2, x_6, x_4, x_19, x_21, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
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
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("candidate", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_getDecl_x3f(x_1, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2;
x_25 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(x_2, x_3, x_1, x_4, x_24, x_23, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_5);
x_33 = l_Lean_MessageData_ofExpr(x_32);
x_34 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_2);
x_38 = lean_array_to_list(lean_box(0), x_2);
x_39 = lean_box(0);
x_40 = l_List_mapTR_loop___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__12(x_38, x_39);
x_41 = l_Lean_MessageData_ofList(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
x_44 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_24, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(x_2, x_3, x_1, x_4, x_24, x_23, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_23 = l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(x_22, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5(x_1, x_22, x_2, x_3, x_4, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
lean_inc(x_1);
x_13 = l_Lean_Meta_isInstance(x_1, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = l_Array_isEmpty___rarg(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__7(x_9, x_11, x_10, x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_8(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_19 = lean_ptr_addr(x_16);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_array_fset(x_3, x_2, x_16);
lean_dec(x_2);
x_2 = x_22;
x_3 = x_23;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
x_10 = x_17;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__2(x_2, x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_4, 3);
lean_inc(x_27);
lean_inc(x_6);
x_28 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
x_35 = lean_box(0);
lean_inc(x_31);
x_36 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_33, x_31, x_35);
x_37 = lean_unbox(x_29);
lean_dec(x_29);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_31);
lean_ctor_set(x_6, 0, x_36);
lean_inc(x_1);
x_38 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_13 = x_39;
x_14 = x_40;
goto block_26;
}
else
{
uint8_t x_41; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_34, x_31, x_35);
lean_ctor_set(x_6, 1, x_45);
lean_ctor_set(x_6, 0, x_36);
lean_inc(x_1);
x_46 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_13 = x_47;
x_14 = x_48;
goto block_26;
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_6, 0);
x_54 = lean_ctor_get(x_6, 1);
x_55 = lean_ctor_get(x_6, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_6);
x_56 = lean_box(0);
lean_inc(x_31);
x_57 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_53, x_31, x_56);
x_58 = lean_unbox(x_29);
lean_dec(x_29);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_31);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set(x_59, 2, x_55);
lean_inc(x_1);
x_60 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_1, x_59, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_13 = x_61;
x_14 = x_62;
goto block_26;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_65 = x_60;
} else {
 lean_dec_ref(x_60);
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
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_54, x_31, x_56);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_55);
lean_inc(x_1);
x_69 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_1, x_68, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_13 = x_70;
x_14 = x_71;
goto block_26;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
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
block_26:
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_2);
x_21 = lean_ptr_addr(x_4);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_9);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_9);
x_16 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
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
x_28 = lean_nat_dec_le(x_13, x_13);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_9);
x_29 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_9, x_41, x_42, x_12);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_43);
x_44 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
x_59 = lean_array_get_size(x_9);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_9);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_58);
x_63 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_62, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_59, x_59);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_59);
lean_dec(x_9);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_58);
x_75 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_74, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_76);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_1);
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_87 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_9, x_85, x_86, x_56);
lean_dec(x_9);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_57);
lean_ctor_set(x_88, 2, x_58);
x_89 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_88, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_1);
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
x_100 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_99, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_102);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
return x_100;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_100, 0);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_100);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_visitCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__2), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_9);
x_16 = l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1(x_10, x_9, x_1, x_9, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
lean_inc(x_9);
x_19 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_9, x_18, x_4, x_5, x_6, x_7, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1(x_10, x_9, x_1, x_20, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_9);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
x_30 = l_Lean_Compiler_LCNF_Specialize_visitFunDecl(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_box(0);
x_37 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_35, x_33, x_36);
lean_ctor_set(x_2, 0, x_37);
lean_inc(x_29);
x_38 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; size_t x_41; size_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_42 = lean_ptr_addr(x_40);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_28);
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_dec(x_46);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_31);
lean_ctor_set(x_38, 0, x_1);
return x_38;
}
else
{
lean_object* x_47; 
lean_dec(x_1);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
}
else
{
size_t x_48; size_t x_49; uint8_t x_50; 
x_48 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_49 = lean_ptr_addr(x_31);
x_50 = lean_usize_dec_eq(x_48, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_1, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_1, 0);
lean_dec(x_53);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_31);
lean_ctor_set(x_38, 0, x_1);
return x_38;
}
else
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_31);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_38, 0, x_54);
return x_38;
}
}
else
{
lean_dec(x_40);
lean_dec(x_31);
lean_ctor_set(x_38, 0, x_1);
return x_38;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_58 = lean_ptr_addr(x_55);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_28);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_60 = x_1;
} else {
 lean_dec_ref(x_1);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_31);
lean_ctor_set(x_61, 1, x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
else
{
size_t x_63; size_t x_64; uint8_t x_65; 
x_63 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_64 = lean_ptr_addr(x_31);
x_65 = lean_usize_dec_eq(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_66 = x_1;
} else {
 lean_dec_ref(x_1);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_55);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_56);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_55);
lean_dec(x_31);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_56);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_38);
if (x_70 == 0)
{
return x_38;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_38, 0);
x_72 = lean_ctor_get(x_38, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_38);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_2, 0);
x_75 = lean_ctor_get(x_2, 1);
x_76 = lean_ctor_get(x_2, 2);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_2);
x_77 = lean_box(0);
x_78 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_74, x_33, x_77);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
lean_inc(x_29);
x_80 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_29, x_79, x_3, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_85 = lean_ptr_addr(x_81);
x_86 = lean_usize_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_28);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_87 = x_1;
} else {
 lean_dec_ref(x_1);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_31);
lean_ctor_set(x_88, 1, x_81);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
else
{
size_t x_90; size_t x_91; uint8_t x_92; 
x_90 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_91 = lean_ptr_addr(x_31);
x_92 = lean_usize_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_93 = x_1;
} else {
 lean_dec_ref(x_1);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_31);
lean_ctor_set(x_94, 1, x_81);
if (lean_is_scalar(x_83)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_83;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_82);
return x_95;
}
else
{
lean_object* x_96; 
lean_dec(x_81);
lean_dec(x_31);
if (lean_is_scalar(x_83)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_83;
}
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_82);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
x_97 = lean_ctor_get(x_80, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_80, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_99 = x_80;
} else {
 lean_dec_ref(x_80);
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
}
else
{
uint8_t x_101; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_30);
if (x_101 == 0)
{
return x_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_30, 0);
x_103 = lean_ctor_get(x_30, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_30);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
case 2:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_1, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 1);
lean_inc(x_106);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_105);
x_107 = l_Lean_Compiler_LCNF_Specialize_visitFunDecl(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = !lean_is_exclusive(x_2);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_2, 0);
x_113 = lean_box(0);
x_114 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_112, x_110, x_113);
lean_ctor_set(x_2, 0, x_114);
lean_inc(x_106);
x_115 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_106, x_2, x_3, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; size_t x_118; size_t x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_119 = lean_ptr_addr(x_117);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_105);
x_121 = !lean_is_exclusive(x_1);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_1, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_1, 0);
lean_dec(x_123);
lean_ctor_set(x_1, 1, x_117);
lean_ctor_set(x_1, 0, x_108);
lean_ctor_set(x_115, 0, x_1);
return x_115;
}
else
{
lean_object* x_124; 
lean_dec(x_1);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_108);
lean_ctor_set(x_124, 1, x_117);
lean_ctor_set(x_115, 0, x_124);
return x_115;
}
}
else
{
size_t x_125; size_t x_126; uint8_t x_127; 
x_125 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_126 = lean_ptr_addr(x_108);
x_127 = lean_usize_dec_eq(x_125, x_126);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_1);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_1, 1);
lean_dec(x_129);
x_130 = lean_ctor_get(x_1, 0);
lean_dec(x_130);
lean_ctor_set(x_1, 1, x_117);
lean_ctor_set(x_1, 0, x_108);
lean_ctor_set(x_115, 0, x_1);
return x_115;
}
else
{
lean_object* x_131; 
lean_dec(x_1);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_108);
lean_ctor_set(x_131, 1, x_117);
lean_ctor_set(x_115, 0, x_131);
return x_115;
}
}
else
{
lean_dec(x_117);
lean_dec(x_108);
lean_ctor_set(x_115, 0, x_1);
return x_115;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; size_t x_134; size_t x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_115, 0);
x_133 = lean_ctor_get(x_115, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_115);
x_134 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_135 = lean_ptr_addr(x_132);
x_136 = lean_usize_dec_eq(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_105);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_137 = x_1;
} else {
 lean_dec_ref(x_1);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(2, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_108);
lean_ctor_set(x_138, 1, x_132);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_133);
return x_139;
}
else
{
size_t x_140; size_t x_141; uint8_t x_142; 
x_140 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_141 = lean_ptr_addr(x_108);
x_142 = lean_usize_dec_eq(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_143 = x_1;
} else {
 lean_dec_ref(x_1);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(2, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_108);
lean_ctor_set(x_144, 1, x_132);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_133);
return x_145;
}
else
{
lean_object* x_146; 
lean_dec(x_132);
lean_dec(x_108);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_1);
lean_ctor_set(x_146, 1, x_133);
return x_146;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_115);
if (x_147 == 0)
{
return x_115;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_115, 0);
x_149 = lean_ctor_get(x_115, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_115);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_2, 0);
x_152 = lean_ctor_get(x_2, 1);
x_153 = lean_ctor_get(x_2, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_2);
x_154 = lean_box(0);
x_155 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_151, x_110, x_154);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
lean_ctor_set(x_156, 2, x_153);
lean_inc(x_106);
x_157 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_106, x_156, x_3, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; size_t x_161; size_t x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_162 = lean_ptr_addr(x_158);
x_163 = lean_usize_dec_eq(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_105);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_164 = x_1;
} else {
 lean_dec_ref(x_1);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(2, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_108);
lean_ctor_set(x_165, 1, x_158);
if (lean_is_scalar(x_160)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_160;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_159);
return x_166;
}
else
{
size_t x_167; size_t x_168; uint8_t x_169; 
x_167 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_168 = lean_ptr_addr(x_108);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_170 = x_1;
} else {
 lean_dec_ref(x_1);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(2, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_108);
lean_ctor_set(x_171, 1, x_158);
if (lean_is_scalar(x_160)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_160;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_159);
return x_172;
}
else
{
lean_object* x_173; 
lean_dec(x_158);
lean_dec(x_108);
if (lean_is_scalar(x_160)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_160;
}
lean_ctor_set(x_173, 0, x_1);
lean_ctor_set(x_173, 1, x_159);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_174 = lean_ctor_get(x_157, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_157, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_176 = x_157;
} else {
 lean_dec_ref(x_157);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_107);
if (x_178 == 0)
{
return x_107;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_107, 0);
x_180 = lean_ctor_get(x_107, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_107);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
case 4:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_1, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 3);
lean_inc(x_183);
x_184 = l_Lean_Compiler_LCNF_Specialize_visitCode___closed__1;
x_185 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__1(x_183, x_184, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_182);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; size_t x_193; size_t x_194; uint8_t x_195; 
x_188 = lean_ctor_get(x_185, 0);
x_189 = lean_ctor_get(x_182, 0);
x_190 = lean_ctor_get(x_182, 1);
x_191 = lean_ctor_get(x_182, 2);
x_192 = lean_ctor_get(x_182, 3);
x_193 = lean_ptr_addr(x_192);
lean_dec(x_192);
x_194 = lean_ptr_addr(x_188);
x_195 = lean_usize_dec_eq(x_193, x_194);
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_1);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_1, 0);
lean_dec(x_197);
lean_ctor_set(x_182, 3, x_188);
lean_ctor_set(x_185, 0, x_1);
return x_185;
}
else
{
lean_object* x_198; 
lean_dec(x_1);
lean_ctor_set(x_182, 3, x_188);
x_198 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_198, 0, x_182);
lean_ctor_set(x_185, 0, x_198);
return x_185;
}
}
else
{
lean_free_object(x_182);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_ctor_set(x_185, 0, x_1);
return x_185;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; size_t x_204; size_t x_205; uint8_t x_206; 
x_199 = lean_ctor_get(x_185, 0);
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
x_202 = lean_ctor_get(x_182, 2);
x_203 = lean_ctor_get(x_182, 3);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_204 = lean_ptr_addr(x_203);
lean_dec(x_203);
x_205 = lean_ptr_addr(x_199);
x_206 = lean_usize_dec_eq(x_204, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_207 = x_1;
} else {
 lean_dec_ref(x_1);
 x_207 = lean_box(0);
}
x_208 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_208, 0, x_200);
lean_ctor_set(x_208, 1, x_201);
lean_ctor_set(x_208, 2, x_202);
lean_ctor_set(x_208, 3, x_199);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(4, 1, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_185, 0, x_209);
return x_185;
}
else
{
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_ctor_set(x_185, 0, x_1);
return x_185;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; size_t x_217; size_t x_218; uint8_t x_219; 
x_210 = lean_ctor_get(x_185, 0);
x_211 = lean_ctor_get(x_185, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_185);
x_212 = lean_ctor_get(x_182, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_182, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_182, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_182, 3);
lean_inc(x_215);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 x_216 = x_182;
} else {
 lean_dec_ref(x_182);
 x_216 = lean_box(0);
}
x_217 = lean_ptr_addr(x_215);
lean_dec(x_215);
x_218 = lean_ptr_addr(x_210);
x_219 = lean_usize_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_220 = x_1;
} else {
 lean_dec_ref(x_1);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_221 = lean_alloc_ctor(0, 4, 0);
} else {
 x_221 = x_216;
}
lean_ctor_set(x_221, 0, x_212);
lean_ctor_set(x_221, 1, x_213);
lean_ctor_set(x_221, 2, x_214);
lean_ctor_set(x_221, 3, x_210);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(4, 1, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_211);
return x_223;
}
else
{
lean_object* x_224; 
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_210);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_1);
lean_ctor_set(x_224, 1, x_211);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_182);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_185);
if (x_225 == 0)
{
return x_185;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_185, 0);
x_227 = lean_ctor_get(x_185, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_185);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
default: 
{
lean_object* x_229; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_1);
lean_ctor_set(x_229, 1, x_8);
return x_229;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_9);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_19, x_9, x_17, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_13, x_13);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
x_30 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_29, x_9, x_27, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_37 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_9, x_35, x_36, x_12);
lean_ctor_set(x_2, 0, x_37);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
x_42 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_41, x_9, x_39, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
x_50 = lean_array_get_size(x_9);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_53, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_1, 3);
lean_inc(x_57);
x_58 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_57, x_9, x_55, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_50, x_50);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_50);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_48);
lean_ctor_set(x_64, 2, x_49);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_65 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_64, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_1, 3);
lean_inc(x_68);
x_69 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_68, x_9, x_66, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_76 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_9, x_74, x_75, x_47);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_48);
lean_ctor_set(x_77, 2, x_49);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_78 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_77, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_1, 3);
lean_inc(x_81);
x_82 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_81, x_9, x_79, x_4, x_5, x_6, x_7, x_80);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_85 = x_78;
} else {
 lean_dec_ref(x_78);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; lean_object* x_15; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_Decl_isTemplateLike(x_1, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_ctor_get(x_1, 5);
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_array_get_size(x_18);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_1, 4, x_27);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_1, 4, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_1);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
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
x_35 = lean_nat_dec_le(x_22, x_22);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_22);
x_36 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_1, 4, x_38);
lean_ctor_set(x_36, 0, x_1);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_1, 4, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_1);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_46 = 0;
x_47 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_48 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_18, x_46, x_47, x_21);
lean_ctor_set(x_2, 0, x_48);
x_49 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_ctor_set(x_1, 4, x_51);
lean_ctor_set(x_49, 0, x_1);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set(x_1, 4, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_free_object(x_1);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_49);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
x_61 = lean_ctor_get(x_1, 2);
x_62 = lean_ctor_get(x_1, 3);
x_63 = lean_ctor_get(x_1, 4);
x_64 = lean_ctor_get(x_1, 5);
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_2, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_2);
x_68 = lean_array_get_size(x_62);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_71, 2, x_67);
x_72 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_63, x_71, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
lean_ctor_set(x_1, 4, x_73);
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_1);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_68, x_68);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_66);
lean_ctor_set(x_82, 2, x_67);
x_83 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_63, x_82, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
lean_ctor_set(x_1, 4, x_84);
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_1);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = 0;
x_93 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_94 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_62, x_92, x_93, x_65);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_66);
lean_ctor_set(x_95, 2, x_67);
x_96 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_63, x_95, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
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
lean_ctor_set(x_1, 4, x_97);
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_1);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_105 = lean_ctor_get(x_1, 0);
x_106 = lean_ctor_get(x_1, 1);
x_107 = lean_ctor_get(x_1, 2);
x_108 = lean_ctor_get(x_1, 3);
x_109 = lean_ctor_get(x_1, 4);
x_110 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_111 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_112 = lean_ctor_get(x_1, 5);
lean_inc(x_112);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_1);
x_113 = lean_ctor_get(x_2, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_2, 2);
lean_inc(x_115);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_116 = x_2;
} else {
 lean_dec_ref(x_2);
 x_116 = lean_box(0);
}
x_117 = lean_array_get_size(x_108);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_nat_dec_lt(x_118, x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 3, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_115);
x_121 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_109, x_120, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_125, 0, x_105);
lean_ctor_set(x_125, 1, x_106);
lean_ctor_set(x_125, 2, x_107);
lean_ctor_set(x_125, 3, x_108);
lean_ctor_set(x_125, 4, x_122);
lean_ctor_set(x_125, 5, x_112);
lean_ctor_set_uint8(x_125, sizeof(void*)*6, x_110);
lean_ctor_set_uint8(x_125, sizeof(void*)*6 + 1, x_111);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
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
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_le(x_117, x_117);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_116;
}
lean_ctor_set(x_132, 0, x_113);
lean_ctor_set(x_132, 1, x_114);
lean_ctor_set(x_132, 2, x_115);
x_133 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_109, x_132, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_137, 0, x_105);
lean_ctor_set(x_137, 1, x_106);
lean_ctor_set(x_137, 2, x_107);
lean_ctor_set(x_137, 3, x_108);
lean_ctor_set(x_137, 4, x_134);
lean_ctor_set(x_137, 5, x_112);
lean_ctor_set_uint8(x_137, sizeof(void*)*6, x_110);
lean_ctor_set_uint8(x_137, sizeof(void*)*6 + 1, x_111);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_139 = lean_ctor_get(x_133, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_141 = x_133;
} else {
 lean_dec_ref(x_133);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = 0;
x_144 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_145 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_108, x_143, x_144, x_113);
if (lean_is_scalar(x_116)) {
 x_146 = lean_alloc_ctor(0, 3, 0);
} else {
 x_146 = x_116;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_114);
lean_ctor_set(x_146, 2, x_115);
x_147 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_109, x_146, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_151, 0, x_105);
lean_ctor_set(x_151, 1, x_106);
lean_ctor_set(x_151, 2, x_107);
lean_ctor_set(x_151, 3, x_108);
lean_ctor_set(x_151, 4, x_148);
lean_ctor_set(x_151, 5, x_112);
lean_ctor_set_uint8(x_151, sizeof(void*)*6, x_110);
lean_ctor_set_uint8(x_151, sizeof(void*)*6 + 1, x_111);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_155 = x_147;
} else {
 lean_dec_ref(x_147);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
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
lean_dec(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_9);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_9, 0);
lean_dec(x_158);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_9, 1);
lean_inc(x_159);
lean_dec(x_9);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_1);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_specialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_11 = lean_st_mk_ref(x_10, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Compiler_LCNF_Specialize_main(x_1, x_9, x_12, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_push(x_19, x_15);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_array_push(x_21, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_12);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Compiler_LCNF_Decl_specialize(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_append___rarg(x_4, x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_saveSpecParamInfo(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1(x_1, x_17, x_18, x_19, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_1);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_array_get_size(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_22, x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1;
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1(x_1, x_30, x_31, x_32, x_2, x_3, x_4, x_5, x_21);
lean_dec(x_1);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_specialize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_specialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_specialize___elambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_specialize___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Lean_Compiler_LCNF_specialize___closed__1;
x_4 = l_Lean_Compiler_LCNF_specialize___closed__2;
x_5 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_specialize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_specialize___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__2;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__3;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__4;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__6;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__8;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__9;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__10;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__11;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__14;
x_2 = lean_unsigned_to_nat(4235u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__1;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2;
x_8 = 0;
x_9 = l_Lean_registerTraceClass(x_7, x_8, x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
x_12 = l_Lean_registerTraceClass(x_11, x_8, x_4, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Specialize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_SpecInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Level(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Specialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_SpecInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Level(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonadScope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Closure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1);
l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2);
l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry = _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__1);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__2);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__3);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__4);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__5 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____lambda__1___closed__5);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__1);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__2);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__3);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__4);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__5 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__5);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__6 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__6);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__7 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__7);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__8 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__8);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__9 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__9);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__10 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46____closed__10);
if (builtin) {res = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_46_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_Specialize_specCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specCacheExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1);
l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2);
l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__3);
l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1);
l_Lean_Compiler_LCNF_Specialize_Context_scope___default = _init_l_Lean_Compiler_LCNF_Specialize_Context_scope___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_Context_scope___default);
l_Lean_Compiler_LCNF_Specialize_Context_ground___default = _init_l_Lean_Compiler_LCNF_Specialize_Context_ground___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_Context_ground___default);
l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_State_decls___default___closed__1);
l_Lean_Compiler_LCNF_Specialize_State_decls___default = _init_l_Lean_Compiler_LCNF_Specialize_State_decls___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_State_decls___default);
l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__1);
l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__2);
l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__3);
l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM = _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM);
l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1);
l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6___closed__1);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4);
l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5);
l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1);
l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2);
l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1 = _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1);
l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__2);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5___closed__3);
l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1);
l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2);
l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__4);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__17 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__17);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__18 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__18);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__3);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4);
l_Lean_Compiler_LCNF_Specialize_visitCode___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_visitCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_visitCode___closed__1);
l_Lean_Compiler_LCNF_specialize___closed__1 = _init_l_Lean_Compiler_LCNF_specialize___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_specialize___closed__1);
l_Lean_Compiler_LCNF_specialize___closed__2 = _init_l_Lean_Compiler_LCNF_specialize___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_specialize___closed__2);
l_Lean_Compiler_LCNF_specialize___closed__3 = _init_l_Lean_Compiler_LCNF_specialize___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_specialize___closed__3);
l_Lean_Compiler_LCNF_specialize = _init_l_Lean_Compiler_LCNF_specialize();
lean_mark_persistent(l_Lean_Compiler_LCNF_specialize);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235____closed__15);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4235_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
