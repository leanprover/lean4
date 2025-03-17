// Lean compiler output
// Module: Lean.Compiler.LCNF.Specialize
// Imports: Lean.Compiler.Specialize Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.SpecInfo Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.Level Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.MonadScope Lean.Compiler.LCNF.Closure Lean.Compiler.LCNF.FVarUtil
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__4;
static lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___closed__1;
lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__3;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__4;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEq;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4;
static lean_object* l_Lean_Compiler_LCNF_specialize___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__1;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_FunDeclCore_toExprM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__1;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__2;
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__6;
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__3;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__3;
lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specCacheExt;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToExpr_abstractM___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_specialize___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5(lean_object*, lean_object*);
lean_object* l_List_toArray___rarg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__4(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_LCtx_addFunDecl___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_specialize___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_saveSpecParamInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_addEntry(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__4;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4;
lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_specialize___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2;
lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__14;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__11(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__6;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__9;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7;
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___rarg(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getSpecParamInfoCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Specialize_visitCode___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__10;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_isGround___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__8;
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__11;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__13;
lean_object* l_Lean_RBTree_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10;
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327_(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
extern lean_object* l_Id_instMonad;
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___rarg___lambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashable;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_allFVar___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_specialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Closure_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__8;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__9;
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__7;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___boxed(lean_object**);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__10;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at_Lean_Compiler_LCNF_Specialize_mkKey___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__2;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__3;
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_toExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__4;
static lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1(size_t, size_t, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__15;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize;
static lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__3;
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
x_1 = l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__4;
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
x_5 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__11(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__2(x_6, x_15, x_16, x_4);
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
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__3(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__3;
x_3 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__6;
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__1(x_2, x_1);
x_4 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Specialize", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("specCacheExt", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2;
x_3 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3;
x_4 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__4;
x_5 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_addEntry), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_toArray___rarg), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__6;
x_3 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__7;
x_4 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__8;
x_5 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__9;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__10;
x_3 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_1);
x_13 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_14 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_13, x_11, x_6);
x_15 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2;
lean_ctor_set(x_8, 4, x_15);
lean_ctor_set(x_8, 0, x_14);
x_16 = lean_st_ref_set(x_4, x_8, x_10);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_6, 1);
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_ctor_get(x_8, 6);
x_30 = lean_ctor_get(x_8, 7);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_1);
x_31 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_32 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_31, x_24, x_6);
x_33 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2;
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set(x_34, 7, x_30);
x_35 = lean_st_ref_set(x_4, x_34, x_23);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_40 = lean_ctor_get(x_6, 0);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_40, 7);
lean_inc(x_48);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 lean_ctor_release(x_40, 7);
 x_49 = x_40;
} else {
 lean_dec_ref(x_40);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
x_51 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_52 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_51, x_42, x_50);
x_53 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2;
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 8, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_46);
lean_ctor_set(x_54, 6, x_47);
lean_ctor_set(x_54, 7, x_48);
x_55 = lean_st_ref_set(x_4, x_54, x_41);
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
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
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
x_1 = l_Lean_Expr_instBEq;
x_2 = l_Lean_Expr_instHashable;
x_3 = l_Lean_SMap_instInhabited___rarg(x_1, x_2);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_Specialize_specCacheExt;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1;
x_13 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_14 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_12, x_13, x_8, x_11);
x_15 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(x_14, x_1);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_Specialize_specCacheExt;
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1;
x_23 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1;
x_24 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_22, x_23, x_18, x_21);
x_25 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(x_24, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
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
lean_dec(x_1);
return x_5;
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
x_1 = l_Id_instMonad;
x_2 = l_OptionT_instMonad___rarg(x_1);
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
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
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
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__2;
x_2 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_Specialize_withLetDecl___spec__5___closed__3;
x_3 = lean_unsigned_to_nat(43u);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_27; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_6);
x_18 = x_34;
x_19 = x_13;
goto block_26;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_28, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_array_fget(x_30, x_31);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_31, x_40);
lean_dec(x_31);
lean_ctor_set(x_28, 1, x_41);
x_42 = lean_box(x_17);
if (lean_obj_tag(x_42) == 4)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = lean_array_push(x_29, x_43);
lean_ctor_set(x_6, 1, x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_6);
x_18 = x_45;
x_19 = x_13;
goto block_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
lean_inc(x_39);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_39);
x_47 = lean_array_push(x_29, x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_48 = l_Lean_Compiler_LCNF_Closure_collectArg(x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_ctor_set(x_6, 1, x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_6);
x_18 = x_50;
x_19 = x_49;
goto block_26;
}
else
{
uint8_t x_51; 
lean_dec(x_47);
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_28);
x_55 = lean_array_fget(x_30, x_31);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_31, x_56);
lean_dec(x_31);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_30);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_32);
x_59 = lean_box(x_17);
if (lean_obj_tag(x_59) == 4)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
x_60 = lean_box(0);
x_61 = lean_array_push(x_29, x_60);
lean_ctor_set(x_6, 1, x_61);
lean_ctor_set(x_6, 0, x_58);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_6);
x_18 = x_62;
x_19 = x_13;
goto block_26;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
lean_inc(x_55);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_55);
x_64 = lean_array_push(x_29, x_63);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l_Lean_Compiler_LCNF_Closure_collectArg(x_55, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_ctor_set(x_6, 1, x_64);
lean_ctor_set(x_6, 0, x_58);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_6);
x_18 = x_67;
x_19 = x_66;
goto block_26;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_64);
lean_dec(x_58);
lean_free_object(x_6);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
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
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_6, 0);
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_6);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 2);
lean_inc(x_76);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_73);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_18 = x_79;
x_19 = x_13;
goto block_26;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
x_81 = lean_array_fget(x_74, x_75);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_75, x_82);
lean_dec(x_75);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 3, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_76);
x_85 = lean_box(x_17);
if (lean_obj_tag(x_85) == 4)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
x_86 = lean_box(0);
x_87 = lean_array_push(x_73, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_18 = x_89;
x_19 = x_13;
goto block_26;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
lean_inc(x_81);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_81);
x_91 = lean_array_push(x_73, x_90);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_92 = l_Lean_Compiler_LCNF_Closure_collectArg(x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_84);
lean_ctor_set(x_94, 1, x_91);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_18 = x_95;
x_19 = x_93;
goto block_26;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_91);
lean_dec(x_84);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_13 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_3);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_LCtx_addFunDecl___spec__1(x_3, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
x_22 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_21, x_3);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_22);
x_24 = 0;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__2___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__3() {
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
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1___boxed), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_3);
x_16 = lean_array_get_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_toSubarray___rarg(x_2, x_17, x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_18);
x_21 = lean_array_size(x_1);
x_22 = lean_box_usize(x_21);
x_23 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1;
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1___boxed), 13, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_19);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_22);
lean_closure_set(x_24, 4, x_23);
lean_closure_set(x_24, 5, x_10);
x_25 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2;
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___rarg), 9, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
lean_dec(x_3);
x_28 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__3;
x_29 = lean_alloc_closure((void*)(l_Lean_RBTree_contains___rarg___boxed), 3, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_27);
x_30 = l_Lean_Compiler_LCNF_Closure_run___rarg(x_26, x_29, x_15, x_5, x_6, x_7, x_8, x_13);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_3);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___lambda__1___boxed), 3, 2);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_3);
x_35 = lean_array_get_size(x_2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_toSubarray___rarg(x_2, x_36, x_35);
x_38 = lean_box(0);
x_39 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_size(x_1);
x_42 = lean_box_usize(x_41);
x_43 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1;
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1___boxed), 13, 6);
lean_closure_set(x_44, 0, x_1);
lean_closure_set(x_44, 1, x_38);
lean_closure_set(x_44, 2, x_1);
lean_closure_set(x_44, 3, x_42);
lean_closure_set(x_44, 4, x_43);
lean_closure_set(x_44, 5, x_40);
x_45 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__2;
x_46 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__2___rarg), 9, 2);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
lean_dec(x_3);
x_48 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__3;
x_49 = lean_alloc_closure((void*)(l_Lean_RBTree_contains___rarg___boxed), 3, 2);
lean_closure_set(x_49, 0, x_48);
lean_closure_set(x_49, 1, x_47);
x_50 = l_Lean_Compiler_LCNF_Closure_run___rarg(x_46, x_49, x_34, x_5, x_6, x_7, x_8, x_32);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_Collector_collect___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1() {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_28; 
x_17 = lean_array_uget(x_4, x_6);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_7, 1);
x_30 = lean_ctor_get(x_7, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_7);
x_19 = x_35;
x_20 = x_14;
goto block_27;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_29, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_array_fget(x_31, x_32);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_32, x_41);
lean_dec(x_32);
lean_ctor_set(x_29, 1, x_42);
x_43 = lean_box(x_18);
switch (lean_obj_tag(x_43)) {
case 1:
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
x_44 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_7, 0, x_44);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_7);
x_19 = x_45;
x_20 = x_14;
goto block_27;
}
case 2:
{
lean_object* x_46; 
lean_dec(x_40);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_7);
x_19 = x_46;
x_20 = x_14;
goto block_27;
}
case 4:
{
lean_object* x_47; 
lean_dec(x_40);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_7);
x_19 = x_47;
x_20 = x_14;
goto block_27;
}
default: 
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_43);
lean_inc(x_8);
x_48 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_7);
x_19 = x_52;
x_20 = x_51;
goto block_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_7, 0, x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_7);
x_19 = x_55;
x_20 = x_53;
goto block_27;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_29);
x_56 = lean_array_fget(x_31, x_32);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_32, x_57);
lean_dec(x_32);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_33);
x_60 = lean_box(x_18);
switch (lean_obj_tag(x_60)) {
case 1:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
x_61 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_61);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_7);
x_19 = x_62;
x_20 = x_14;
goto block_27;
}
case 2:
{
lean_object* x_63; 
lean_dec(x_56);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_3);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_7);
x_19 = x_63;
x_20 = x_14;
goto block_27;
}
case 4:
{
lean_object* x_64; 
lean_dec(x_56);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_3);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_7);
x_19 = x_64;
x_20 = x_14;
goto block_27;
}
default: 
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_60);
lean_inc(x_8);
x_65 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_3);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_7);
x_19 = x_69;
x_20 = x_68;
goto block_27;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_71);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_7);
x_19 = x_72;
x_20 = x_70;
goto block_27;
}
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_7, 1);
lean_inc(x_73);
lean_dec(x_7);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 2);
lean_inc(x_76);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_inc(x_3);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_73);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_19 = x_79;
x_20 = x_14;
goto block_27;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
x_81 = lean_array_fget(x_74, x_75);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_75, x_82);
lean_dec(x_75);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 3, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_76);
x_85 = lean_box(x_18);
switch (lean_obj_tag(x_85)) {
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_81);
x_86 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_19 = x_88;
x_20 = x_14;
goto block_27;
}
case 2:
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_81);
lean_inc(x_3);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_3);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_19 = x_90;
x_20 = x_14;
goto block_27;
}
case 4:
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_81);
lean_inc(x_3);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_3);
lean_ctor_set(x_91, 1, x_84);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_19 = x_92;
x_20 = x_14;
goto block_27;
}
default: 
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_85);
lean_inc(x_8);
x_93 = l_Lean_Compiler_LCNF_Specialize_isGround___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__1(x_81, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_3);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_3);
lean_ctor_set(x_97, 1, x_84);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_19 = x_98;
x_20 = x_96;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_100 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_84);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_19 = x_102;
x_20 = x_99;
goto block_27;
}
}
}
}
}
block_27:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_6 = x_25;
x_7 = x_23;
x_14 = x_20;
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
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_array_size(x_1);
x_17 = 0;
lean_inc(x_3);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(x_1, x_13, x_14, x_1, x_16, x_17, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
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
x_16 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_size(x_1);
x_9 = 0;
lean_inc(x_1);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__1(x_8, x_9, x_1);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Specialize_expandCodeDecls___spec__2(x_8, x_9, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_14 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(x_2, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_27; 
x_17 = lean_array_uget(x_5, x_7);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_17);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_8);
x_18 = x_34;
x_19 = x_14;
goto block_26;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_28, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_array_fget(x_30, x_31);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_31, x_40);
lean_dec(x_31);
lean_ctor_set(x_28, 1, x_41);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_17, 2);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_inc(x_1);
x_45 = l_Lean_Expr_instantiateLevelParamsNoCache(x_43, x_44, x_1);
lean_ctor_set(x_17, 2, x_45);
x_46 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_17, x_9, x_10, x_11, x_12, x_13, x_14);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_push(x_29, x_47);
lean_ctor_set(x_8, 1, x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_8);
x_18 = x_50;
x_19 = x_48;
goto block_26;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
x_53 = lean_ctor_get(x_17, 2);
x_54 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_1);
x_56 = l_Lean_Expr_instantiateLevelParamsNoCache(x_53, x_55, x_1);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_54);
x_58 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_57, x_9, x_10, x_11, x_12, x_13, x_14);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_array_push(x_29, x_59);
lean_ctor_set(x_8, 1, x_61);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_8);
x_18 = x_62;
x_19 = x_60;
goto block_26;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_39);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_64 = lean_ctor_get(x_39, 0);
x_65 = lean_st_ref_get(x_9, x_14);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = 1;
x_69 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_66, x_64, x_68);
lean_dec(x_66);
x_70 = lean_st_ref_take(x_9, x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_17, 0);
lean_inc(x_73);
lean_dec(x_17);
x_74 = l_Lean_Compiler_LCNF_Arg_toExpr(x_69);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
x_78 = lean_array_get_size(x_77);
x_79 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_73);
x_80 = 32;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = 16;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = lean_uint64_to_usize(x_85);
x_87 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_88 = 1;
x_89 = lean_usize_sub(x_87, x_88);
x_90 = lean_usize_land(x_86, x_89);
x_91 = lean_array_uget(x_77, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_73, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_93 = lean_nat_add(x_76, x_40);
lean_dec(x_76);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_73);
lean_ctor_set(x_94, 1, x_74);
lean_ctor_set(x_94, 2, x_91);
x_95 = lean_array_uset(x_77, x_90, x_94);
x_96 = lean_unsigned_to_nat(4u);
x_97 = lean_nat_mul(x_93, x_96);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_nat_div(x_97, x_98);
lean_dec(x_97);
x_100 = lean_array_get_size(x_95);
x_101 = lean_nat_dec_le(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_95);
lean_ctor_set(x_71, 1, x_102);
lean_ctor_set(x_71, 0, x_93);
x_103 = lean_st_ref_set(x_9, x_71, x_72);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_ctor_set(x_39, 0, x_8);
x_18 = x_39;
x_19 = x_104;
goto block_26;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_ctor_set(x_71, 1, x_95);
lean_ctor_set(x_71, 0, x_93);
x_105 = lean_st_ref_set(x_9, x_71, x_72);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_ctor_set(x_39, 0, x_8);
x_18 = x_39;
x_19 = x_106;
goto block_26;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_box(0);
x_108 = lean_array_uset(x_77, x_90, x_107);
x_109 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_73, x_74, x_91);
x_110 = lean_array_uset(x_108, x_90, x_109);
lean_ctor_set(x_71, 1, x_110);
x_111 = lean_st_ref_set(x_9, x_71, x_72);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
lean_ctor_set(x_39, 0, x_8);
x_18 = x_39;
x_19 = x_112;
goto block_26;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; uint64_t x_122; size_t x_123; size_t x_124; size_t x_125; size_t x_126; size_t x_127; lean_object* x_128; uint8_t x_129; 
x_113 = lean_ctor_get(x_71, 0);
x_114 = lean_ctor_get(x_71, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_71);
x_115 = lean_array_get_size(x_114);
x_116 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_73);
x_117 = 32;
x_118 = lean_uint64_shift_right(x_116, x_117);
x_119 = lean_uint64_xor(x_116, x_118);
x_120 = 16;
x_121 = lean_uint64_shift_right(x_119, x_120);
x_122 = lean_uint64_xor(x_119, x_121);
x_123 = lean_uint64_to_usize(x_122);
x_124 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_125 = 1;
x_126 = lean_usize_sub(x_124, x_125);
x_127 = lean_usize_land(x_123, x_126);
x_128 = lean_array_uget(x_114, x_127);
x_129 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_73, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_130 = lean_nat_add(x_113, x_40);
lean_dec(x_113);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_73);
lean_ctor_set(x_131, 1, x_74);
lean_ctor_set(x_131, 2, x_128);
x_132 = lean_array_uset(x_114, x_127, x_131);
x_133 = lean_unsigned_to_nat(4u);
x_134 = lean_nat_mul(x_130, x_133);
x_135 = lean_unsigned_to_nat(3u);
x_136 = lean_nat_div(x_134, x_135);
lean_dec(x_134);
x_137 = lean_array_get_size(x_132);
x_138 = lean_nat_dec_le(x_136, x_137);
lean_dec(x_137);
lean_dec(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_132);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_130);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_st_ref_set(x_9, x_140, x_72);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
lean_ctor_set(x_39, 0, x_8);
x_18 = x_39;
x_19 = x_142;
goto block_26;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_130);
lean_ctor_set(x_143, 1, x_132);
x_144 = lean_st_ref_set(x_9, x_143, x_72);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
lean_ctor_set(x_39, 0, x_8);
x_18 = x_39;
x_19 = x_145;
goto block_26;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_box(0);
x_147 = lean_array_uset(x_114, x_127, x_146);
x_148 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_73, x_74, x_128);
x_149 = lean_array_uset(x_147, x_127, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_113);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_st_ref_set(x_9, x_150, x_72);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
lean_ctor_set(x_39, 0, x_8);
x_18 = x_39;
x_19 = x_152;
goto block_26;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; size_t x_175; size_t x_176; size_t x_177; size_t x_178; size_t x_179; lean_object* x_180; uint8_t x_181; 
x_153 = lean_ctor_get(x_39, 0);
lean_inc(x_153);
lean_dec(x_39);
x_154 = lean_st_ref_get(x_9, x_14);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = 1;
x_158 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_155, x_153, x_157);
lean_dec(x_155);
x_159 = lean_st_ref_take(x_9, x_156);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_17, 0);
lean_inc(x_162);
lean_dec(x_17);
x_163 = l_Lean_Compiler_LCNF_Arg_toExpr(x_158);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
x_167 = lean_array_get_size(x_165);
x_168 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_162);
x_169 = 32;
x_170 = lean_uint64_shift_right(x_168, x_169);
x_171 = lean_uint64_xor(x_168, x_170);
x_172 = 16;
x_173 = lean_uint64_shift_right(x_171, x_172);
x_174 = lean_uint64_xor(x_171, x_173);
x_175 = lean_uint64_to_usize(x_174);
x_176 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_177 = 1;
x_178 = lean_usize_sub(x_176, x_177);
x_179 = lean_usize_land(x_175, x_178);
x_180 = lean_array_uget(x_165, x_179);
x_181 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_162, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_182 = lean_nat_add(x_164, x_40);
lean_dec(x_164);
x_183 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_183, 0, x_162);
lean_ctor_set(x_183, 1, x_163);
lean_ctor_set(x_183, 2, x_180);
x_184 = lean_array_uset(x_165, x_179, x_183);
x_185 = lean_unsigned_to_nat(4u);
x_186 = lean_nat_mul(x_182, x_185);
x_187 = lean_unsigned_to_nat(3u);
x_188 = lean_nat_div(x_186, x_187);
lean_dec(x_186);
x_189 = lean_array_get_size(x_184);
x_190 = lean_nat_dec_le(x_188, x_189);
lean_dec(x_189);
lean_dec(x_188);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_184);
if (lean_is_scalar(x_166)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_166;
}
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_st_ref_set(x_9, x_192, x_161);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_8);
x_18 = x_195;
x_19 = x_194;
goto block_26;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
if (lean_is_scalar(x_166)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_166;
}
lean_ctor_set(x_196, 0, x_182);
lean_ctor_set(x_196, 1, x_184);
x_197 = lean_st_ref_set(x_9, x_196, x_161);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_8);
x_18 = x_199;
x_19 = x_198;
goto block_26;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_200 = lean_box(0);
x_201 = lean_array_uset(x_165, x_179, x_200);
x_202 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_162, x_163, x_180);
x_203 = lean_array_uset(x_201, x_179, x_202);
if (lean_is_scalar(x_166)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_166;
}
lean_ctor_set(x_204, 0, x_164);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_st_ref_set(x_9, x_204, x_161);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_8);
x_18 = x_207;
x_19 = x_206;
goto block_26;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_28);
x_208 = lean_array_fget(x_30, x_31);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_31, x_209);
lean_dec(x_31);
x_211 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_211, 0, x_30);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_32);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_212 = lean_ctor_get(x_17, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_17, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_17, 2);
lean_inc(x_214);
x_215 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_216 = x_17;
} else {
 lean_dec_ref(x_17);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_2, 1);
lean_inc(x_217);
lean_inc(x_1);
x_218 = l_Lean_Expr_instantiateLevelParamsNoCache(x_214, x_217, x_1);
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 3, 1);
} else {
 x_219 = x_216;
}
lean_ctor_set(x_219, 0, x_212);
lean_ctor_set(x_219, 1, x_213);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set_uint8(x_219, sizeof(void*)*3, x_215);
x_220 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_219, x_9, x_10, x_11, x_12, x_13, x_14);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_array_push(x_29, x_221);
lean_ctor_set(x_8, 1, x_223);
lean_ctor_set(x_8, 0, x_211);
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_8);
x_18 = x_224;
x_19 = x_222;
goto block_26;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint64_t x_241; uint64_t x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; uint64_t x_246; uint64_t x_247; size_t x_248; size_t x_249; size_t x_250; size_t x_251; size_t x_252; lean_object* x_253; uint8_t x_254; 
x_225 = lean_ctor_get(x_208, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_226 = x_208;
} else {
 lean_dec_ref(x_208);
 x_226 = lean_box(0);
}
x_227 = lean_st_ref_get(x_9, x_14);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = 1;
x_231 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_228, x_225, x_230);
lean_dec(x_228);
x_232 = lean_st_ref_take(x_9, x_229);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_17, 0);
lean_inc(x_235);
lean_dec(x_17);
x_236 = l_Lean_Compiler_LCNF_Arg_toExpr(x_231);
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_239 = x_233;
} else {
 lean_dec_ref(x_233);
 x_239 = lean_box(0);
}
x_240 = lean_array_get_size(x_238);
x_241 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_235);
x_242 = 32;
x_243 = lean_uint64_shift_right(x_241, x_242);
x_244 = lean_uint64_xor(x_241, x_243);
x_245 = 16;
x_246 = lean_uint64_shift_right(x_244, x_245);
x_247 = lean_uint64_xor(x_244, x_246);
x_248 = lean_uint64_to_usize(x_247);
x_249 = lean_usize_of_nat(x_240);
lean_dec(x_240);
x_250 = 1;
x_251 = lean_usize_sub(x_249, x_250);
x_252 = lean_usize_land(x_248, x_251);
x_253 = lean_array_uget(x_238, x_252);
x_254 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_235, x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_255 = lean_nat_add(x_237, x_209);
lean_dec(x_237);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_235);
lean_ctor_set(x_256, 1, x_236);
lean_ctor_set(x_256, 2, x_253);
x_257 = lean_array_uset(x_238, x_252, x_256);
x_258 = lean_unsigned_to_nat(4u);
x_259 = lean_nat_mul(x_255, x_258);
x_260 = lean_unsigned_to_nat(3u);
x_261 = lean_nat_div(x_259, x_260);
lean_dec(x_259);
x_262 = lean_array_get_size(x_257);
x_263 = lean_nat_dec_le(x_261, x_262);
lean_dec(x_262);
lean_dec(x_261);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_257);
if (lean_is_scalar(x_239)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_239;
}
lean_ctor_set(x_265, 0, x_255);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_st_ref_set(x_9, x_265, x_234);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
lean_ctor_set(x_8, 0, x_211);
if (lean_is_scalar(x_226)) {
 x_268 = lean_alloc_ctor(1, 1, 0);
} else {
 x_268 = x_226;
}
lean_ctor_set(x_268, 0, x_8);
x_18 = x_268;
x_19 = x_267;
goto block_26;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
if (lean_is_scalar(x_239)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_239;
}
lean_ctor_set(x_269, 0, x_255);
lean_ctor_set(x_269, 1, x_257);
x_270 = lean_st_ref_set(x_9, x_269, x_234);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
lean_ctor_set(x_8, 0, x_211);
if (lean_is_scalar(x_226)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_226;
}
lean_ctor_set(x_272, 0, x_8);
x_18 = x_272;
x_19 = x_271;
goto block_26;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_box(0);
x_274 = lean_array_uset(x_238, x_252, x_273);
x_275 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_235, x_236, x_253);
x_276 = lean_array_uset(x_274, x_252, x_275);
if (lean_is_scalar(x_239)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_239;
}
lean_ctor_set(x_277, 0, x_237);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_st_ref_set(x_9, x_277, x_234);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
lean_ctor_set(x_8, 0, x_211);
if (lean_is_scalar(x_226)) {
 x_280 = lean_alloc_ctor(1, 1, 0);
} else {
 x_280 = x_226;
}
lean_ctor_set(x_280, 0, x_8);
x_18 = x_280;
x_19 = x_279;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_281 = lean_ctor_get(x_8, 0);
x_282 = lean_ctor_get(x_8, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_8);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 2);
lean_inc(x_285);
x_286 = lean_nat_dec_lt(x_284, x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_17);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_281);
lean_ctor_set(x_287, 1, x_282);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_18 = x_288;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 x_289 = x_281;
} else {
 lean_dec_ref(x_281);
 x_289 = lean_box(0);
}
x_290 = lean_array_fget(x_283, x_284);
x_291 = lean_unsigned_to_nat(1u);
x_292 = lean_nat_add(x_284, x_291);
lean_dec(x_284);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(0, 3, 0);
} else {
 x_293 = x_289;
}
lean_ctor_set(x_293, 0, x_283);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_285);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_294 = lean_ctor_get(x_17, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_17, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_17, 2);
lean_inc(x_296);
x_297 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_298 = x_17;
} else {
 lean_dec_ref(x_17);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_2, 1);
lean_inc(x_299);
lean_inc(x_1);
x_300 = l_Lean_Expr_instantiateLevelParamsNoCache(x_296, x_299, x_1);
if (lean_is_scalar(x_298)) {
 x_301 = lean_alloc_ctor(0, 3, 1);
} else {
 x_301 = x_298;
}
lean_ctor_set(x_301, 0, x_294);
lean_ctor_set(x_301, 1, x_295);
lean_ctor_set(x_301, 2, x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*3, x_297);
x_302 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_301, x_9, x_10, x_11, x_12, x_13, x_14);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_array_push(x_282, x_303);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_293);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_18 = x_307;
x_19 = x_304;
goto block_26;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint64_t x_324; uint64_t x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; uint64_t x_329; uint64_t x_330; size_t x_331; size_t x_332; size_t x_333; size_t x_334; size_t x_335; lean_object* x_336; uint8_t x_337; 
x_308 = lean_ctor_get(x_290, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 x_309 = x_290;
} else {
 lean_dec_ref(x_290);
 x_309 = lean_box(0);
}
x_310 = lean_st_ref_get(x_9, x_14);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = 1;
x_314 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_311, x_308, x_313);
lean_dec(x_311);
x_315 = lean_st_ref_take(x_9, x_312);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_17, 0);
lean_inc(x_318);
lean_dec(x_17);
x_319 = l_Lean_Compiler_LCNF_Arg_toExpr(x_314);
x_320 = lean_ctor_get(x_316, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_316, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_322 = x_316;
} else {
 lean_dec_ref(x_316);
 x_322 = lean_box(0);
}
x_323 = lean_array_get_size(x_321);
x_324 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_318);
x_325 = 32;
x_326 = lean_uint64_shift_right(x_324, x_325);
x_327 = lean_uint64_xor(x_324, x_326);
x_328 = 16;
x_329 = lean_uint64_shift_right(x_327, x_328);
x_330 = lean_uint64_xor(x_327, x_329);
x_331 = lean_uint64_to_usize(x_330);
x_332 = lean_usize_of_nat(x_323);
lean_dec(x_323);
x_333 = 1;
x_334 = lean_usize_sub(x_332, x_333);
x_335 = lean_usize_land(x_331, x_334);
x_336 = lean_array_uget(x_321, x_335);
x_337 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_318, x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_338 = lean_nat_add(x_320, x_291);
lean_dec(x_320);
x_339 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_339, 0, x_318);
lean_ctor_set(x_339, 1, x_319);
lean_ctor_set(x_339, 2, x_336);
x_340 = lean_array_uset(x_321, x_335, x_339);
x_341 = lean_unsigned_to_nat(4u);
x_342 = lean_nat_mul(x_338, x_341);
x_343 = lean_unsigned_to_nat(3u);
x_344 = lean_nat_div(x_342, x_343);
lean_dec(x_342);
x_345 = lean_array_get_size(x_340);
x_346 = lean_nat_dec_le(x_344, x_345);
lean_dec(x_345);
lean_dec(x_344);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_347 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_340);
if (lean_is_scalar(x_322)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_322;
}
lean_ctor_set(x_348, 0, x_338);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_st_ref_set(x_9, x_348, x_317);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
lean_dec(x_349);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_293);
lean_ctor_set(x_351, 1, x_282);
if (lean_is_scalar(x_309)) {
 x_352 = lean_alloc_ctor(1, 1, 0);
} else {
 x_352 = x_309;
}
lean_ctor_set(x_352, 0, x_351);
x_18 = x_352;
x_19 = x_350;
goto block_26;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
if (lean_is_scalar(x_322)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_322;
}
lean_ctor_set(x_353, 0, x_338);
lean_ctor_set(x_353, 1, x_340);
x_354 = lean_st_ref_set(x_9, x_353, x_317);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_293);
lean_ctor_set(x_356, 1, x_282);
if (lean_is_scalar(x_309)) {
 x_357 = lean_alloc_ctor(1, 1, 0);
} else {
 x_357 = x_309;
}
lean_ctor_set(x_357, 0, x_356);
x_18 = x_357;
x_19 = x_355;
goto block_26;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_358 = lean_box(0);
x_359 = lean_array_uset(x_321, x_335, x_358);
x_360 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_318, x_319, x_336);
x_361 = lean_array_uset(x_359, x_335, x_360);
if (lean_is_scalar(x_322)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_322;
}
lean_ctor_set(x_362, 0, x_320);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_st_ref_set(x_9, x_362, x_317);
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_293);
lean_ctor_set(x_365, 1, x_282);
if (lean_is_scalar(x_309)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_309;
}
lean_ctor_set(x_366, 0, x_365);
x_18 = x_366;
x_19 = x_364;
goto block_26;
}
}
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_7, x_23);
x_7 = x_24;
x_8 = x_22;
x_14 = x_19;
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
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__1;
x_2 = l_Lean_Compiler_LCNF_instInhabitedDecl;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__2;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize.mkSpecDecl.go", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("can only specialize decls with code", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1;
x_2 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__2;
x_3 = lean_unsigned_to_nat(226u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_array_size(x_3);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_21, x_22, x_3, x_8, x_9, x_10, x_11, x_12, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_size(x_4);
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___spec__2(x_26, x_22, x_4, x_8, x_9, x_10, x_11, x_12, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; size_t x_45; lean_object* x_46; uint8_t x_47; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_array_get_size(x_2);
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_31);
x_33 = l_Array_toSubarray___rarg(x_2, x_32, x_31);
x_34 = lean_box(0);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 0, x_33);
x_35 = lean_array_size(x_16);
lean_inc(x_6);
lean_inc(x_1);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(x_1, x_6, x_34, x_16, x_16, x_35, x_22, x_27, x_8, x_9, x_10, x_11, x_12, x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_get_size(x_16);
x_41 = l_Array_toSubarray___rarg(x_16, x_31, x_40);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
lean_inc(x_6);
lean_inc(x_1);
x_46 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(x_1, x_6, x_41, x_43, x_45, x_39, x_8, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_41);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
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
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_15, x_1, x_20);
x_57 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_56, x_8, x_9, x_10, x_11, x_12, x_55);
lean_dec(x_8);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Compiler_LCNF_attachCodeDecls(x_29, x_58);
lean_dec(x_29);
lean_inc(x_60);
x_61 = l_Lean_Compiler_LCNF_Code_inferType(x_60, x_9, x_10, x_11, x_12, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_54);
x_64 = l_Lean_Compiler_LCNF_mkForallParams(x_54, x_62, x_9, x_10, x_11, x_12, x_63);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_62);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
lean_ctor_set(x_14, 0, x_60);
x_67 = lean_box(0);
lean_ctor_set(x_6, 5, x_67);
lean_ctor_set(x_6, 3, x_54);
lean_ctor_set(x_6, 2, x_66);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_7);
x_68 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_6);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
lean_ctor_set(x_14, 0, x_60);
x_71 = lean_box(0);
lean_ctor_set(x_6, 5, x_71);
lean_ctor_set(x_6, 3, x_54);
lean_ctor_set(x_6, 2, x_69);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_7);
x_72 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_60);
lean_dec(x_54);
lean_free_object(x_6);
lean_free_object(x_14);
lean_dec(x_7);
lean_dec(x_5);
x_74 = !lean_is_exclusive(x_64);
if (x_74 == 0)
{
return x_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_64, 0);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_64);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_60);
lean_dec(x_54);
lean_free_object(x_6);
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_61);
if (x_78 == 0)
{
return x_61;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_61, 0);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_61);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_6);
x_82 = lean_ctor_get(x_46, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_46, 1);
lean_inc(x_83);
lean_dec(x_46);
x_84 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_15, x_1, x_20);
x_85 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_84, x_8, x_9, x_10, x_11, x_12, x_83);
lean_dec(x_8);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Compiler_LCNF_attachCodeDecls(x_29, x_86);
lean_dec(x_29);
lean_inc(x_88);
x_89 = l_Lean_Compiler_LCNF_Code_inferType(x_88, x_9, x_10, x_11, x_12, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_82);
x_92 = l_Lean_Compiler_LCNF_mkForallParams(x_82, x_90, x_9, x_10, x_11, x_12, x_91);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
lean_ctor_set(x_14, 0, x_88);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_97, 0, x_7);
lean_ctor_set(x_97, 1, x_5);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_82);
lean_ctor_set(x_97, 4, x_14);
lean_ctor_set(x_97, 5, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_97, sizeof(void*)*6 + 1, x_19);
x_98 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_97);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
lean_dec(x_82);
lean_free_object(x_14);
lean_dec(x_7);
lean_dec(x_5);
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_102 = x_92;
} else {
 lean_dec_ref(x_92);
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
lean_dec(x_88);
lean_dec(x_82);
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_104 = lean_ctor_get(x_89, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_89, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_106 = x_89;
} else {
 lean_dec_ref(x_89);
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
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; size_t x_123; lean_object* x_124; size_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_108 = lean_ctor_get(x_27, 0);
x_109 = lean_ctor_get(x_27, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_27);
x_110 = lean_array_get_size(x_2);
x_111 = lean_unsigned_to_nat(0u);
lean_inc(x_110);
x_112 = l_Array_toSubarray___rarg(x_2, x_111, x_110);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_24);
x_115 = lean_array_size(x_16);
lean_inc(x_6);
lean_inc(x_1);
x_116 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(x_1, x_6, x_113, x_16, x_16, x_115, x_22, x_114, x_8, x_9, x_10, x_11, x_12, x_109);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_array_get_size(x_16);
x_121 = l_Array_toSubarray___rarg(x_16, x_110, x_120);
x_122 = lean_ctor_get(x_121, 2);
lean_inc(x_122);
x_123 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
x_125 = lean_usize_of_nat(x_124);
lean_dec(x_124);
lean_inc(x_6);
lean_inc(x_1);
x_126 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(x_1, x_6, x_121, x_123, x_125, x_119, x_8, x_9, x_10, x_11, x_12, x_118);
lean_dec(x_121);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_127 = x_6;
} else {
 lean_dec_ref(x_6);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_15, x_1, x_20);
x_131 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_130, x_8, x_9, x_10, x_11, x_12, x_129);
lean_dec(x_8);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Compiler_LCNF_attachCodeDecls(x_108, x_132);
lean_dec(x_108);
lean_inc(x_134);
x_135 = l_Lean_Compiler_LCNF_Code_inferType(x_134, x_9, x_10, x_11, x_12, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_128);
x_138 = l_Lean_Compiler_LCNF_mkForallParams(x_128, x_136, x_9, x_10, x_11, x_12, x_137);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
lean_ctor_set(x_14, 0, x_134);
x_142 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_143 = lean_alloc_ctor(0, 6, 2);
} else {
 x_143 = x_127;
}
lean_ctor_set(x_143, 0, x_7);
lean_ctor_set(x_143, 1, x_5);
lean_ctor_set(x_143, 2, x_139);
lean_ctor_set(x_143, 3, x_128);
lean_ctor_set(x_143, 4, x_14);
lean_ctor_set(x_143, 5, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*6, x_18);
lean_ctor_set_uint8(x_143, sizeof(void*)*6 + 1, x_19);
x_144 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_143);
if (lean_is_scalar(x_141)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_141;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_140);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_134);
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_14);
lean_dec(x_7);
lean_dec(x_5);
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_148 = x_138;
} else {
 lean_dec_ref(x_138);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_134);
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_150 = lean_ctor_get(x_135, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_135, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_152 = x_135;
} else {
 lean_dec_ref(x_135);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
else
{
uint8_t x_154; uint8_t x_155; lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; size_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; size_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; size_t x_180; lean_object* x_181; size_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_154 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_155 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_156 = lean_ctor_get(x_14, 0);
lean_inc(x_156);
lean_dec(x_14);
x_157 = lean_array_size(x_3);
x_158 = 0;
x_159 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_157, x_158, x_3, x_8, x_9, x_10, x_11, x_12, x_13);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_array_size(x_4);
x_163 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___spec__2(x_162, x_158, x_4, x_8, x_9, x_10, x_11, x_12, x_161);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = lean_array_get_size(x_2);
x_168 = lean_unsigned_to_nat(0u);
lean_inc(x_167);
x_169 = l_Array_toSubarray___rarg(x_2, x_168, x_167);
x_170 = lean_box(0);
if (lean_is_scalar(x_166)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_166;
}
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_160);
x_172 = lean_array_size(x_16);
lean_inc(x_6);
lean_inc(x_1);
x_173 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(x_1, x_6, x_170, x_16, x_16, x_172, x_158, x_171, x_8, x_9, x_10, x_11, x_12, x_165);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_array_get_size(x_16);
x_178 = l_Array_toSubarray___rarg(x_16, x_167, x_177);
x_179 = lean_ctor_get(x_178, 2);
lean_inc(x_179);
x_180 = lean_usize_of_nat(x_179);
lean_dec(x_179);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
x_182 = lean_usize_of_nat(x_181);
lean_dec(x_181);
lean_inc(x_6);
lean_inc(x_1);
x_183 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__2(x_1, x_6, x_178, x_180, x_182, x_176, x_8, x_9, x_10, x_11, x_12, x_175);
lean_dec(x_178);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_184 = x_6;
} else {
 lean_dec_ref(x_6);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_15, x_1, x_156);
x_188 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_187, x_8, x_9, x_10, x_11, x_12, x_186);
lean_dec(x_8);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Compiler_LCNF_attachCodeDecls(x_164, x_189);
lean_dec(x_164);
lean_inc(x_191);
x_192 = l_Lean_Compiler_LCNF_Code_inferType(x_191, x_9, x_10, x_11, x_12, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_185);
x_195 = l_Lean_Compiler_LCNF_mkForallParams(x_185, x_193, x_9, x_10, x_11, x_12, x_194);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_191);
x_200 = lean_box(0);
if (lean_is_scalar(x_184)) {
 x_201 = lean_alloc_ctor(0, 6, 2);
} else {
 x_201 = x_184;
}
lean_ctor_set(x_201, 0, x_7);
lean_ctor_set(x_201, 1, x_5);
lean_ctor_set(x_201, 2, x_196);
lean_ctor_set(x_201, 3, x_185);
lean_ctor_set(x_201, 4, x_199);
lean_ctor_set(x_201, 5, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*6, x_154);
lean_ctor_set_uint8(x_201, sizeof(void*)*6 + 1, x_155);
x_202 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_201);
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_198;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_197);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_7);
lean_dec(x_5);
x_204 = lean_ctor_get(x_195, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_195, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_206 = x_195;
} else {
 lean_dec_ref(x_195);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_208 = lean_ctor_get(x_192, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_192, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_210 = x_192;
} else {
 lean_dec_ref(x_192);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_212 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__4;
x_213 = l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3(x_212, x_8, x_9, x_10, x_11, x_12, x_13);
return x_213;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
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
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_at_", 4, 4);
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
x_1 = lean_mk_string_unchecked("spec", 4, 4);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2;
x_19 = l_Lean_Name_appendCore(x_17, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_7, 2);
lean_inc(x_20);
lean_dec(x_7);
x_21 = l_Lean_Name_appendCore(x_19, x_20);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4;
x_23 = l_Lean_Name_appendCore(x_21, x_22);
lean_dec(x_21);
x_24 = lean_array_get_size(x_15);
lean_dec(x_15);
x_25 = lean_name_append_index_after(x_23, x_24);
x_26 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__3;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_26, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_mk_ref(x_26, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_28);
x_33 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(x_2, x_3, x_4, x_5, x_6, x_28, x_25, x_31, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Compiler_LCNF_eraseDecl(x_28, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_34);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
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
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_31);
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_dec(x_33);
x_49 = l_Lean_Compiler_LCNF_eraseDecl(x_28, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_47);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
return x_27;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_27, 0);
x_60 = lean_ctor_get(x_27, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_27);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_6;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_array_fget(x_13, x_14);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_14, x_22);
lean_dec(x_14);
lean_ctor_set(x_11, 1, x_23);
x_24 = lean_box(x_9);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; size_t x_26; size_t x_27; 
x_25 = lean_array_push(x_12, x_21);
lean_ctor_set(x_6, 1, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
goto _start;
}
else
{
size_t x_29; size_t x_30; 
lean_dec(x_24);
lean_dec(x_21);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_32 = lean_array_fget(x_13, x_14);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_14, x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_15);
x_36 = lean_box(x_9);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; size_t x_38; size_t x_39; 
x_37 = lean_array_push(x_12, x_32);
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_35);
x_38 = 1;
x_39 = lean_usize_add(x_5, x_38);
x_5 = x_39;
goto _start;
}
else
{
size_t x_41; size_t x_42; 
lean_dec(x_36);
lean_dec(x_32);
lean_ctor_set(x_6, 0, x_35);
x_41 = 1;
x_42 = lean_usize_add(x_5, x_41);
x_5 = x_42;
goto _start;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_6);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 2);
lean_inc(x_48);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_51 = x_44;
} else {
 lean_dec_ref(x_44);
 x_51 = lean_box(0);
}
x_52 = lean_array_fget(x_46, x_47);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_47, x_53);
lean_dec(x_47);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 3, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_48);
x_56 = lean_box(x_9);
if (lean_obj_tag(x_56) == 4)
{
lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; 
x_57 = lean_array_push(x_45, x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = 1;
x_60 = lean_usize_add(x_5, x_59);
x_5 = x_60;
x_6 = x_58;
goto _start;
}
else
{
lean_object* x_62; size_t x_63; size_t x_64; 
lean_dec(x_56);
lean_dec(x_52);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_45);
x_63 = 1;
x_64 = lean_usize_add(x_5, x_63);
x_5 = x_64;
x_6 = x_62;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_5 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_6 = lean_box(0);
x_7 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(x_1, x_6, x_1, x_9, x_10, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_1);
x_14 = lean_array_get_size(x_2);
x_15 = l_Array_toSubarray___rarg(x_2, x_13, x_14);
x_16 = l_Array_ofSubarray___rarg(x_15);
lean_dec(x_15);
x_17 = l_Array_append___rarg(x_12, x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_getRemainingArgs___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_Lean_isTracingEnabledForCore(x_1, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
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
x_5 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
x_8 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__4(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_apply_8(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_8(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static double _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
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
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_7, 2);
x_22 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1;
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_st_ref_take(x_8, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_25, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; double x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
x_35 = 0;
x_36 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
x_37 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_float(x_37, sizeof(void*)*2, x_34);
lean_ctor_set_float(x_37, sizeof(void*)*2 + 8, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 16, x_35);
x_38 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_39 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_15);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_10);
lean_ctor_set(x_24, 1, x_39);
lean_ctor_set(x_24, 0, x_10);
x_40 = l_Lean_PersistentArray_push___rarg(x_33, x_24);
lean_ctor_set(x_26, 0, x_40);
x_41 = lean_st_ref_set(x_8, x_25, x_28);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint64_t x_48; lean_object* x_49; double x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_48 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
x_49 = lean_ctor_get(x_26, 0);
lean_inc(x_49);
lean_dec(x_26);
x_50 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
x_51 = 0;
x_52 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
x_53 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_float(x_53, sizeof(void*)*2, x_50);
lean_ctor_set_float(x_53, sizeof(void*)*2 + 8, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 16, x_51);
x_54 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_55 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_15);
lean_ctor_set(x_55, 2, x_54);
lean_inc(x_10);
lean_ctor_set(x_24, 1, x_55);
lean_ctor_set(x_24, 0, x_10);
x_56 = l_Lean_PersistentArray_push___rarg(x_49, x_24);
x_57 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint64(x_57, sizeof(void*)*1, x_48);
lean_ctor_set(x_25, 3, x_57);
x_58 = lean_st_ref_set(x_8, x_25, x_28);
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
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; lean_object* x_72; double x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_63 = lean_ctor_get(x_25, 0);
x_64 = lean_ctor_get(x_25, 1);
x_65 = lean_ctor_get(x_25, 2);
x_66 = lean_ctor_get(x_25, 4);
x_67 = lean_ctor_get(x_25, 5);
x_68 = lean_ctor_get(x_25, 6);
x_69 = lean_ctor_get(x_25, 7);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_25);
x_70 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
x_71 = lean_ctor_get(x_26, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_72 = x_26;
} else {
 lean_dec_ref(x_26);
 x_72 = lean_box(0);
}
x_73 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
x_74 = 0;
x_75 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
x_76 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_float(x_76, sizeof(void*)*2, x_73);
lean_ctor_set_float(x_76, sizeof(void*)*2 + 8, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 16, x_74);
x_77 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_78 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_15);
lean_ctor_set(x_78, 2, x_77);
lean_inc(x_10);
lean_ctor_set(x_24, 1, x_78);
lean_ctor_set(x_24, 0, x_10);
x_79 = l_Lean_PersistentArray_push___rarg(x_71, x_24);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 1, 8);
} else {
 x_80 = x_72;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint64(x_80, sizeof(void*)*1, x_70);
x_81 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_81, 0, x_63);
lean_ctor_set(x_81, 1, x_64);
lean_ctor_set(x_81, 2, x_65);
lean_ctor_set(x_81, 3, x_80);
lean_ctor_set(x_81, 4, x_66);
lean_ctor_set(x_81, 5, x_67);
lean_ctor_set(x_81, 6, x_68);
lean_ctor_set(x_81, 7, x_69);
x_82 = lean_st_ref_set(x_8, x_81, x_28);
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
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint64_t x_96; lean_object* x_97; lean_object* x_98; double x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_87 = lean_ctor_get(x_24, 1);
lean_inc(x_87);
lean_dec(x_24);
x_88 = lean_ctor_get(x_25, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_25, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_25, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_25, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_25, 5);
lean_inc(x_92);
x_93 = lean_ctor_get(x_25, 6);
lean_inc(x_93);
x_94 = lean_ctor_get(x_25, 7);
lean_inc(x_94);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 x_95 = x_25;
} else {
 lean_dec_ref(x_25);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
x_97 = lean_ctor_get(x_26, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_98 = x_26;
} else {
 lean_dec_ref(x_26);
 x_98 = lean_box(0);
}
x_99 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
x_100 = 0;
x_101 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
x_102 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_float(x_102, sizeof(void*)*2, x_99);
lean_ctor_set_float(x_102, sizeof(void*)*2 + 8, x_99);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 16, x_100);
x_103 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_104 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_15);
lean_ctor_set(x_104, 2, x_103);
lean_inc(x_10);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_10);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_PersistentArray_push___rarg(x_97, x_105);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(0, 1, 8);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set_uint64(x_107, sizeof(void*)*1, x_96);
if (lean_is_scalar(x_95)) {
 x_108 = lean_alloc_ctor(0, 8, 0);
} else {
 x_108 = x_95;
}
lean_ctor_set(x_108, 0, x_88);
lean_ctor_set(x_108, 1, x_89);
lean_ctor_set(x_108, 2, x_90);
lean_ctor_set(x_108, 3, x_107);
lean_ctor_set(x_108, 4, x_91);
lean_ctor_set(x_108, 5, x_92);
lean_ctor_set(x_108, 6, x_93);
lean_ctor_set(x_108, 7, x_94);
x_109 = lean_st_ref_set(x_8, x_108, x_87);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint64_t x_135; lean_object* x_136; lean_object* x_137; double x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_114 = lean_ctor_get(x_15, 0);
x_115 = lean_ctor_get(x_15, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_15);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_116);
lean_dec(x_116);
x_118 = lean_ctor_get(x_7, 2);
x_119 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1;
lean_inc(x_118);
x_120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_120, 0, x_14);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_118);
x_121 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_2);
x_122 = lean_st_ref_take(x_8, x_115);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 5);
lean_inc(x_131);
x_132 = lean_ctor_get(x_123, 6);
lean_inc(x_132);
x_133 = lean_ctor_get(x_123, 7);
lean_inc(x_133);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 lean_ctor_release(x_123, 6);
 lean_ctor_release(x_123, 7);
 x_134 = x_123;
} else {
 lean_dec_ref(x_123);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get_uint64(x_124, sizeof(void*)*1);
x_136 = lean_ctor_get(x_124, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
x_138 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2;
x_139 = 0;
x_140 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
x_141 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_141, 0, x_1);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set_float(x_141, sizeof(void*)*2, x_138);
lean_ctor_set_float(x_141, sizeof(void*)*2 + 8, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*2 + 16, x_139);
x_142 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
x_143 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_121);
lean_ctor_set(x_143, 2, x_142);
lean_inc(x_10);
if (lean_is_scalar(x_126)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_126;
}
lean_ctor_set(x_144, 0, x_10);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_PersistentArray_push___rarg(x_136, x_144);
if (lean_is_scalar(x_137)) {
 x_146 = lean_alloc_ctor(0, 1, 8);
} else {
 x_146 = x_137;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set_uint64(x_146, sizeof(void*)*1, x_135);
if (lean_is_scalar(x_134)) {
 x_147 = lean_alloc_ctor(0, 8, 0);
} else {
 x_147 = x_134;
}
lean_ctor_set(x_147, 0, x_127);
lean_ctor_set(x_147, 1, x_128);
lean_ctor_set(x_147, 2, x_129);
lean_ctor_set(x_147, 3, x_146);
lean_ctor_set(x_147, 4, x_130);
lean_ctor_set(x_147, 5, x_131);
lean_ctor_set(x_147, 6, x_132);
lean_ctor_set(x_147, 7, x_133);
x_148 = lean_st_ref_set(x_8, x_147, x_125);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_box(0);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__1;
x_3 = l_instInhabitedOfMonad___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__2;
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
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_visitCode), 8, 0);
return x_1;
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
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_32);
x_77 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
lean_inc(x_8);
x_78 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_77, x_34, x_76, x_8, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_35 = x_79;
x_36 = x_80;
goto block_71;
}
else
{
uint8_t x_81; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_73, x_73);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_73);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_72);
lean_ctor_set(x_86, 1, x_72);
lean_ctor_set(x_86, 2, x_32);
x_87 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
lean_inc(x_8);
x_88 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_87, x_34, x_86, x_8, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_35 = x_89;
x_36 = x_90;
goto block_71;
}
else
{
uint8_t x_91; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_96 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_33, x_5, x_95, x_72);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_72);
lean_ctor_set(x_97, 2, x_32);
x_98 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
lean_inc(x_8);
x_99 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_98, x_34, x_97, x_8, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_35 = x_100;
x_36 = x_101;
goto block_71;
}
else
{
uint8_t x_102; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
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
uint8_t x_106; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_29);
if (x_106 == 0)
{
return x_29;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_29, 0);
x_108 = lean_ctor_get(x_29, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_29);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_25);
if (x_110 == 0)
{
return x_25;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_25, 0);
x_112 = lean_ctor_get(x_25, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_25);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_19);
if (x_114 == 0)
{
return x_19;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_19, 0);
x_116 = lean_ctor_get(x_19, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_19);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
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
x_1 = lean_mk_string_unchecked("specialize", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("step", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2;
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
x_1 = lean_mk_string_unchecked("new: ", 5, 5);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cached: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("!key.hasFVar\n    ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize.specializeApp\?", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12;
x_3 = lean_unsigned_to_nat(281u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__11;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("!key.hasLooseBVars\n    ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__9;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__14;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__12;
x_3 = lean_unsigned_to_nat(280u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__15;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasFVar(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_box(0);
lean_inc(x_2);
x_21 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_2, x_20);
x_22 = lean_array_size(x_3);
x_23 = 0;
lean_inc(x_3);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_22, x_23, x_3);
x_25 = l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(x_4, x_5);
x_26 = l_Array_append___rarg(x_24, x_25);
lean_dec(x_25);
x_27 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(x_1, x_15, x_16, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_32 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_6, x_7, x_8, x_3, x_9, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
x_36 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_35, x_11, x_12, x_13, x_14, x_15, x_16, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_27);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_33, x_1, x_21, x_26, x_23, x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_39);
lean_dec(x_11);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
x_46 = l_Lean_MessageData_ofName(x_45);
x_47 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_46);
lean_ctor_set(x_36, 0, x_47);
x_48 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_48);
lean_ctor_set(x_27, 0, x_36);
x_49 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_35, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_43);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_33, x_1, x_21, x_26, x_23, x_50, x_11, x_12, x_13, x_14, x_15, x_16, x_51);
lean_dec(x_11);
lean_dec(x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
x_55 = l_Lean_MessageData_ofName(x_54);
x_56 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_58);
lean_ctor_set(x_27, 0, x_57);
x_59 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_35, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_53);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_33, x_1, x_21, x_26, x_23, x_60, x_11, x_12, x_13, x_14, x_15, x_16, x_61);
lean_dec(x_11);
lean_dec(x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_27);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
return x_32;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_32, 0);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_32);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_dec(x_27);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
x_68 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_6, x_7, x_8, x_3, x_9, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
x_72 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_71, x_11, x_12, x_13, x_14, x_15, x_16, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_box(0);
x_77 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_69, x_1, x_21, x_26, x_23, x_76, x_11, x_12, x_13, x_14, x_15, x_16, x_75);
lean_dec(x_11);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
x_81 = l_Lean_MessageData_ofName(x_80);
x_82 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__5;
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_79;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_71, x_85, x_11, x_12, x_13, x_14, x_15, x_16, x_78);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1(x_69, x_1, x_21, x_26, x_23, x_87, x_11, x_12, x_13, x_14, x_15, x_16, x_88);
lean_dec(x_11);
lean_dec(x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_90 = lean_ctor_get(x_68, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_68, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_92 = x_68;
} else {
 lean_dec_ref(x_68);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_27);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_27, 1);
x_96 = lean_ctor_get(x_27, 0);
lean_dec(x_96);
x_97 = lean_ctor_get(x_28, 0);
lean_inc(x_97);
lean_dec(x_28);
x_98 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
x_99 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_98, x_11, x_12, x_13, x_14, x_15, x_16, x_95);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_27);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_box(0);
x_104 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_97, x_21, x_26, x_103, x_11, x_12, x_13, x_14, x_15, x_16, x_102);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_104;
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_99);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_99, 1);
x_107 = lean_ctor_get(x_99, 0);
lean_dec(x_107);
lean_inc(x_97);
x_108 = l_Lean_MessageData_ofName(x_97);
x_109 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8;
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_108);
lean_ctor_set(x_99, 0, x_109);
x_110 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_110);
lean_ctor_set(x_27, 0, x_99);
x_111 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_98, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_106);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_97, x_21, x_26, x_112, x_11, x_12, x_13, x_14, x_15, x_16, x_113);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_112);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = lean_ctor_get(x_99, 1);
lean_inc(x_115);
lean_dec(x_99);
lean_inc(x_97);
x_116 = l_Lean_MessageData_ofName(x_97);
x_117 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_119);
lean_ctor_set(x_27, 0, x_118);
x_120 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_98, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_115);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_97, x_21, x_26, x_121, x_11, x_12, x_13, x_14, x_15, x_16, x_122);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_124 = lean_ctor_get(x_27, 1);
lean_inc(x_124);
lean_dec(x_27);
x_125 = lean_ctor_get(x_28, 0);
lean_inc(x_125);
lean_dec(x_28);
x_126 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__3;
x_127 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_126, x_11, x_12, x_13, x_14, x_15, x_16, x_124);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_box(0);
x_132 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_125, x_21, x_26, x_131, x_11, x_12, x_13, x_14, x_15, x_16, x_130);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
lean_inc(x_125);
x_135 = l_Lean_MessageData_ofName(x_125);
x_136 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__8;
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(7, 2, 0);
} else {
 x_137 = x_134;
 lean_ctor_set_tag(x_137, 7);
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_126, x_139, x_11, x_12, x_13, x_14, x_15, x_16, x_133);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__2(x_125, x_21, x_26, x_141, x_11, x_12, x_13, x_14, x_15, x_16, x_142);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_141);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__13;
x_145 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7(x_144, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__16;
x_147 = l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7(x_146, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_147;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key: ", 5, 5);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
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
lean_dec(x_22);
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
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_5);
x_32 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_27);
lean_dec(x_5);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_30, x_31, x_20, x_1, x_2, x_6, x_4, x_19, x_21, x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_35);
lean_dec(x_1);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_32, 1);
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
lean_inc(x_30);
x_41 = l_Lean_MessageData_ofExpr(x_30);
x_42 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_42);
x_43 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_43);
lean_ctor_set(x_27, 0, x_32);
x_44 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_5, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_30, x_31, x_20, x_1, x_2, x_6, x_4, x_19, x_21, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_46);
lean_dec(x_45);
lean_dec(x_1);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_dec(x_32);
lean_inc(x_30);
x_49 = l_Lean_MessageData_ofExpr(x_30);
x_50 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_52);
lean_ctor_set(x_27, 0, x_51);
x_53 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_5, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_48);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_30, x_31, x_20, x_1, x_2, x_6, x_4, x_19, x_21, x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_55);
lean_dec(x_54);
lean_dec(x_1);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_27, 0);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_27);
lean_inc(x_5);
x_59 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_box(0);
x_64 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_57, x_58, x_20, x_1, x_2, x_6, x_4, x_19, x_21, x_63, x_8, x_9, x_10, x_11, x_12, x_13, x_62);
lean_dec(x_1);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
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
lean_inc(x_57);
x_67 = l_Lean_MessageData_ofExpr(x_57);
x_68 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___closed__2;
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(7, 2, 0);
} else {
 x_69 = x_66;
 lean_ctor_set_tag(x_69, 7);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_5, x_71, x_8, x_9, x_10, x_11, x_12, x_13, x_65);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3(x_57, x_58, x_20, x_1, x_2, x_6, x_4, x_19, x_21, x_73, x_8, x_9, x_10, x_11, x_12, x_13, x_74);
lean_dec(x_73);
lean_dec(x_1);
return x_75;
}
}
}
else
{
uint8_t x_76; 
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
x_76 = !lean_is_exclusive(x_15);
if (x_76 == 0)
{
return x_15;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_15, 0);
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_15);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("candidate", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2;
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
x_1 = lean_mk_string_unchecked(", ", 2, 2);
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
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_22, 4);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_23);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__2;
x_26 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__2(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(x_2, x_3, x_1, x_4, x_25, x_22, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_33 = lean_ctor_get(x_26, 1);
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
x_35 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_5);
x_36 = l_Lean_MessageData_ofExpr(x_35);
x_37 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_37);
x_38 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_2);
x_40 = lean_array_to_list(x_2);
x_41 = lean_box(0);
x_42 = l_List_mapTR_loop___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__11(x_40, x_41);
x_43 = l_Lean_MessageData_ofList(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
x_46 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_25, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(x_2, x_3, x_1, x_4, x_25, x_22, x_47, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
lean_dec(x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_ctor_get(x_26, 1);
lean_inc(x_50);
lean_dec(x_26);
x_51 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_5);
x_52 = l_Lean_MessageData_ofExpr(x_51);
x_53 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__6;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___closed__4;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_2);
x_57 = lean_array_to_list(x_2);
x_58 = lean_box(0);
x_59 = l_List_mapTR_loop___at_Lean_Compiler_LCNF_saveSpecParamInfo___spec__11(x_57, x_58);
x_60 = l_Lean_MessageData_ofList(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
x_63 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_25, x_62, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(x_2, x_3, x_1, x_4, x_25, x_22, x_64, x_7, x_8, x_9, x_10, x_11, x_12, x_65);
lean_dec(x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_23);
lean_dec(x_22);
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
x_67 = !lean_is_exclusive(x_14);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_14, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_14, 0, x_69);
return x_14;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_dec(x_14);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
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
switch (lean_obj_tag(x_1)) {
case 3:
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
case 4:
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_10);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
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
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_26 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_25, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_1, 4, x_28);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_1, 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_1);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
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
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_22, x_22);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_22);
x_37 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_38 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_37, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_1, 4, x_40);
lean_ctor_set(x_38, 0, x_1);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_1, 4, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_1);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_18, x_48, x_49, x_21);
lean_ctor_set(x_2, 0, x_50);
x_51 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_52 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_51, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_1, 4, x_54);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_1, 4, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_free_object(x_1);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_52);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_ctor_get(x_1, 1);
x_64 = lean_ctor_get(x_1, 2);
x_65 = lean_ctor_get(x_1, 3);
x_66 = lean_ctor_get(x_1, 4);
x_67 = lean_ctor_get(x_1, 5);
x_68 = lean_ctor_get(x_2, 0);
x_69 = lean_ctor_get(x_2, 1);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_2);
x_71 = lean_array_get_size(x_65);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_70);
x_75 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_76 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_75, x_66, x_74, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
lean_ctor_set(x_1, 4, x_77);
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_1);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
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
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_71, x_71);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_71);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_68);
lean_ctor_set(x_86, 1, x_69);
lean_ctor_set(x_86, 2, x_70);
x_87 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_88 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_87, x_66, x_86, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
lean_ctor_set(x_1, 4, x_89);
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_1);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = 0;
x_98 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_99 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_65, x_97, x_98, x_68);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_69);
lean_ctor_set(x_100, 2, x_70);
x_101 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_102 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_101, x_66, x_100, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
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
lean_ctor_set(x_1, 4, x_103);
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_1);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
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
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_111 = lean_ctor_get(x_1, 0);
x_112 = lean_ctor_get(x_1, 1);
x_113 = lean_ctor_get(x_1, 2);
x_114 = lean_ctor_get(x_1, 3);
x_115 = lean_ctor_get(x_1, 4);
x_116 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_117 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_118 = lean_ctor_get(x_1, 5);
lean_inc(x_118);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_1);
x_119 = lean_ctor_get(x_2, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_2, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_2, 2);
lean_inc(x_121);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_122 = x_2;
} else {
 lean_dec_ref(x_2);
 x_122 = lean_box(0);
}
x_123 = lean_array_get_size(x_114);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_dec_lt(x_124, x_123);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_123);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 3, 0);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_120);
lean_ctor_set(x_126, 2, x_121);
x_127 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_128 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_127, x_115, x_126, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_132, 0, x_111);
lean_ctor_set(x_132, 1, x_112);
lean_ctor_set(x_132, 2, x_113);
lean_ctor_set(x_132, 3, x_114);
lean_ctor_set(x_132, 4, x_129);
lean_ctor_set(x_132, 5, x_118);
lean_ctor_set_uint8(x_132, sizeof(void*)*6, x_116);
lean_ctor_set_uint8(x_132, sizeof(void*)*6 + 1, x_117);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_118);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
uint8_t x_138; 
x_138 = lean_nat_dec_le(x_123, x_123);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_123);
if (lean_is_scalar(x_122)) {
 x_139 = lean_alloc_ctor(0, 3, 0);
} else {
 x_139 = x_122;
}
lean_ctor_set(x_139, 0, x_119);
lean_ctor_set(x_139, 1, x_120);
lean_ctor_set(x_139, 2, x_121);
x_140 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_141 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_140, x_115, x_139, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_145, 0, x_111);
lean_ctor_set(x_145, 1, x_112);
lean_ctor_set(x_145, 2, x_113);
lean_ctor_set(x_145, 3, x_114);
lean_ctor_set(x_145, 4, x_142);
lean_ctor_set(x_145, 5, x_118);
lean_ctor_set_uint8(x_145, sizeof(void*)*6, x_116);
lean_ctor_set_uint8(x_145, sizeof(void*)*6 + 1, x_117);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_118);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_153 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_withParams___spec__1(x_114, x_151, x_152, x_119);
if (lean_is_scalar(x_122)) {
 x_154 = lean_alloc_ctor(0, 3, 0);
} else {
 x_154 = x_122;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_120);
lean_ctor_set(x_154, 2, x_121);
x_155 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3;
x_156 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__5(x_155, x_115, x_154, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_160, 0, x_111);
lean_ctor_set(x_160, 1, x_112);
lean_ctor_set(x_160, 2, x_113);
lean_ctor_set(x_160, 3, x_114);
lean_ctor_set(x_160, 4, x_157);
lean_ctor_set(x_160, 5, x_118);
lean_ctor_set_uint8(x_160, sizeof(void*)*6, x_116);
lean_ctor_set_uint8(x_160, sizeof(void*)*6 + 1, x_117);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_118);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
x_162 = lean_ctor_get(x_156, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_156, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_164 = x_156;
} else {
 lean_dec_ref(x_156);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_166 = !lean_is_exclusive(x_9);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_9, 0);
lean_dec(x_167);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_9, 1);
lean_inc(x_168);
lean_dec(x_9);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_168);
return x_169;
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
x_10 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
lean_dec(x_13);
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
x_14 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
x_16 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
x_19 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
x_25 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
x_28 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
x_32 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2;
x_2 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__2;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__3;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__4;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__6;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__8;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__9;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__10;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__11;
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__14;
x_2 = lean_unsigned_to_nat(4327u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__1;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__15;
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
l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__3);
l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry___closed__4);
l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry = _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__1);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__2);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__3);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__4);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__5);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__6 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____lambda__1___closed__6);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__1);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__2);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__3);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__4);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__5 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__5);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__6 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__6);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__7 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__7);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__8 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__8);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__9 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__9);
l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__10 = _init_l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49____closed__10);
if (builtin) {res = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_Specialize_specCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specCacheExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__1);
l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_cacheSpec___closed__2);
l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___closed__1);
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
l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_Collector_collect___closed__3);
l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1 = _init_l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed__const__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Specialize_shouldSpecialize___spec__3___closed__1);
l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___closed__1);
l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__1);
l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___spec__3___closed__2);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__1);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__2);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__3);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go___closed__4);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__1);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__2);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__3);
l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4 = _init_l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___closed__4);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__2();
l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__6___closed__3);
l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__1);
l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___spec__7___closed__2);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__1);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__2);
l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f___lambda__1___closed__3);
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
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327____closed__15);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4327_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
