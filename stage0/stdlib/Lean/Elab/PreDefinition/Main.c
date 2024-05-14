// Lean compiler output
// Module: Lean.Elab.PreDefinition.Main
// Imports: Lean.Util.SCC Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural Lean.Elab.PreDefinition.WF.Main Lean.Elab.PreDefinition.MkInhabitant
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__10(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__23(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__12___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__5;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___boxed(lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addPreDefinitions___lambda__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__1;
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__2(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__1;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__14;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__4;
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__3;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__2;
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l___private_Init_GetElem_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1;
static lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FoldConstsImpl_initCache;
LEAN_EXPORT lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addPreDefinitions___boxed__const__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__9;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__14;
lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__4;
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__10;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___closed__1;
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__4;
lean_object* l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__10;
lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__13;
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__9___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1(lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__11;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__2;
lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__5;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___boxed(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__15;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__4;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__16;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___lambda__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__3;
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_addAutoBoundImplicits_go___spec__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__9(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ensureFunIndReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__12(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(size_t, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__3;
static lean_object* l_Lean_Elab_addPreDefinitions___closed__3;
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_350____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__14(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__3;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__1;
lean_object* l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2;
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1;
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__13;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__11(size_t, size_t, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__2;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed__const__1;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__6(lean_object*, size_t, size_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__5;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___closed__1;
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_Elab_addAndCompileUnsafe___spec__2(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addPreDefinitions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080_(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__8(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14(lean_object*, lean_object*, lean_object*, size_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__15(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_15_(uint8_t, uint8_t);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__23___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Elab_WF_TerminationHints_isNotNone(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_instMonadControlReaderT___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_addPreDefinitions___spec__7(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
static lean_object* l_Lean_Elab_addPreDefinitions___closed__8;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_addPreDefinitions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_TerminationHints_ensureNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__1;
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__15;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__11;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__6;
static lean_object* l_Lean_Elab_addPreDefinitions___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__6;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__6;
lean_object* l_Lean_Expr_headBeta(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_zetaReduce___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20___boxed(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_compileDecl___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__9;
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Elab_addPreDefinitions___closed__4;
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__7;
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_instMonadControlReaderT___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = lean_box(0);
x_12 = 0;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_12, x_11, x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 6);
x_17 = 3;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_2);
lean_ctor_set(x_18, 5, x_4);
lean_ctor_set(x_18, 6, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*7, x_17);
x_19 = 0;
x_20 = 1;
x_21 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_18, x_19, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_4 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Elab_mkInhabitantFor(x_14, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__1(x_1, x_2, x_3, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l_Lean_Meta_mkSorry(x_6, x_23, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 0;
x_28 = 1;
x_29 = l_Lean_Meta_mkLambdaFVars(x_5, x_25, x_27, x_23, x_28, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__1(x_1, x_2, x_3, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_1);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_to_list(lean_box(0), x_1);
x_13 = lean_box(0);
x_14 = l_List_mapTR_loop___at_Lean_Elab_addAndCompileUnsafe___spec__2(x_12, x_13);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
x_16 = lean_box(x_3);
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__2___boxed), 13, 4);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_14);
lean_closure_set(x_17, 3, x_16);
x_18 = l_Lean_Meta_forallTelescope___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___rarg(x_15, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("processing ", 11);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__3;
x_18 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_23 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3(x_1, x_16, x_2, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = 1;
x_34 = lean_usize_add(x_5, x_33);
x_5 = x_34;
x_6 = x_32;
x_13 = x_31;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
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
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_18, 1);
x_42 = lean_ctor_get(x_18, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_16, 3);
lean_inc(x_43);
x_44 = l_Lean_MessageData_ofName(x_43);
x_45 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__5;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_44);
lean_ctor_set(x_18, 0, x_45);
x_46 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_18);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_17, x_47, x_7, x_8, x_9, x_10, x_11, x_12, x_41);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_51 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3(x_1, x_16, x_2, x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_51, 0, x_55);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; 
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_dec(x_51);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
lean_dec(x_52);
x_61 = 1;
x_62 = lean_usize_add(x_5, x_61);
x_5 = x_62;
x_6 = x_60;
x_13 = x_59;
goto _start;
}
}
else
{
uint8_t x_64; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_51, 0);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_dec(x_18);
x_69 = lean_ctor_get(x_16, 3);
lean_inc(x_69);
x_70 = l_Lean_MessageData_ofName(x_69);
x_71 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__5;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_17, x_74, x_7, x_8, x_9, x_10, x_11, x_12, x_68);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_78 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3(x_1, x_16, x_2, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
lean_dec(x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; 
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
lean_dec(x_79);
x_86 = 1;
x_87 = lean_usize_add(x_5, x_86);
x_5 = x_87;
x_6 = x_85;
x_13 = x_84;
goto _start;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_89 = lean_ctor_get(x_78, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_91 = x_78;
} else {
 lean_dec_ref(x_78);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2(x_1, x_2, x_1, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_addAndCompilePartialRec(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__2(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2(x_1, x_14, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_name_eq(x_4, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_instInhabitedPreDefinition;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__15(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash___override(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__15(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__14(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_1, x_2, x_8);
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
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(x_13, x_15);
return x_18;
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Name_hash___override(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_11 = 1;
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_11);
x_13 = l_Lean_HashMap_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_6, x_1, x_12);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_17, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_24 = 1;
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = l_Lean_HashMap_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_18, x_1, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_1);
lean_inc(x_5);
x_6 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_1(x_2, x_9);
x_11 = l_Lean_HashMap_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_5, x_1, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_3, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_16);
x_18 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(x_16, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_apply_1(x_2, x_22);
x_24 = l_Lean_HashMap_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_16, x_1, x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_17);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
return x_2;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_nat_dec_lt(x_16, x_18);
if (x_19 == 0)
{
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_dec(x_18);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_nat_dec_lt(x_16, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_2, 1, x_22);
return x_2;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_2, 1, x_23);
return x_2;
}
}
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_28 = x_1;
} else {
 lean_dec_ref(x_1);
 x_28 = lean_box(0);
}
x_29 = lean_nat_dec_lt(x_26, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_26);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_25);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_7);
x_9 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_7, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(x_1, x_7, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_2);
x_19 = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(x_2, x_18, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_3 = x_8;
x_4 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
x_22 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
lean_dec(x_10);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_11);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_3 = x_8;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
lean_inc(x_2);
x_26 = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(x_2, x_11, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_3 = x_8;
x_4 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_6);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___closed__1;
x_4 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_4, 3, x_9);
lean_ctor_set(x_4, 0, x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___lambda__1), 1, 0);
lean_inc(x_20);
x_23 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_20, x_22, x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_inc(x_20);
lean_ctor_set(x_2, 1, x_3);
x_27 = lean_name_eq(x_1, x_20);
lean_dec(x_20);
if (x_27 == 0)
{
lean_free_object(x_23);
{
lean_object* _tmp_1 = x_21;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_25;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 3);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_25, 3, x_32);
lean_ctor_set(x_25, 0, x_21);
x_33 = lean_box(0);
lean_ctor_set(x_23, 0, x_33);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_25, 1);
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_box(0);
lean_ctor_set(x_23, 1, x_38);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_dec(x_23);
lean_inc(x_20);
lean_ctor_set(x_2, 1, x_3);
x_41 = lean_name_eq(x_1, x_20);
lean_dec(x_20);
if (x_41 == 0)
{
{
lean_object* _tmp_1 = x_21;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_40;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 3);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_45);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 4, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_53 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___lambda__1), 1, 0);
lean_inc(x_51);
x_54 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_51, x_53, x_4);
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
lean_inc(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_3);
x_58 = lean_name_eq(x_1, x_51);
lean_dec(x_51);
if (x_58 == 0)
{
lean_dec(x_56);
x_2 = x_52;
x_3 = x_57;
x_4 = x_55;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 3);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 4, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_56;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_4 = l___private_Lean_Util_SCC_0__Lean_SCC_push___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__10(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_apply_1(x_1, x_2);
lean_inc(x_2);
x_7 = l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__19(x_1, x_2, x_6, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_350____spec__1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; 
lean_free_object(x_9);
x_17 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(x_2, x_12);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_350____spec__1(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(x_2, x_19);
lean_dec(x_2);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_6);
x_8 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_6, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_1);
x_12 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(x_1, x_6, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_6);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_2 = x_7;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_Lean_mkHashMapImp___rarg(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_3);
x_8 = l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__24(x_2, x_1, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_List_reverse___rarg(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__2;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__4;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__5;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__1;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(x_6, x_12, x_1, x_10, x_11, x_12);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; 
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__3;
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7;
x_19 = l_panic___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(x_18);
x_20 = lean_array_uset(x_8, x_3, x_19);
x_3 = x_16;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_array_uset(x_8, x_3, x_22);
x_3 = x_16;
x_4 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7;
x_27 = l_panic___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(x_26);
x_28 = lean_array_uset(x_8, x_3, x_27);
x_3 = x_16;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_array_uset(x_8, x_3, x_30);
x_3 = x_16;
x_4 = x_31;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_List_redLength___rarg(x_6);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_6, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(x_1, x_13, x_14, x_11);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_8, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_9; 
x_9 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(x_5, x_2, x_3, x_4);
if (x_9 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_usize_of_nat(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__1;
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(x_3, x_7, x_1, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed__const__1;
x_11 = lean_box_usize(x_5);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__1___boxed), 6, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_11);
x_13 = 8191;
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_14; 
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__3;
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7;
x_16 = l_panic___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(x_15);
x_17 = lean_ctor_get(x_16, 5);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Expr_FoldConstsImpl_initCache;
x_19 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_12, x_13, x_17, x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 5);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_FoldConstsImpl_initCache;
x_24 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_12, x_13, x_22, x_2, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7;
x_28 = l_panic___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(x_27);
x_29 = lean_ctor_get(x_28, 5);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Expr_FoldConstsImpl_initCache;
x_31 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_12, x_13, x_29, x_2, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_ctor_get(x_33, 5);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Expr_FoldConstsImpl_initCache;
x_36 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_12, x_13, x_34, x_2, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
lean_inc(x_1);
x_2 = lean_array_to_list(lean_box(0), x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lean_Elab_addAndCompileUnsafe___spec__2(x_2, x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5(x_4, x_5);
x_7 = l_List_redLength___rarg(x_6);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
x_9 = l_List_toArrayAux___rarg(x_6, x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(x_1, x_11, x_12, x_9);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__23___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__23(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
x_9 = l_Lean_Meta_collectMVars(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_collectMVars(x_11, x_2, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__3;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortCommandExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_9 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
x_26 = lean_ctor_get(x_1, 4);
x_27 = lean_ctor_get(x_1, 6);
x_28 = lean_ctor_get(x_1, 5);
lean_dec(x_28);
x_29 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_26);
x_30 = l_Lean_Meta_mkSorry(x_26, x_29, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_ctor_set(x_1, 5, x_31);
lean_inc(x_1);
x_33 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(x_1, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_Array_isEmpty___rarg(x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_free_object(x_33);
lean_dec(x_1);
x_38 = l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg(x_36);
return x_38;
}
else
{
lean_ctor_set(x_33, 0, x_1);
return x_33;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = l_Array_isEmpty___rarg(x_39);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_1);
x_42 = l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg(x_40);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_1);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get(x_1, 3);
x_53 = lean_ctor_get(x_1, 4);
x_54 = lean_ctor_get(x_1, 6);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_dec(x_1);
x_55 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_53);
x_56 = l_Lean_Meta_mkSorry(x_53, x_55, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_50);
lean_ctor_set(x_59, 2, x_51);
lean_ctor_set(x_59, 3, x_52);
lean_ctor_set(x_59, 4, x_53);
lean_ctor_set(x_59, 5, x_57);
lean_ctor_set(x_59, 6, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*7, x_49);
lean_inc(x_59);
x_60 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(x_59, x_4, x_5, x_6, x_7, x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_Array_isEmpty___rarg(x_61);
lean_dec(x_61);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_63);
lean_dec(x_59);
x_65 = l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg(x_62);
return x_65;
}
else
{
lean_object* x_66; 
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
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
}
}
else
{
uint8_t x_71; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Expr_constName_x21(x_1);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_getAppFn(x_6);
lean_dec(x_6);
x_8 = l_Lean_Expr_isConst(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_7);
x_13 = 1;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__1(x_7, x_1, x_14, x_15);
lean_dec(x_7);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
goto _start;
}
}
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_12 = lean_apply_6(x_2, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_21, x_6, x_7, x_8, x_9, x_10, x_20);
return x_22;
}
default: 
{
lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_12, 0);
lean_dec(x_25);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_12, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_uget(x_7, x_6);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_7, x_6, x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_6, x_22);
x_24 = lean_array_uset(x_18, x_6, x_20);
x_6 = x_23;
x_7 = x_24;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_array_set(x_6, x_7, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_7, x_17);
lean_dec(x_7);
x_5 = x_14;
x_6 = x_16;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_6);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__6(x_1, x_2, x_3, x_4, x_24, x_25, x_6, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_mkAppN(x_21, x_27);
x_30 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_29, x_8, x_9, x_10, x_11, x_12, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 10);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*11);
x_21 = lean_nat_dec_eq(x_12, x_13);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_6, 10);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 9);
lean_dec(x_24);
x_25 = lean_ctor_get(x_6, 8);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 7);
lean_dec(x_26);
x_27 = lean_ctor_get(x_6, 6);
lean_dec(x_27);
x_28 = lean_ctor_get(x_6, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_6, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_6, 3);
lean_dec(x_30);
x_31 = lean_ctor_get(x_6, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_6, 0);
lean_dec(x_33);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_12, x_34);
lean_dec(x_12);
lean_ctor_set(x_6, 3, x_35);
x_36 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_6);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_12, x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_10);
lean_ctor_set(x_47, 2, x_11);
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 4, x_13);
lean_ctor_set(x_47, 5, x_14);
lean_ctor_set(x_47, 6, x_15);
lean_ctor_set(x_47, 7, x_16);
lean_ctor_set(x_47, 8, x_17);
lean_ctor_set(x_47, 9, x_18);
lean_ctor_set(x_47, 10, x_19);
lean_ctor_set_uint8(x_47, sizeof(void*)*11, x_20);
x_48 = lean_apply_6(x_2, x_3, x_4, x_5, x_47, x_7, x_8);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg(x_14, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_162; lean_object* x_163; 
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
x_162 = lean_ctor_get(x_6, 0);
lean_inc(x_162);
lean_dec(x_6);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_12);
return x_163;
}
case 1:
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_5);
x_164 = lean_ctor_get(x_6, 0);
lean_inc(x_164);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_165 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_164, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_166, x_7, x_8, x_9, x_10, x_11, x_167);
return x_168;
}
else
{
uint8_t x_169; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_165);
if (x_169 == 0)
{
return x_165;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_165, 0);
x_171 = lean_ctor_get(x_165, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_165);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
default: 
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_6, 0);
lean_inc(x_173);
lean_dec(x_6);
if (lean_obj_tag(x_173) == 0)
{
x_13 = x_5;
goto block_161;
}
else
{
lean_object* x_174; 
lean_dec(x_5);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec(x_173);
x_13 = x_174;
goto block_161;
}
}
}
block_161:
{
switch (lean_obj_tag(x_13)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_14);
x_16 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__7(x_1, x_2, x_3, x_4, x_13, x_17, x_19, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
case 6:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_13, sizeof(void*)*3 + 8);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_22, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_23, x_7, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_31 = l_Lean_Expr_lam___override(x_21, x_22, x_23, x_24);
x_32 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_33 = lean_ptr_addr(x_26);
x_34 = lean_usize_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_23);
x_35 = l_Lean_Expr_lam___override(x_21, x_26, x_29, x_24);
x_36 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_35, x_7, x_8, x_9, x_10, x_11, x_30);
return x_36;
}
else
{
size_t x_37; size_t x_38; uint8_t x_39; 
x_37 = lean_ptr_addr(x_23);
lean_dec(x_23);
x_38 = lean_ptr_addr(x_29);
x_39 = lean_usize_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_40 = l_Lean_Expr_lam___override(x_21, x_26, x_29, x_24);
x_41 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_40, x_7, x_8, x_9, x_10, x_11, x_30);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_24, x_24);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_31);
x_43 = l_Lean_Expr_lam___override(x_21, x_26, x_29, x_24);
x_44 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_43, x_7, x_8, x_9, x_10, x_11, x_30);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_21);
x_45 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_31, x_7, x_8, x_9, x_10, x_11, x_30);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
return x_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 0);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
return x_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
case 7:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_13, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_13, 2);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_13, sizeof(void*)*3 + 8);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_55);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_55, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_56);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_61 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_56, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
x_64 = l_Lean_Expr_forallE___override(x_54, x_55, x_56, x_57);
x_65 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_66 = lean_ptr_addr(x_59);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
lean_dec(x_56);
x_68 = l_Lean_Expr_forallE___override(x_54, x_59, x_62, x_57);
x_69 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_68, x_7, x_8, x_9, x_10, x_11, x_63);
return x_69;
}
else
{
size_t x_70; size_t x_71; uint8_t x_72; 
x_70 = lean_ptr_addr(x_56);
lean_dec(x_56);
x_71 = lean_ptr_addr(x_62);
x_72 = lean_usize_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
x_73 = l_Lean_Expr_forallE___override(x_54, x_59, x_62, x_57);
x_74 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_73, x_7, x_8, x_9, x_10, x_11, x_63);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_57, x_57);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
x_76 = l_Lean_Expr_forallE___override(x_54, x_59, x_62, x_57);
x_77 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_76, x_7, x_8, x_9, x_10, x_11, x_63);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_54);
x_78 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_64, x_7, x_8, x_9, x_10, x_11, x_63);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_58);
if (x_83 == 0)
{
return x_58;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_58, 0);
x_85 = lean_ctor_get(x_58, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_58);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_13, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_13, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_13, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_13, 3);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_13, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_88);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_92 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_88, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_89);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_95 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_89, x_7, x_8, x_9, x_10, x_11, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_90);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_98 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_90, x_7, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ptr_addr(x_88);
lean_dec(x_88);
x_102 = lean_ptr_addr(x_93);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_13);
x_104 = l_Lean_Expr_letE___override(x_87, x_93, x_96, x_99, x_91);
x_105 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_104, x_7, x_8, x_9, x_10, x_11, x_100);
return x_105;
}
else
{
size_t x_106; size_t x_107; uint8_t x_108; 
x_106 = lean_ptr_addr(x_89);
lean_dec(x_89);
x_107 = lean_ptr_addr(x_96);
x_108 = lean_usize_dec_eq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_90);
lean_dec(x_13);
x_109 = l_Lean_Expr_letE___override(x_87, x_93, x_96, x_99, x_91);
x_110 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_109, x_7, x_8, x_9, x_10, x_11, x_100);
return x_110;
}
else
{
size_t x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_13);
x_114 = l_Lean_Expr_letE___override(x_87, x_93, x_96, x_99, x_91);
x_115 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_114, x_7, x_8, x_9, x_10, x_11, x_100);
return x_115;
}
else
{
lean_object* x_116; 
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_87);
x_116 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_13, x_7, x_8, x_9, x_10, x_11, x_100);
return x_116;
}
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_98);
if (x_117 == 0)
{
return x_98;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_98, 0);
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_98);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_95);
if (x_121 == 0)
{
return x_95;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_95, 0);
x_123 = lean_ctor_get(x_95, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_95);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_92);
if (x_125 == 0)
{
return x_92;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_92, 0);
x_127 = lean_ctor_get(x_92, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_92);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
case 10:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_13, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_13, 1);
lean_inc(x_130);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_130);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_131 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_130, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; size_t x_134; size_t x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ptr_addr(x_130);
lean_dec(x_130);
x_135 = lean_ptr_addr(x_132);
x_136 = lean_usize_dec_eq(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_13);
x_137 = l_Lean_Expr_mdata___override(x_129, x_132);
x_138 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_137, x_7, x_8, x_9, x_10, x_11, x_133);
return x_138;
}
else
{
lean_object* x_139; 
lean_dec(x_132);
lean_dec(x_129);
x_139 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_13, x_7, x_8, x_9, x_10, x_11, x_133);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_131);
if (x_140 == 0)
{
return x_131;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
case 11:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_13, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_13, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_13, 2);
lean_inc(x_146);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_146);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_147 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_1, x_2, x_3, x_4, x_146, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; size_t x_150; size_t x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ptr_addr(x_146);
lean_dec(x_146);
x_151 = lean_ptr_addr(x_148);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_13);
x_153 = l_Lean_Expr_proj___override(x_144, x_145, x_148);
x_154 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_153, x_7, x_8, x_9, x_10, x_11, x_149);
return x_154;
}
else
{
lean_object* x_155; 
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_144);
x_155 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_13, x_7, x_8, x_9, x_10, x_11, x_149);
return x_155;
}
}
else
{
uint8_t x_156; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_147);
if (x_156 == 0)
{
return x_147;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_147, 0);
x_158 = lean_ctor_get(x_147, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_147);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
default: 
{
lean_object* x_160; 
x_160 = l_Lean_Core_transform_visit_visitPost___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__5(x_1, x_2, x_3, x_4, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_160;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_3, x_1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_6);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = lean_apply_7(x_4, lean_box(0), x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_5);
x_17 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_15, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_13);
lean_inc(x_1);
lean_inc(x_5);
x_18 = lean_apply_1(x_1, x_5);
x_19 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1), 12, 5);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_zetaReduce___spec__14___rarg), 8, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Core_withIncRecDepth___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__8(x_3, x_21, x_6, x_7, x_8, x_9, x_10, x_16);
lean_dec(x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__2), 3, 2);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_23);
x_26 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_26, 0, x_6);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_apply_7(x_4, lean_box(0), x_26, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_23);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_23);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_40);
return x_13;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
lean_inc(x_5);
x_43 = l_Lean_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_41, x_5);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_1);
lean_inc(x_5);
x_44 = lean_apply_1(x_1, x_5);
x_45 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1), 12, 5);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_2);
lean_closure_set(x_46, 2, x_3);
lean_closure_set(x_46, 3, x_4);
lean_closure_set(x_46, 4, x_5);
x_47 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_zetaReduce___spec__14___rarg), 8, 2);
lean_closure_set(x_47, 0, x_45);
lean_closure_set(x_47, 1, x_46);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_48 = l_Lean_Core_withIncRecDepth___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__8(x_3, x_47, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_3);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__2), 3, 2);
lean_closure_set(x_51, 0, x_5);
lean_closure_set(x_51, 1, x_49);
x_52 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_52, 0, x_6);
lean_closure_set(x_52, 1, x_51);
x_53 = lean_apply_7(x_4, lean_box(0), x_52, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_63 = x_48;
} else {
 lean_dec_ref(x_48);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_43, 0);
lean_inc(x_65);
lean_dec(x_43);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_42);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_13);
if (x_67 == 0)
{
return x_13;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_13, 0);
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_13);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_apply_1(x_2, x_7);
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
static lean_object* _init_l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
x_10 = l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__1;
x_11 = l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__2;
x_12 = lean_st_mk_ref(x_11, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4(x_2, x_3, x_9, x_10, x_1, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
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
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isApp(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_getAppFn(x_2);
x_12 = l_Lean_Expr_isLambda(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_15);
x_17 = l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
lean_inc(x_2);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_18, x_20);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_15, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
x_24 = l_Lean_Expr_headBeta(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_29 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__2(x_1, x_21, x_27, x_28);
lean_dec(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Expr_headBeta(x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 2);
x_19 = lean_ctor_get(x_12, 3);
x_20 = lean_ctor_get(x_12, 4);
x_21 = lean_ctor_get(x_12, 5);
x_22 = lean_ctor_get(x_12, 6);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___boxed), 7, 1);
lean_closure_set(x_23, 0, x_1);
x_24 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3(x_21, x_23, x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_12, 5, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_30 = lean_array_uset(x_14, x_3, x_12);
x_3 = x_29;
x_4 = x_30;
x_9 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_free_object(x_12);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get_uint8(x_12, sizeof(void*)*7);
x_38 = lean_ctor_get(x_12, 1);
x_39 = lean_ctor_get(x_12, 2);
x_40 = lean_ctor_get(x_12, 3);
x_41 = lean_ctor_get(x_12, 4);
x_42 = lean_ctor_get(x_12, 5);
x_43 = lean_ctor_get(x_12, 6);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_36);
lean_dec(x_12);
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___boxed), 7, 1);
lean_closure_set(x_44, 0, x_1);
x_45 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3(x_42, x_44, x_45, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_38);
lean_ctor_set(x_49, 2, x_39);
lean_ctor_set(x_49, 3, x_40);
lean_ctor_set(x_49, 4, x_41);
lean_ctor_set(x_49, 5, x_47);
lean_ctor_set(x_49, 6, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*7, x_37);
x_50 = 1;
x_51 = lean_usize_add(x_3, x_50);
x_52 = lean_array_uset(x_14, x_3, x_49);
x_3 = x_51;
x_4 = x_52;
x_9 = x_48;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
lean_inc(x_1);
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10(x_1, x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__6(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_withIncRecDepth___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = 1;
x_17 = l_Lean_Elab_Term_addTermInfo_x27(x_13, x_11, x_14, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 4);
lean_inc(x_17);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 3);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_addDecl(x_22, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_14);
x_25 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___lambda__1), 9, 2);
lean_closure_set(x_25, 0, x_15);
lean_closure_set(x_25, 1, x_14);
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(x_25, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__2;
x_30 = lean_array_push(x_29, x_14);
x_31 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l_Lean_Elab_applyAttributesOf(x_30, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Lean_Elab_applyAttributesOf(x_30, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_39 = lean_box(0);
x_3 = x_38;
x_4 = x_39;
x_11 = x_36;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_23);
if (x_53 == 0)
{
return x_23;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
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
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to declare `", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` because `", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` has already been declared", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lean_MessageData_ofName(x_1);
x_9 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_MessageData_ofName(x_2);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__6;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_8 = l_Lean_Name_str___override(x_1, x_2);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
x_14 = l_Lean_Environment_contains(x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; 
lean_free_object(x_9);
x_16 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
x_20 = l_Lean_Environment_contains(x_19, x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_18);
return x_23;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("induct", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
x_26 = l_Lean_replaceRef(x_12, x_19);
lean_dec(x_12);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_27 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set(x_27, 4, x_18);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_20);
lean_ctor_set(x_27, 7, x_21);
lean_ctor_set(x_27, 8, x_22);
lean_ctor_set(x_27, 9, x_23);
lean_ctor_set(x_27, 10, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*11, x_25);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___closed__1;
x_29 = l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(x_13, x_28, x_5, x_6, x_27, x_8, x_9);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 1;
x_33 = lean_usize_add(x_2, x_32);
x_2 = x_33;
x_4 = x_30;
x_9 = x_31;
goto _start;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
}
}
static lean_object* _init_l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mutual_induct", 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ensureFunIndReservedNamesAvailable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_68; uint8_t x_69; 
x_7 = lean_array_get_size(x_1);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_lt(x_68, x_7);
if (x_69 == 0)
{
x_8 = x_6;
goto block_67;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_7, x_7);
if (x_70 == 0)
{
x_8 = x_6;
goto block_67;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = 0;
x_72 = lean_usize_of_nat(x_7);
x_73 = lean_box(0);
x_74 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3(x_1, x_71, x_72, x_73, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_8 = x_75;
goto block_67;
}
else
{
uint8_t x_76; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
block_67:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_7);
lean_dec(x_7);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_4, 5);
x_13 = l_Lean_Elab_instInhabitedPreDefinition;
x_14 = l___private_Init_GetElem_0__outOfBounds___rarg(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_replaceRef(x_15, x_12);
lean_dec(x_12);
lean_dec(x_15);
lean_ctor_set(x_4, 5, x_17);
x_18 = l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1;
x_19 = l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(x_16, x_18, x_2, x_3, x_4, x_5, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_ctor_get(x_4, 4);
x_25 = lean_ctor_get(x_4, 5);
x_26 = lean_ctor_get(x_4, 6);
x_27 = lean_ctor_get(x_4, 7);
x_28 = lean_ctor_get(x_4, 8);
x_29 = lean_ctor_get(x_4, 9);
x_30 = lean_ctor_get(x_4, 10);
x_31 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_32 = l_Lean_Elab_instInhabitedPreDefinition;
x_33 = l___private_Init_GetElem_0__outOfBounds___rarg(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_replaceRef(x_34, x_25);
lean_dec(x_25);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_22);
lean_ctor_set(x_37, 3, x_23);
lean_ctor_set(x_37, 4, x_24);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set(x_37, 6, x_26);
lean_ctor_set(x_37, 7, x_27);
lean_ctor_set(x_37, 8, x_28);
lean_ctor_set(x_37, 9, x_29);
lean_ctor_set(x_37, 10, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*11, x_31);
x_38 = l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1;
x_39 = l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(x_35, x_38, x_2, x_3, x_37, x_5, x_8);
lean_dec(x_5);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_4);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_4, 5);
x_42 = lean_array_fget(x_1, x_9);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_replaceRef(x_43, x_41);
lean_dec(x_41);
lean_dec(x_43);
lean_ctor_set(x_4, 5, x_45);
x_46 = l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1;
x_47 = l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(x_44, x_46, x_2, x_3, x_4, x_5, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
x_50 = lean_ctor_get(x_4, 2);
x_51 = lean_ctor_get(x_4, 3);
x_52 = lean_ctor_get(x_4, 4);
x_53 = lean_ctor_get(x_4, 5);
x_54 = lean_ctor_get(x_4, 6);
x_55 = lean_ctor_get(x_4, 7);
x_56 = lean_ctor_get(x_4, 8);
x_57 = lean_ctor_get(x_4, 9);
x_58 = lean_ctor_get(x_4, 10);
x_59 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
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
lean_dec(x_4);
x_60 = lean_array_fget(x_1, x_9);
lean_dec(x_1);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 3);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_replaceRef(x_61, x_53);
lean_dec(x_53);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_49);
lean_ctor_set(x_64, 2, x_50);
lean_ctor_set(x_64, 3, x_51);
lean_ctor_set(x_64, 4, x_52);
lean_ctor_set(x_64, 5, x_63);
lean_ctor_set(x_64, 6, x_54);
lean_ctor_set(x_64, 7, x_55);
lean_ctor_set(x_64, 8, x_56);
lean_ctor_set(x_64, 9, x_57);
lean_ctor_set(x_64, 10, x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*11, x_59);
x_65 = l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1;
x_66 = l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(x_62, x_65, x_2, x_3, x_64, x_5, x_8);
lean_dec(x_5);
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_2);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ensureReservedNameAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
static double _init_l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; double x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_16, 3);
x_20 = l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
x_21 = 0;
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6;
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2;
x_25 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_10);
lean_ctor_set(x_14, 1, x_25);
lean_ctor_set(x_14, 0, x_10);
x_26 = l_Lean_PersistentArray_push___rarg(x_19, x_14);
lean_ctor_set(x_16, 3, x_26);
x_27 = lean_st_ref_set(x_8, x_16, x_18);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; double x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_14, 1);
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
x_37 = lean_ctor_get(x_16, 2);
x_38 = lean_ctor_get(x_16, 3);
x_39 = lean_ctor_get(x_16, 4);
x_40 = lean_ctor_get(x_16, 5);
x_41 = lean_ctor_get(x_16, 6);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_42 = l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
x_43 = 0;
x_44 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6;
x_45 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_float(x_45, sizeof(void*)*2, x_42);
lean_ctor_set_float(x_45, sizeof(void*)*2 + 8, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*2 + 16, x_43);
x_46 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2;
x_47 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_47, 2, x_46);
lean_inc(x_10);
lean_ctor_set(x_14, 1, x_47);
lean_ctor_set(x_14, 0, x_10);
x_48 = l_Lean_PersistentArray_push___rarg(x_38, x_14);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_49, 2, x_37);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_39);
lean_ctor_set(x_49, 5, x_40);
lean_ctor_set(x_49, 6, x_41);
x_50 = lean_st_ref_set(x_8, x_49, x_34);
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
x_53 = lean_box(0);
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
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; double x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 6);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
x_65 = l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
x_66 = 0;
x_67 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6;
x_68 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_float(x_68, sizeof(void*)*2, x_65);
lean_ctor_set_float(x_68, sizeof(void*)*2 + 8, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 16, x_66);
x_69 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2;
x_70 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_12);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_10);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_10);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_PersistentArray_push___rarg(x_60, x_71);
if (lean_is_scalar(x_64)) {
 x_73 = lean_alloc_ctor(0, 7, 0);
} else {
 x_73 = x_64;
}
lean_ctor_set(x_73, 0, x_57);
lean_ctor_set(x_73, 1, x_58);
lean_ctor_set(x_73, 2, x_59);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_61);
lean_ctor_set(x_73, 5, x_62);
lean_ctor_set(x_73, 6, x_63);
x_74 = lean_st_ref_set(x_8, x_73, x_56);
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
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("body", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=\n", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_dec(x_14);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_box(0);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_25 = lean_ctor_get(x_16, 1);
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_14, 3);
lean_inc(x_27);
x_28 = l_Lean_MessageData_ofName(x_27);
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_29);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_ctor_get(x_14, 4);
lean_inc(x_32);
x_33 = l_Lean_MessageData_ofExpr(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__6;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_ctor_get(x_14, 5);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_MessageData_ofExpr(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_29);
x_41 = l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1(x_15, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = 1;
x_44 = lean_usize_add(x_3, x_43);
x_45 = lean_box(0);
x_3 = x_44;
x_4 = x_45;
x_11 = x_42;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_dec(x_16);
x_48 = lean_ctor_get(x_14, 3);
lean_inc(x_48);
x_49 = l_Lean_MessageData_ofName(x_48);
x_50 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_ctor_get(x_14, 4);
lean_inc(x_54);
x_55 = l_Lean_MessageData_ofExpr(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__6;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_14, 5);
lean_inc(x_59);
lean_dec(x_14);
x_60 = l_Lean_MessageData_ofExpr(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
x_63 = l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1(x_15, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = 1;
x_66 = lean_usize_add(x_3, x_65);
x_67 = lean_box(0);
x_3 = x_66;
x_4 = x_67;
x_11 = x_64;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_15, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
lean_dec(x_5);
x_7 = 4;
x_8 = l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_15_(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(size_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_array_uget(x_5, x_6);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_15_(x_10, x_11);
if (x_12 == 0)
{
if (x_4 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
goto _start;
}
else
{
size_t x_16; uint8_t x_17; 
x_16 = lean_usize_of_nat(x_3);
x_17 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(x_2, x_1, x_16);
if (x_17 == 0)
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_6, x_18);
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
}
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = lean_usize_add(x_6, x_22);
x_6 = x_23;
goto _start;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__6(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
lean_dec(x_5);
x_7 = 1;
x_8 = l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_15_(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_addPreDefinitions___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
x_10 = l_Lean_MessageData_ofExpr(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_const___override(x_14, x_15);
x_17 = l_Lean_MessageData_ofExpr(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_13;
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__8(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 6);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_WF_TerminationHints_isNotNone(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__9(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Modifiers_isPartial(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid use of 'partial', '", 27);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a function", 19);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_16 = l_Lean_Meta_whnfD(x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = l_Lean_Elab_Modifiers_isPartial(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
size_t x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_box(0);
x_3 = x_22;
x_4 = x_23;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
x_25 = l_Lean_Expr_isForall(x_17);
lean_dec(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 3);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_Lean_MessageData_ofName(x_27);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_indentExpr(x_15);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_9, 5);
x_39 = l_Lean_replaceRef(x_26, x_38);
lean_dec(x_38);
lean_dec(x_26);
lean_ctor_set(x_9, 5, x_39);
x_40 = l_Lean_throwError___at_Lean_Elab_Term_addAutoBoundImplicits_go___spec__50(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
x_47 = lean_ctor_get(x_9, 2);
x_48 = lean_ctor_get(x_9, 3);
x_49 = lean_ctor_get(x_9, 4);
x_50 = lean_ctor_get(x_9, 5);
x_51 = lean_ctor_get(x_9, 6);
x_52 = lean_ctor_get(x_9, 7);
x_53 = lean_ctor_get(x_9, 8);
x_54 = lean_ctor_get(x_9, 9);
x_55 = lean_ctor_get(x_9, 10);
x_56 = lean_ctor_get_uint8(x_9, sizeof(void*)*11);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_57 = l_Lean_replaceRef(x_26, x_50);
lean_dec(x_50);
lean_dec(x_26);
x_58 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_57);
lean_ctor_set(x_58, 6, x_51);
lean_ctor_set(x_58, 7, x_52);
lean_ctor_set(x_58, 8, x_53);
lean_ctor_set(x_58, 9, x_54);
lean_ctor_set(x_58, 10, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*11, x_56);
x_59 = l_Lean_throwError___at_Lean_Elab_Term_addAutoBoundImplicits_go___spec__50(x_36, x_5, x_6, x_7, x_8, x_58, x_10, x_18);
lean_dec(x_10);
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
lean_dec(x_15);
lean_dec(x_14);
x_64 = 1;
x_65 = lean_usize_add(x_3, x_64);
x_66 = lean_box(0);
x_3 = x_65;
x_4 = x_66;
x_11 = x_18;
goto _start;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_16);
if (x_68 == 0)
{
return x_16;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_16, 0);
x_70 = lean_ctor_get(x_16, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_16);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("partial", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 6);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___closed__1;
lean_inc(x_9);
x_16 = l_Lean_Elab_WF_TerminationHints_ensureNone(x_14, x_15, x_9, x_10, x_11);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__12(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 3);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unsafe", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 6);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___closed__1;
lean_inc(x_9);
x_16 = l_Lean_Elab_WF_TerminationHints_ensureNone(x_14, x_15, x_9, x_10, x_11);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("not recursive", 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 6);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___closed__1;
x_12 = l_Lean_Elab_WF_TerminationHints_ensureNone(x_10, x_11, x_7, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fail to show termination for", 28);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nwith errors\n", 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_array_to_list(lean_box(0), x_1);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_Lean_Elab_addPreDefinitions___spec__7(x_3, x_4);
x_6 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
x_7 = l_Lean_MessageData_joinSep(x_5, x_6);
x_8 = l_Lean_indentD(x_7);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__5;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_Structural_structuralRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
x_25 = l_Lean_Exception_isRuntime(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_free_object(x_17);
x_26 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_12, x_4, x_5, x_6, x_7, x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_st_ref_take(x_5, x_28);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_ctor_set(x_32, 0, x_16);
x_36 = lean_st_ref_set(x_5, x_32, x_34);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
x_41 = l_Lean_Elab_wfRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_free_object(x_23);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_free_object(x_26);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = l_Lean_Exception_isRuntime(x_47);
if (x_48 == 0)
{
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_52);
lean_ctor_set(x_23, 0, x_40);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_52);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_50);
lean_ctor_set(x_26, 0, x_30);
lean_ctor_set(x_47, 1, x_26);
lean_ctor_set(x_47, 0, x_39);
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_54);
lean_ctor_set(x_23, 0, x_40);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_54);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_53);
lean_ctor_set(x_26, 0, x_30);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_26);
lean_ctor_set(x_41, 0, x_55);
return x_41;
}
}
else
{
lean_free_object(x_23);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_free_object(x_26);
return x_41;
}
}
else
{
lean_free_object(x_23);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_free_object(x_26);
return x_41;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
x_58 = l_Lean_Exception_isRuntime(x_56);
if (x_58 == 0)
{
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_61);
lean_ctor_set(x_23, 0, x_40);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_61);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_59);
lean_ctor_set(x_26, 0, x_30);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_26);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
else
{
lean_object* x_64; 
lean_free_object(x_23);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_free_object(x_26);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_free_object(x_23);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_free_object(x_26);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_23, 0);
x_67 = lean_ctor_get(x_23, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_23);
x_68 = l_Lean_Elab_wfRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_30);
lean_free_object(x_26);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
x_76 = l_Lean_Exception_isRuntime(x_73);
if (x_76 == 0)
{
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_67);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_79);
lean_ctor_set(x_30, 0, x_80);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_77);
lean_ctor_set(x_26, 0, x_30);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_26);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_30);
lean_free_object(x_26);
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_74);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_30);
lean_free_object(x_26);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_74);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_30);
lean_free_object(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_36);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_36, 0);
lean_dec(x_86);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_23);
return x_36;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_36, 1);
lean_inc(x_87);
lean_dec(x_36);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_23);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_30, 1);
x_90 = lean_ctor_get(x_32, 1);
x_91 = lean_ctor_get(x_32, 2);
x_92 = lean_ctor_get(x_32, 3);
x_93 = lean_ctor_get(x_32, 4);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_32);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_16);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_91);
lean_ctor_set(x_94, 3, x_92);
lean_ctor_set(x_94, 4, x_93);
x_95 = lean_st_ref_set(x_5, x_94, x_89);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_23, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_99 = x_23;
} else {
 lean_dec_ref(x_23);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Elab_wfRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_96);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_free_object(x_30);
lean_free_object(x_26);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_107 = x_100;
} else {
 lean_dec_ref(x_100);
 x_107 = lean_box(0);
}
x_108 = l_Lean_Exception_isRuntime(x_105);
if (x_108 == 0)
{
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
 x_110 = lean_box(0);
}
x_111 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
if (lean_is_scalar(x_99)) {
 x_112 = lean_alloc_ctor(7, 2, 0);
} else {
 x_112 = x_99;
 lean_ctor_set_tag(x_112, 7);
}
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_111);
lean_ctor_set(x_30, 0, x_112);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_109);
lean_ctor_set(x_26, 0, x_30);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_97);
lean_ctor_set(x_113, 1, x_26);
if (lean_is_scalar(x_107)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_107;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_free_object(x_30);
lean_free_object(x_26);
if (lean_is_scalar(x_107)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_107;
}
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_106);
return x_115;
}
}
else
{
lean_object* x_116; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_free_object(x_30);
lean_free_object(x_26);
if (lean_is_scalar(x_107)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_107;
}
lean_ctor_set(x_116, 0, x_105);
lean_ctor_set(x_116, 1, x_106);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_30);
lean_free_object(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_95, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_118 = x_95;
} else {
 lean_dec_ref(x_95);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
 lean_ctor_set_tag(x_119, 1);
}
lean_ctor_set(x_119, 0, x_23);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_30, 0);
x_121 = lean_ctor_get(x_30, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_30);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 4);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_16);
lean_ctor_set(x_127, 1, x_122);
lean_ctor_set(x_127, 2, x_123);
lean_ctor_set(x_127, 3, x_124);
lean_ctor_set(x_127, 4, x_125);
x_128 = lean_st_ref_set(x_5, x_127, x_121);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_23, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_23, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_132 = x_23;
} else {
 lean_dec_ref(x_23);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Elab_wfRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_129);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_free_object(x_26);
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
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Exception_isRuntime(x_138);
if (x_141 == 0)
{
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_143 = x_138;
} else {
 lean_dec_ref(x_138);
 x_143 = lean_box(0);
}
x_144 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
if (lean_is_scalar(x_132)) {
 x_145 = lean_alloc_ctor(7, 2, 0);
} else {
 x_145 = x_132;
 lean_ctor_set_tag(x_145, 7);
}
lean_ctor_set(x_145, 0, x_131);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_142);
lean_ctor_set(x_26, 0, x_146);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_130);
lean_ctor_set(x_147, 1, x_26);
if (lean_is_scalar(x_140)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_140;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_139);
return x_148;
}
else
{
lean_object* x_149; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_free_object(x_26);
if (lean_is_scalar(x_140)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_140;
}
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_139);
return x_149;
}
}
else
{
lean_object* x_150; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_free_object(x_26);
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_138);
lean_ctor_set(x_150, 1, x_139);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_free_object(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_152 = x_128;
} else {
 lean_dec_ref(x_128);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
 lean_ctor_set_tag(x_153, 1);
}
lean_ctor_set(x_153, 0, x_23);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_154 = lean_ctor_get(x_26, 1);
lean_inc(x_154);
lean_dec(x_26);
x_155 = lean_st_ref_take(x_5, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_156, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_156, 4);
lean_inc(x_162);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 lean_ctor_release(x_156, 3);
 lean_ctor_release(x_156, 4);
 x_163 = x_156;
} else {
 lean_dec_ref(x_156);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 5, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_16);
lean_ctor_set(x_164, 1, x_159);
lean_ctor_set(x_164, 2, x_160);
lean_ctor_set(x_164, 3, x_161);
lean_ctor_set(x_164, 4, x_162);
x_165 = lean_st_ref_set(x_5, x_164, x_157);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_ctor_get(x_23, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_23, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_169 = x_23;
} else {
 lean_dec_ref(x_23);
 x_169 = lean_box(0);
}
x_170 = l_Lean_Elab_wfRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_166);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_158);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_175 = lean_ctor_get(x_170, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_177 = x_170;
} else {
 lean_dec_ref(x_170);
 x_177 = lean_box(0);
}
x_178 = l_Lean_Exception_isRuntime(x_175);
if (x_178 == 0)
{
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
x_181 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
if (lean_is_scalar(x_169)) {
 x_182 = lean_alloc_ctor(7, 2, 0);
} else {
 x_182 = x_169;
 lean_ctor_set_tag(x_182, 7);
}
lean_ctor_set(x_182, 0, x_168);
lean_ctor_set(x_182, 1, x_181);
if (lean_is_scalar(x_158)) {
 x_183 = lean_alloc_ctor(7, 2, 0);
} else {
 x_183 = x_158;
 lean_ctor_set_tag(x_183, 7);
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_179);
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_167);
lean_ctor_set(x_185, 1, x_184);
if (lean_is_scalar(x_177)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_177;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
return x_186;
}
else
{
lean_object* x_187; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_158);
if (lean_is_scalar(x_177)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_177;
}
lean_ctor_set(x_187, 0, x_175);
lean_ctor_set(x_187, 1, x_176);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_158);
if (lean_is_scalar(x_177)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_177;
}
lean_ctor_set(x_188, 0, x_175);
lean_ctor_set(x_188, 1, x_176);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_158);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_165, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_190 = x_165;
} else {
 lean_dec_ref(x_165);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_23);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_17, 0);
x_193 = lean_ctor_get(x_17, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_17);
x_194 = l_Lean_Exception_isRuntime(x_192);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_195 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_12, x_4, x_5, x_6, x_7, x_193);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = lean_st_ref_take(x_5, x_196);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 4);
lean_inc(x_205);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 x_206 = x_199;
} else {
 lean_dec_ref(x_199);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_16);
lean_ctor_set(x_207, 1, x_202);
lean_ctor_set(x_207, 2, x_203);
lean_ctor_set(x_207, 3, x_204);
lean_ctor_set(x_207, 4, x_205);
x_208 = lean_st_ref_set(x_5, x_207, x_200);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_ctor_get(x_192, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_192, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_212 = x_192;
} else {
 lean_dec_ref(x_192);
 x_212 = lean_box(0);
}
x_213 = l_Lean_Elab_wfRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_209);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_197);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_220 = x_213;
} else {
 lean_dec_ref(x_213);
 x_220 = lean_box(0);
}
x_221 = l_Lean_Exception_isRuntime(x_218);
if (x_221 == 0)
{
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_223 = x_218;
} else {
 lean_dec_ref(x_218);
 x_223 = lean_box(0);
}
x_224 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3;
if (lean_is_scalar(x_212)) {
 x_225 = lean_alloc_ctor(7, 2, 0);
} else {
 x_225 = x_212;
 lean_ctor_set_tag(x_225, 7);
}
lean_ctor_set(x_225, 0, x_211);
lean_ctor_set(x_225, 1, x_224);
if (lean_is_scalar(x_201)) {
 x_226 = lean_alloc_ctor(7, 2, 0);
} else {
 x_226 = x_201;
 lean_ctor_set_tag(x_226, 7);
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
if (lean_is_scalar(x_197)) {
 x_227 = lean_alloc_ctor(7, 2, 0);
} else {
 x_227 = x_197;
 lean_ctor_set_tag(x_227, 7);
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_222);
if (lean_is_scalar(x_223)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_223;
}
lean_ctor_set(x_228, 0, x_210);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_220)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_220;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_219);
return x_229;
}
else
{
lean_object* x_230; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_197);
if (lean_is_scalar(x_220)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_220;
}
lean_ctor_set(x_230, 0, x_218);
lean_ctor_set(x_230, 1, x_219);
return x_230;
}
}
else
{
lean_object* x_231; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_197);
if (lean_is_scalar(x_220)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_220;
}
lean_ctor_set(x_231, 0, x_218);
lean_ctor_set(x_231, 1, x_219);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_201);
lean_dec(x_197);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_232 = lean_ctor_get(x_208, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_233 = x_208;
} else {
 lean_dec_ref(x_208);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
 lean_ctor_set_tag(x_234, 1);
}
lean_ctor_set(x_234, 0, x_192);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_192);
lean_ctor_set(x_235, 1, x_193);
return x_235;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_23; lean_object* x_65; lean_object* x_66; lean_object* x_196; lean_object* x_238; lean_object* x_275; uint8_t x_276; 
lean_dec(x_3);
x_65 = lean_array_get_size(x_1);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_dec_eq(x_65, x_275);
if (x_276 == 0)
{
lean_object* x_277; 
x_277 = lean_box(0);
x_238 = x_277;
goto block_274;
}
else
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_unsigned_to_nat(0u);
x_279 = lean_nat_dec_lt(x_278, x_65);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_280 = l_Lean_Elab_instInhabitedPreDefinition;
x_281 = l___private_Init_GetElem_0__outOfBounds___rarg(x_280);
x_282 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(x_281);
if (x_282 == 0)
{
lean_object* x_283; 
x_283 = lean_box(0);
x_238 = x_283;
goto block_274;
}
else
{
lean_object* x_284; 
lean_dec(x_65);
lean_dec(x_1);
x_284 = l___private_Init_GetElem_0__outOfBounds___rarg(x_280);
x_23 = x_284;
goto block_64;
}
}
else
{
lean_object* x_285; uint8_t x_286; 
x_285 = lean_array_fget(x_1, x_278);
lean_inc(x_285);
x_286 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(x_285);
if (x_286 == 0)
{
lean_object* x_287; 
lean_dec(x_285);
x_287 = lean_box(0);
x_238 = x_287;
goto block_274;
}
else
{
lean_dec(x_65);
lean_dec(x_1);
x_23 = x_285;
goto block_64;
}
}
}
block_22:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
block_64:
{
lean_object* x_24; 
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Elab_eraseRecAppSyntax(x_23, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 3);
lean_inc(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_27);
x_28 = l_Lean_Meta_ensureEqnReservedNamesAvailable(x_27, x_8, x_9, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*2 + 1);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_34 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_25);
x_35 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_25, x_34, x_33, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1(x_25, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_36);
lean_dec(x_25);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_dec(x_28);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_44);
x_46 = 0;
x_47 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_25);
x_48 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_25, x_46, x_45, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1(x_25, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_49);
lean_dec(x_25);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_28);
if (x_56 == 0)
{
return x_28;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_28, 0);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_28);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_24);
if (x_60 == 0)
{
return x_24;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_24, 0);
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_24);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
block_195:
{
lean_object* x_67; 
lean_dec(x_66);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_67 = l_Lean_Elab_ensureFunIndReservedNamesAvailable(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_153; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_lt(x_70, x_65);
if (x_71 == 0)
{
lean_object* x_184; 
x_184 = lean_box(0);
x_153 = x_184;
goto block_183;
}
else
{
size_t x_185; uint8_t x_186; 
x_185 = lean_usize_of_nat(x_65);
x_186 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__8(x_1, x_2, x_185);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_box(0);
x_153 = x_187;
goto block_183;
}
else
{
lean_object* x_188; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_188 = l_Lean_Elab_wfRecursion(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
if (lean_obj_tag(x_188) == 0)
{
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = x_188;
goto block_22;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_72 = x_189;
x_73 = x_190;
goto block_152;
}
}
}
block_152:
{
uint8_t x_74; 
x_74 = l_Lean_Exception_isRuntime(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_69);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_75 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_73);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_90; 
x_77 = lean_ctor_get(x_75, 1);
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = l_Lean_Elab_Term_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (x_71 == 0)
{
lean_object* x_103; 
lean_free_object(x_75);
lean_dec(x_65);
x_103 = lean_box(0);
x_90 = x_103;
goto block_102;
}
else
{
size_t x_104; uint8_t x_105; 
x_104 = lean_usize_of_nat(x_65);
x_105 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(x_2, x_1, x_65, x_71, x_1, x_2, x_104);
lean_dec(x_65);
if (x_105 == 0)
{
lean_object* x_106; 
lean_free_object(x_75);
x_106 = lean_box(0);
x_90 = x_106;
goto block_102;
}
else
{
uint8_t x_107; 
x_107 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__6(x_1, x_2, x_104);
if (x_107 == 0)
{
lean_object* x_108; 
lean_free_object(x_75);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_108 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
lean_dec(x_1);
if (lean_obj_tag(x_108) == 0)
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = x_108;
goto block_22;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_83 = x_109;
x_84 = x_110;
goto block_89;
}
}
else
{
lean_object* x_111; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_111 = lean_box(0);
lean_ctor_set(x_75, 1, x_81);
lean_ctor_set(x_75, 0, x_111);
x_11 = x_75;
goto block_22;
}
}
}
block_89:
{
uint8_t x_85; 
x_85 = l_Lean_Exception_isRuntime(x_83);
if (x_85 == 0)
{
uint8_t x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_82);
x_86 = 0;
x_87 = l_Lean_Elab_Term_SavedState_restore(x_80, x_86, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
x_11 = x_87;
goto block_22;
}
else
{
lean_object* x_88; 
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_82)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_82;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
x_11 = x_88;
goto block_22;
}
}
block_102:
{
uint8_t x_91; lean_object* x_92; 
lean_dec(x_90);
x_91 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_92 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(x_1, x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_92) == 0)
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = x_92;
goto block_22;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Exception_isRuntime(x_93);
if (x_95 == 0)
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_93);
x_96 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_80);
x_97 = l_Lean_Elab_Term_SavedState_restore(x_80, x_96, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_99 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_1);
if (lean_obj_tag(x_99) == 0)
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = x_99;
goto block_22;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_83 = x_100;
x_84 = x_101;
goto block_89;
}
}
else
{
lean_dec(x_1);
x_83 = x_93;
x_84 = x_94;
goto block_89;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_124; 
x_112 = lean_ctor_get(x_75, 1);
lean_inc(x_112);
lean_dec(x_75);
x_113 = l_Lean_Elab_Term_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (x_71 == 0)
{
lean_object* x_137; 
lean_dec(x_65);
x_137 = lean_box(0);
x_124 = x_137;
goto block_136;
}
else
{
size_t x_138; uint8_t x_139; 
x_138 = lean_usize_of_nat(x_65);
x_139 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(x_2, x_1, x_65, x_71, x_1, x_2, x_138);
lean_dec(x_65);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_box(0);
x_124 = x_140;
goto block_136;
}
else
{
uint8_t x_141; 
x_141 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__6(x_1, x_2, x_138);
if (x_141 == 0)
{
lean_object* x_142; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_142 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
lean_dec(x_1);
if (lean_obj_tag(x_142) == 0)
{
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = x_142;
goto block_22;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_117 = x_143;
x_118 = x_144;
goto block_123;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_115);
x_11 = x_146;
goto block_22;
}
}
}
block_123:
{
uint8_t x_119; 
x_119 = l_Lean_Exception_isRuntime(x_117);
if (x_119 == 0)
{
uint8_t x_120; lean_object* x_121; 
lean_dec(x_117);
lean_dec(x_116);
x_120 = 0;
x_121 = l_Lean_Elab_Term_SavedState_restore(x_114, x_120, x_4, x_5, x_6, x_7, x_8, x_9, x_118);
x_11 = x_121;
goto block_22;
}
else
{
lean_object* x_122; 
lean_dec(x_114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_116;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_118);
x_11 = x_122;
goto block_22;
}
}
block_136:
{
uint8_t x_125; lean_object* x_126; 
lean_dec(x_124);
x_125 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_126 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(x_1, x_125, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
if (lean_obj_tag(x_126) == 0)
{
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = x_126;
goto block_22;
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Exception_isRuntime(x_127);
if (x_129 == 0)
{
uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_127);
x_130 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_114);
x_131 = l_Lean_Elab_Term_SavedState_restore(x_114, x_130, x_4, x_5, x_6, x_7, x_8, x_9, x_128);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_133 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_132);
lean_dec(x_1);
if (lean_obj_tag(x_133) == 0)
{
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = x_133;
goto block_22;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_117 = x_134;
x_118 = x_135;
goto block_123;
}
}
else
{
lean_dec(x_1);
x_117 = x_127;
x_118 = x_128;
goto block_123;
}
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_75);
if (x_147 == 0)
{
x_11 = x_75;
goto block_22;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_75, 0);
x_149 = lean_ctor_get(x_75, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_75);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_11 = x_150;
goto block_22;
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_69)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_69;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_72);
lean_ctor_set(x_151, 1, x_73);
x_11 = x_151;
goto block_22;
}
}
block_183:
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_153);
lean_inc(x_1);
x_154 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2), 2, 1);
lean_closure_set(x_154, 0, x_1);
if (x_71 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = l_Lean_Elab_instInhabitedPreDefinition;
x_181 = l___private_Init_GetElem_0__outOfBounds___rarg(x_180);
x_155 = x_181;
goto block_179;
}
else
{
lean_object* x_182; 
x_182 = lean_array_fget(x_1, x_70);
x_155 = x_182;
goto block_179;
}
block_179:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_ctor_get(x_8, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_8, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_8, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_8, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_8, 4);
lean_inc(x_161);
x_162 = lean_ctor_get(x_8, 5);
lean_inc(x_162);
x_163 = lean_ctor_get(x_8, 6);
lean_inc(x_163);
x_164 = lean_ctor_get(x_8, 7);
lean_inc(x_164);
x_165 = lean_ctor_get(x_8, 8);
lean_inc(x_165);
x_166 = lean_ctor_get(x_8, 9);
lean_inc(x_166);
x_167 = lean_ctor_get(x_8, 10);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_169 = l_Lean_replaceRef(x_156, x_162);
lean_dec(x_162);
lean_dec(x_156);
x_170 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_170, 0, x_157);
lean_ctor_set(x_170, 1, x_158);
lean_ctor_set(x_170, 2, x_159);
lean_ctor_set(x_170, 3, x_160);
lean_ctor_set(x_170, 4, x_161);
lean_ctor_set(x_170, 5, x_169);
lean_ctor_set(x_170, 6, x_163);
lean_ctor_set(x_170, 7, x_164);
lean_ctor_set(x_170, 8, x_165);
lean_ctor_set(x_170, 9, x_166);
lean_ctor_set(x_170, 10, x_167);
lean_ctor_set_uint8(x_170, sizeof(void*)*11, x_168);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_171 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__3), 8, 3);
lean_closure_set(x_171, 0, x_1);
lean_closure_set(x_171, 1, x_4);
lean_closure_set(x_171, 2, x_5);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_172 = l_Lean_Meta_mapErrorImp___rarg(x_171, x_154, x_6, x_7, x_170, x_9, x_68);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
x_11 = x_172;
goto block_22;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_172);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_11 = x_176;
goto block_22;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
lean_dec(x_172);
x_72 = x_177;
x_73 = x_178;
goto block_152;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_67);
if (x_191 == 0)
{
return x_67;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_67, 0);
x_193 = lean_ctor_get(x_67, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_67);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
block_237:
{
lean_object* x_197; uint8_t x_198; 
lean_dec(x_196);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_nat_dec_lt(x_197, x_65);
if (x_198 == 0)
{
lean_object* x_199; 
x_199 = lean_box(0);
x_66 = x_199;
goto block_195;
}
else
{
size_t x_200; uint8_t x_201; 
x_200 = lean_usize_of_nat(x_65);
x_201 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__9(x_1, x_2, x_200);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_box(0);
x_66 = x_202;
goto block_195;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10(x_1, x_200, x_2, x_203, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; uint8_t x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_206 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_207 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(x_1, x_206, x_4, x_5, x_6, x_7, x_8, x_9, x_205);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_207, 1);
x_210 = lean_ctor_get(x_207, 0);
lean_dec(x_210);
x_211 = lean_nat_dec_le(x_65, x_65);
lean_dec(x_65);
if (x_211 == 0)
{
lean_object* x_212; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
lean_ctor_set(x_207, 0, x_212);
return x_207;
}
else
{
lean_object* x_213; uint8_t x_214; 
lean_free_object(x_207);
x_213 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11(x_1, x_2, x_200, x_203, x_4, x_5, x_6, x_7, x_8, x_9, x_209);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_213, 0);
lean_dec(x_215);
x_216 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
lean_ctor_set(x_213, 0, x_216);
return x_213;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_213, 1);
lean_inc(x_217);
lean_dec(x_213);
x_218 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_207, 1);
lean_inc(x_220);
lean_dec(x_207);
x_221 = lean_nat_dec_le(x_65, x_65);
lean_dec(x_65);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_222 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_220);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11(x_1, x_2, x_200, x_203, x_4, x_5, x_6, x_7, x_8, x_9, x_220);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_207);
if (x_229 == 0)
{
return x_207;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_207, 0);
x_231 = lean_ctor_get(x_207, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_207);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_204);
if (x_233 == 0)
{
return x_204;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_204, 0);
x_235 = lean_ctor_get(x_204, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_204);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
}
block_274:
{
lean_object* x_239; uint8_t x_240; 
lean_dec(x_238);
x_239 = lean_unsigned_to_nat(0u);
x_240 = lean_nat_dec_lt(x_239, x_65);
if (x_240 == 0)
{
lean_object* x_241; 
x_241 = lean_box(0);
x_196 = x_241;
goto block_237;
}
else
{
size_t x_242; uint8_t x_243; 
x_242 = lean_usize_of_nat(x_65);
x_243 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__12(x_1, x_2, x_242);
if (x_243 == 0)
{
lean_object* x_244; 
x_244 = lean_box(0);
x_196 = x_244;
goto block_237;
}
else
{
uint8_t x_245; lean_object* x_246; 
x_245 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_246 = l_Lean_Elab_addAndCompileUnsafe(x_1, x_245, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_248 = lean_ctor_get(x_246, 1);
x_249 = lean_ctor_get(x_246, 0);
lean_dec(x_249);
x_250 = lean_nat_dec_le(x_65, x_65);
lean_dec(x_65);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_251 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
lean_ctor_set(x_246, 0, x_251);
return x_246;
}
else
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_free_object(x_246);
x_252 = lean_box(0);
x_253 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13(x_1, x_2, x_242, x_252, x_4, x_5, x_6, x_7, x_8, x_9, x_248);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_253, 0);
lean_dec(x_255);
x_256 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
lean_ctor_set(x_253, 0, x_256);
return x_253;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
lean_dec(x_253);
x_258 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
else
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_246, 1);
lean_inc(x_260);
lean_dec(x_246);
x_261 = lean_nat_dec_le(x_65, x_65);
lean_dec(x_65);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_262 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = lean_box(0);
x_265 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13(x_1, x_2, x_242, x_264, x_4, x_5, x_6, x_7, x_8, x_9, x_260);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
x_268 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_246);
if (x_270 == 0)
{
return x_246;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_246, 0);
x_272 = lean_ctor_get(x_246, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_246);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("scc", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_8);
x_18 = lean_array_uget(x_5, x_7);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__2;
x_20 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4(x_18, x_4, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = 1;
x_36 = lean_usize_add(x_7, x_35);
x_7 = x_36;
x_8 = x_34;
x_15 = x_33;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_20, 1);
x_44 = lean_ctor_get(x_20, 0);
lean_dec(x_44);
x_45 = lean_array_get_size(x_18);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
lean_inc(x_18);
x_47 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__11(x_46, x_4, x_18);
x_48 = lean_array_to_list(lean_box(0), x_47);
x_49 = lean_box(0);
x_50 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_48, x_49);
x_51 = l_Lean_MessageData_ofList(x_50);
x_52 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_51);
lean_ctor_set(x_20, 0, x_52);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_20);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_19, x_53, x_9, x_10, x_11, x_12, x_13, x_14, x_43);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4(x_18, x_4, x_55, x_9, x_10, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
x_67 = 1;
x_68 = lean_usize_add(x_7, x_67);
x_7 = x_68;
x_8 = x_66;
x_15 = x_65;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_70 = !lean_is_exclusive(x_57);
if (x_70 == 0)
{
return x_57;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_57);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_74 = lean_ctor_get(x_20, 1);
lean_inc(x_74);
lean_dec(x_20);
x_75 = lean_array_get_size(x_18);
x_76 = lean_usize_of_nat(x_75);
lean_dec(x_75);
lean_inc(x_18);
x_77 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__11(x_76, x_4, x_18);
x_78 = lean_array_to_list(lean_box(0), x_77);
x_79 = lean_box(0);
x_80 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_78, x_79);
x_81 = l_Lean_MessageData_ofList(x_80);
x_82 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_19, x_84, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4(x_18, x_4, x_86, x_9, x_10, x_11, x_12, x_13, x_14, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
lean_dec(x_89);
x_96 = 1;
x_97 = lean_usize_add(x_7, x_96);
x_7 = x_97;
x_8 = x_95;
x_15 = x_94;
goto _start;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_99 = lean_ctor_get(x_88, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_101 = x_88;
} else {
 lean_dec_ref(x_88);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addPreDefinitions___lambda__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(x_1, x_2, x_3, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__3(x_2, x_3, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps(x_17, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs(x_20);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14(x_4, x_4, x_5, x_3, x_22, x_24, x_3, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_13);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__1;
x_2 = l_Lean_Elab_addPreDefinitions___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__4;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__5;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlTOfPure___rarg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__3;
x_2 = l_Lean_Elab_addPreDefinitions___closed__6;
x_3 = l_instMonadControlTOfMonadControl___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__3;
x_2 = l_Lean_Elab_addPreDefinitions___closed__7;
x_3 = l_instMonadControlTOfMonadControl___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__14() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_addPreDefinitions___closed__13;
x_3 = l_Lean_Elab_addPreDefinitions___closed__12;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_addPreDefinitions___closed__11;
x_2 = l_Lean_Elab_addPreDefinitions___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_addPreDefinitions___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addPreDefinitions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = l_Lean_Elab_addPreDefinitions___closed__3;
x_12 = l_Lean_Elab_addPreDefinitions___closed__8;
x_13 = lean_box_usize(x_10);
x_14 = l_Lean_Elab_addPreDefinitions___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_addPreDefinitions___lambda__1___boxed), 12, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_11);
lean_closure_set(x_15, 4, x_12);
x_16 = l_Lean_Elab_addPreDefinitions___closed__15;
x_17 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2;
x_18 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__4___rarg(x_16, x_17, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__3(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; uint8_t x_9; size_t x_10; size_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(x_8, x_2, x_3, x_9, x_5, x_10, x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__6(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__8(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__9(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__12(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__4(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14(x_1, x_2, x_3, x_16, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addPreDefinitions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_addPreDefinitions___lambda__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__2;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__3;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__5;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__7;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__8;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PreDefinition", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__9;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Main", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__11;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__13;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__15;
x_2 = lean_unsigned_to_nat(2080u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__2;
x_3 = 0;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__16;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__2;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* initialize_Lean_Util_SCC(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_SCC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__6);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__2___closed__7);
l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___closed__1 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___closed__1);
l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___closed__1 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___closed__1();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__5 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__5);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__6 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__6);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___closed__7);
l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed__const__1 = _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___lambda__2___boxed__const__1);
l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__1);
l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__2);
l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef___closed__3);
l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__1);
l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef___spec__1___rarg___closed__2);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__9___rarg___closed__2);
l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1___closed__1 = _init_l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Core_transform_visit___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__4___lambda__1___closed__1);
l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__1 = _init_l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__1();
lean_mark_persistent(l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__1);
l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__2 = _init_l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__2();
lean_mark_persistent(l_Lean_Core_transform___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__3___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_betaReduceLetRecApps___spec__10___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAsAxioms___spec__1___closed__2);
l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__1 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__1();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__1);
l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__2 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__2();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__2);
l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__3 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__3();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__3);
l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__4 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__4();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__4);
l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__5 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__5();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__5);
l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__6 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__6();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__2___closed__6);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_ensureFunIndReservedNamesAvailable___spec__3___closed__1);
l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1 = _init_l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1();
lean_mark_persistent(l_Lean_Elab_ensureFunIndReservedNamesAvailable___closed__1);
l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_addPreDefinitions___spec__1___closed__1();
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__10___closed__4);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__11___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_addPreDefinitions___spec__13___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___lambda__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__14___closed__2);
l_Lean_Elab_addPreDefinitions___closed__1 = _init_l_Lean_Elab_addPreDefinitions___closed__1();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__1);
l_Lean_Elab_addPreDefinitions___closed__2 = _init_l_Lean_Elab_addPreDefinitions___closed__2();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__2);
l_Lean_Elab_addPreDefinitions___closed__3 = _init_l_Lean_Elab_addPreDefinitions___closed__3();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__3);
l_Lean_Elab_addPreDefinitions___closed__4 = _init_l_Lean_Elab_addPreDefinitions___closed__4();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__4);
l_Lean_Elab_addPreDefinitions___closed__5 = _init_l_Lean_Elab_addPreDefinitions___closed__5();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__5);
l_Lean_Elab_addPreDefinitions___closed__6 = _init_l_Lean_Elab_addPreDefinitions___closed__6();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__6);
l_Lean_Elab_addPreDefinitions___closed__7 = _init_l_Lean_Elab_addPreDefinitions___closed__7();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__7);
l_Lean_Elab_addPreDefinitions___closed__8 = _init_l_Lean_Elab_addPreDefinitions___closed__8();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__8);
l_Lean_Elab_addPreDefinitions___closed__9 = _init_l_Lean_Elab_addPreDefinitions___closed__9();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__9);
l_Lean_Elab_addPreDefinitions___closed__10 = _init_l_Lean_Elab_addPreDefinitions___closed__10();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__10);
l_Lean_Elab_addPreDefinitions___closed__11 = _init_l_Lean_Elab_addPreDefinitions___closed__11();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__11);
l_Lean_Elab_addPreDefinitions___closed__12 = _init_l_Lean_Elab_addPreDefinitions___closed__12();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__12);
l_Lean_Elab_addPreDefinitions___closed__13 = _init_l_Lean_Elab_addPreDefinitions___closed__13();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__13);
l_Lean_Elab_addPreDefinitions___closed__14 = _init_l_Lean_Elab_addPreDefinitions___closed__14();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__14);
l_Lean_Elab_addPreDefinitions___closed__15 = _init_l_Lean_Elab_addPreDefinitions___closed__15();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___closed__15);
l_Lean_Elab_addPreDefinitions___boxed__const__1 = _init_l_Lean_Elab_addPreDefinitions___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_addPreDefinitions___boxed__const__1);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__14);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__15 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__15();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__15);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__16 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__16();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080____closed__16);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Main___hyg_2080_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
