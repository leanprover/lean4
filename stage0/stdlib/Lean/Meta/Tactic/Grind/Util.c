// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Util
// Imports: Init.Simproc Init.Grind.Tactics Lean.Meta.AbstractNestedProofs Lean.Meta.Transform Lean.Meta.Tactic.Util Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Simp.Simproc
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__3;
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Core_betaReduce_spec__0_spec__0_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at_____private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__2;
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__6____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
static lean_object* l_Lean_Meta_Grind_replacePreMatchCond___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_unfoldReducible___closed__0;
static lean_object* l_Lean_Meta_Grind_isDIte___closed__1;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__1;
static lean_object* l_Lean_MVarId_clearAuxDecls___closed__0;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_isDIte___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__2;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__3____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
lean_object* l_Lean_Meta_abstractMVars___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isGrindGadget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_isIte___closed__1;
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__5;
static lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__0;
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_foldProjs___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_clearAuxDecls___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__0;
static lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__4;
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__0;
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__3;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__2____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__6;
static lean_object* l_Lean_Meta_Grind_replacePreMatchCond___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__1;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__9;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__3;
static lean_object* l_Lean_MVarId_byContra_x3f___closed__0;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__2;
uint8_t l_Lean_Expr_isFalse(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeLevels___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__1;
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__3;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__5____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__6;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__4;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_(lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__4____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_Grind_foldProjs___lam__2___closed__12;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_isIte___closed__0;
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGrindGadget___boxed(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__2___closed__10;
uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_normalizeLevels_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__0____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
static lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__1;
lean_object* l_Lean_Level_normalize(lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__0;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__1;
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1___closed__0;
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__5;
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goal contains metavariables", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_8, x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Expr_hasExprMVar(x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
x_16 = l_Lean_MVarId_ensureNoMVar___closed__1;
x_17 = l_Lean_MVarId_ensureNoMVar___closed__5;
x_18 = l_Lean_Meta_throwTacticEx___redArg(x_16, x_1, x_17, x_2, x_3, x_4, x_5, x_13);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = l_Lean_Expr_hasExprMVar(x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_MVarId_ensureNoMVar___closed__1;
x_25 = l_Lean_MVarId_ensureNoMVar___closed__5;
x_26 = l_Lean_Meta_throwTacticEx___redArg(x_24, x_1, x_25, x_2, x_3, x_4, x_5, x_20);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_ensureNoMVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Meta_mkForallFVars(x_3, x_4, x_1, x_2, x_2, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_abstractMVars___redArg(x_1, x_2, x_5, x_6, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_14);
lean_dec(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_14, x_3, x_2, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_4);
x_18 = l_Lean_MVarId_getTag(x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_16, x_19, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_22);
x_24 = l_Lean_mkAppN(x_22, x_13);
lean_dec_ref(x_13);
x_25 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_4, x_24, x_6, x_23);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec_ref(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
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
lean_dec_ref(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_MVarId_ensureNoMVar___closed__1;
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_11, x_3, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_hasExprMVar(x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_13);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_box(x_17);
x_21 = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__0___boxed), 9, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_box(x_18);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__1___boxed), 9, 4);
lean_closure_set(x_23, 0, x_15);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_1);
x_24 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_23, x_2, x_3, x_4, x_5, x_16);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = l_Lean_Expr_hasExprMVar(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_box(x_27);
x_32 = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__0___boxed), 9, 2);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_box(x_29);
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__1___boxed), 9, 4);
lean_closure_set(x_34, 0, x_25);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_32);
lean_closure_set(x_34, 3, x_1);
x_35 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_34, x_2, x_3, x_4, x_5, x_26);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
return x_8;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_8, 0);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_8);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_2);
x_12 = l_Lean_MVarId_abstractMVars___lam__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_MVarId_abstractMVars___lam__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_1);
x_11 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_1);
x_14 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_17 = lean_apply_6(x_3, x_15, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_18, x_12, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec_ref(x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_21);
x_23 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_21, x_5, x_22);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
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
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
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
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MVarId_ensureNoMVar___closed__1;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_transformTarget___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("EqMatch", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_isGrindGadget___closed__2;
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_3 = l_Lean_Meta_Grind_isGrindGadget___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isGrindGadget(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__3;
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGrindGadget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isGrindGadget(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
lean_inc(x_3);
x_4 = lean_get_reducibility_status(x_1, x_3);
x_5 = lean_box(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Meta_Grind_isGrindGadget(x_3);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_find_expr(x_8, x_1);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
uint8_t x_12; lean_object* x_13; 
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_box(x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_find_expr(x_17, x_1);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_18);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_isUnfoldReducibleTarget(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_5, x_4);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_2, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_5, x_4, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = lean_array_uset(x_19, x_4, x_16);
x_4 = x_21;
x_5 = x_22;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc_ref(x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_10 = lean_apply_6(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_3);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec_ref(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_11);
x_20 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
default: 
{
lean_object* x_21; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec_ref(x_11);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_10, 0);
lean_dec(x_23);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_3);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec_ref(x_21);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec_ref(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
x_14 = lean_array_set(x_4, x_5, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_3 = x_12;
x_4 = x_14;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_18 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_array_size(x_4);
x_22 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__0(x_1, x_2, x_21, x_22, x_4, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_mkAppN(x_19, x_24);
lean_dec(x_24);
x_27 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_2, x_26, x_6, x_7, x_8, x_9, x_10, x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
x_14 = lean_array_set(x_4, x_5, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
x_17 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2_spec__2(x_1, x_2, x_12, x_14, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_18 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_array_size(x_4);
x_22 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__0(x_1, x_2, x_21, x_22, x_4, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_mkAppN(x_19, x_24);
lean_dec(x_24);
x_27 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_2, x_26, x_6, x_7, x_8, x_9, x_10, x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
x_21 = lean_ctor_get(x_5, 6);
x_22 = lean_ctor_get(x_5, 7);
x_23 = lean_ctor_get(x_5, 8);
x_24 = lean_ctor_get(x_5, 9);
x_25 = lean_ctor_get(x_5, 10);
x_26 = lean_ctor_get(x_5, 11);
x_27 = lean_ctor_get(x_5, 12);
x_28 = lean_nat_dec_eq(x_18, x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_18, x_29);
lean_dec(x_18);
lean_ctor_set(x_5, 3, x_30);
x_31 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_8 = x_31;
goto block_13;
}
else
{
lean_object* x_32; 
lean_free_object(x_5);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_32 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Core_betaReduce_spec__0_spec__0_spec__4_spec__4___redArg(x_20, x_7);
x_8 = x_32;
goto block_13;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
x_35 = lean_ctor_get(x_5, 2);
x_36 = lean_ctor_get(x_5, 3);
x_37 = lean_ctor_get(x_5, 4);
x_38 = lean_ctor_get(x_5, 5);
x_39 = lean_ctor_get(x_5, 6);
x_40 = lean_ctor_get(x_5, 7);
x_41 = lean_ctor_get(x_5, 8);
x_42 = lean_ctor_get(x_5, 9);
x_43 = lean_ctor_get(x_5, 10);
x_44 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_45 = lean_ctor_get(x_5, 11);
x_46 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_47 = lean_ctor_get(x_5, 12);
lean_inc(x_47);
lean_inc(x_45);
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
lean_dec(x_5);
x_48 = lean_nat_dec_eq(x_36, x_37);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_36, x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_34);
lean_ctor_set(x_51, 2, x_35);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_37);
lean_ctor_set(x_51, 5, x_38);
lean_ctor_set(x_51, 6, x_39);
lean_ctor_set(x_51, 7, x_40);
lean_ctor_set(x_51, 8, x_41);
lean_ctor_set(x_51, 9, x_42);
lean_ctor_set(x_51, 10, x_43);
lean_ctor_set(x_51, 11, x_45);
lean_ctor_set(x_51, 12, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*13, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*13 + 1, x_46);
x_52 = lean_apply_6(x_1, x_2, x_3, x_4, x_51, x_6, x_7);
x_8 = x_52;
goto block_13;
}
else
{
lean_object* x_53; 
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_53 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Core_betaReduce_spec__0_spec__0_spec__4_spec__4___redArg(x_38, x_7);
x_8 = x_53;
goto block_13;
}
}
block_13:
{
if (lean_obj_tag(x_8) == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
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
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_56; 
lean_inc_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_56 = lean_apply_6(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
switch (lean_obj_tag(x_58)) {
case 0:
{
lean_object* x_144; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_144 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_144);
lean_dec_ref(x_58);
lean_ctor_set(x_56, 0, x_144);
return x_56;
}
case 1:
{
lean_object* x_145; lean_object* x_146; 
lean_free_object(x_56);
lean_dec_ref(x_2);
x_145 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_145);
lean_dec_ref(x_58);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_146 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_145, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_147, x_4, x_5, x_6, x_7, x_8, x_148);
return x_149;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_146;
}
}
default: 
{
lean_object* x_150; 
lean_free_object(x_56);
x_150 = lean_ctor_get(x_58, 0);
lean_inc(x_150);
lean_dec_ref(x_58);
if (lean_obj_tag(x_150) == 0)
{
x_60 = x_2;
goto block_143;
}
else
{
lean_object* x_151; 
lean_dec_ref(x_2);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_60 = x_151;
goto block_143;
}
}
}
block_143:
{
switch (lean_obj_tag(x_60)) {
case 5:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1___closed__0;
x_62 = l_Lean_Expr_getAppNumArgs(x_60);
lean_inc(x_62);
x_63 = lean_mk_array(x_62, x_61);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_62, x_64);
lean_dec(x_62);
x_66 = l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2(x_1, x_3, x_60, x_63, x_65, x_4, x_5, x_6, x_7, x_8, x_59);
lean_dec(x_65);
return x_66;
}
case 6:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_60, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get_uint8(x_60, sizeof(void*)*3 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_68);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_71 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_68, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_69);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_74 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_69, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ptr_addr(x_68);
lean_dec_ref(x_68);
x_78 = lean_ptr_addr(x_72);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_dec_ref(x_69);
x_42 = x_60;
x_43 = x_67;
x_44 = x_72;
x_45 = x_76;
x_46 = x_75;
x_47 = x_70;
x_48 = x_79;
goto block_55;
}
else
{
size_t x_80; size_t x_81; uint8_t x_82; 
x_80 = lean_ptr_addr(x_69);
lean_dec_ref(x_69);
x_81 = lean_ptr_addr(x_75);
x_82 = lean_usize_dec_eq(x_80, x_81);
x_42 = x_60;
x_43 = x_67;
x_44 = x_72;
x_45 = x_76;
x_46 = x_75;
x_47 = x_70;
x_48 = x_82;
goto block_55;
}
}
else
{
lean_dec(x_72);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_74;
}
}
else
{
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_71;
}
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_60, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_85);
x_86 = lean_ctor_get_uint8(x_60, sizeof(void*)*3 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_84);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_87 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_84, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_85);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_90 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_85, x_4, x_5, x_6, x_7, x_8, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_ptr_addr(x_84);
lean_dec_ref(x_84);
x_94 = lean_ptr_addr(x_88);
x_95 = lean_usize_dec_eq(x_93, x_94);
if (x_95 == 0)
{
lean_dec_ref(x_85);
x_28 = x_60;
x_29 = x_92;
x_30 = x_91;
x_31 = x_86;
x_32 = x_88;
x_33 = x_83;
x_34 = x_95;
goto block_41;
}
else
{
size_t x_96; size_t x_97; uint8_t x_98; 
x_96 = lean_ptr_addr(x_85);
lean_dec_ref(x_85);
x_97 = lean_ptr_addr(x_91);
x_98 = lean_usize_dec_eq(x_96, x_97);
x_28 = x_60;
x_29 = x_92;
x_30 = x_91;
x_31 = x_86;
x_32 = x_88;
x_33 = x_83;
x_34 = x_98;
goto block_41;
}
}
else
{
lean_dec(x_88);
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_90;
}
}
else
{
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_87;
}
}
case 8:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_60, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_60, 3);
lean_inc_ref(x_102);
x_103 = lean_ctor_get_uint8(x_60, sizeof(void*)*4 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_100);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_104 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_100, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_101);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_107 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_101, x_4, x_5, x_6, x_7, x_8, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_102);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_110 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_102, x_4, x_5, x_6, x_7, x_8, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; size_t x_113; size_t x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = lean_ptr_addr(x_100);
lean_dec_ref(x_100);
x_114 = lean_ptr_addr(x_105);
x_115 = lean_usize_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_dec_ref(x_101);
x_10 = x_60;
x_11 = x_112;
x_12 = x_111;
x_13 = x_108;
x_14 = x_102;
x_15 = x_103;
x_16 = x_105;
x_17 = x_99;
x_18 = x_115;
goto block_27;
}
else
{
size_t x_116; size_t x_117; uint8_t x_118; 
x_116 = lean_ptr_addr(x_101);
lean_dec_ref(x_101);
x_117 = lean_ptr_addr(x_108);
x_118 = lean_usize_dec_eq(x_116, x_117);
x_10 = x_60;
x_11 = x_112;
x_12 = x_111;
x_13 = x_108;
x_14 = x_102;
x_15 = x_103;
x_16 = x_105;
x_17 = x_99;
x_18 = x_118;
goto block_27;
}
}
else
{
lean_dec(x_108);
lean_dec(x_105);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_110;
}
}
else
{
lean_dec(x_105);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_107;
}
}
else
{
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_104;
}
}
case 10:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_60, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_120);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_120);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_121 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_120, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; size_t x_124; size_t x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = lean_ptr_addr(x_120);
lean_dec_ref(x_120);
x_125 = lean_ptr_addr(x_122);
x_126 = lean_usize_dec_eq(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_60);
x_127 = l_Lean_Expr_mdata___override(x_119, x_122);
x_128 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_127, x_4, x_5, x_6, x_7, x_8, x_123);
return x_128;
}
else
{
lean_object* x_129; 
lean_dec(x_122);
lean_dec(x_119);
x_129 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_60, x_4, x_5, x_6, x_7, x_8, x_123);
return x_129;
}
}
else
{
lean_dec_ref(x_120);
lean_dec(x_119);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_121;
}
}
case 11:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_60, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_60, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_132);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_132);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_133 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_132, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_ptr_addr(x_132);
lean_dec_ref(x_132);
x_137 = lean_ptr_addr(x_134);
x_138 = lean_usize_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_60);
x_139 = l_Lean_Expr_proj___override(x_130, x_131, x_134);
x_140 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_139, x_4, x_5, x_6, x_7, x_8, x_135);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_134);
lean_dec(x_131);
lean_dec(x_130);
x_141 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_60, x_4, x_5, x_6, x_7, x_8, x_135);
return x_141;
}
}
else
{
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec_ref(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_133;
}
}
default: 
{
lean_object* x_142; 
x_142 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_60, x_4, x_5, x_6, x_7, x_8, x_59);
return x_142;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_56, 0);
x_153 = lean_ctor_get(x_56, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_56);
switch (lean_obj_tag(x_152)) {
case 0:
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_238 = lean_ctor_get(x_152, 0);
lean_inc_ref(x_238);
lean_dec_ref(x_152);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_153);
return x_239;
}
case 1:
{
lean_object* x_240; lean_object* x_241; 
lean_dec_ref(x_2);
x_240 = lean_ctor_get(x_152, 0);
lean_inc_ref(x_240);
lean_dec_ref(x_152);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_241 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_240, x_4, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec_ref(x_241);
x_244 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_242, x_4, x_5, x_6, x_7, x_8, x_243);
return x_244;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_241;
}
}
default: 
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_152, 0);
lean_inc(x_245);
lean_dec_ref(x_152);
if (lean_obj_tag(x_245) == 0)
{
x_154 = x_2;
goto block_237;
}
else
{
lean_object* x_246; 
lean_dec_ref(x_2);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_154 = x_246;
goto block_237;
}
}
}
block_237:
{
switch (lean_obj_tag(x_154)) {
case 5:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1___closed__0;
x_156 = l_Lean_Expr_getAppNumArgs(x_154);
lean_inc(x_156);
x_157 = lean_mk_array(x_156, x_155);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_sub(x_156, x_158);
lean_dec(x_156);
x_160 = l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2(x_1, x_3, x_154, x_157, x_159, x_4, x_5, x_6, x_7, x_8, x_153);
lean_dec(x_159);
return x_160;
}
case 6:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_154, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_154, 2);
lean_inc_ref(x_163);
x_164 = lean_ctor_get_uint8(x_154, sizeof(void*)*3 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_162);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_165 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_162, x_4, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_163);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_168 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_163, x_4, x_5, x_6, x_7, x_8, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec_ref(x_168);
x_171 = lean_ptr_addr(x_162);
lean_dec_ref(x_162);
x_172 = lean_ptr_addr(x_166);
x_173 = lean_usize_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_dec_ref(x_163);
x_42 = x_154;
x_43 = x_161;
x_44 = x_166;
x_45 = x_170;
x_46 = x_169;
x_47 = x_164;
x_48 = x_173;
goto block_55;
}
else
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_163);
lean_dec_ref(x_163);
x_175 = lean_ptr_addr(x_169);
x_176 = lean_usize_dec_eq(x_174, x_175);
x_42 = x_154;
x_43 = x_161;
x_44 = x_166;
x_45 = x_170;
x_46 = x_169;
x_47 = x_164;
x_48 = x_176;
goto block_55;
}
}
else
{
lean_dec(x_166);
lean_dec_ref(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_168;
}
}
else
{
lean_dec_ref(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_165;
}
}
case 7:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_154, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_154, 2);
lean_inc_ref(x_179);
x_180 = lean_ctor_get_uint8(x_154, sizeof(void*)*3 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_178);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_181 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_178, x_4, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec_ref(x_181);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_179);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_184 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_179, x_4, x_5, x_6, x_7, x_8, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; size_t x_187; size_t x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_ptr_addr(x_178);
lean_dec_ref(x_178);
x_188 = lean_ptr_addr(x_182);
x_189 = lean_usize_dec_eq(x_187, x_188);
if (x_189 == 0)
{
lean_dec_ref(x_179);
x_28 = x_154;
x_29 = x_186;
x_30 = x_185;
x_31 = x_180;
x_32 = x_182;
x_33 = x_177;
x_34 = x_189;
goto block_41;
}
else
{
size_t x_190; size_t x_191; uint8_t x_192; 
x_190 = lean_ptr_addr(x_179);
lean_dec_ref(x_179);
x_191 = lean_ptr_addr(x_185);
x_192 = lean_usize_dec_eq(x_190, x_191);
x_28 = x_154;
x_29 = x_186;
x_30 = x_185;
x_31 = x_180;
x_32 = x_182;
x_33 = x_177;
x_34 = x_192;
goto block_41;
}
}
else
{
lean_dec(x_182);
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_184;
}
}
else
{
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_181;
}
}
case 8:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_193 = lean_ctor_get(x_154, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_154, 2);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_154, 3);
lean_inc_ref(x_196);
x_197 = lean_ctor_get_uint8(x_154, sizeof(void*)*4 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_194);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_198 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_194, x_4, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_195);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_201 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_195, x_4, x_5, x_6, x_7, x_8, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_196);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_204 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_196, x_4, x_5, x_6, x_7, x_8, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; size_t x_207; size_t x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
x_207 = lean_ptr_addr(x_194);
lean_dec_ref(x_194);
x_208 = lean_ptr_addr(x_199);
x_209 = lean_usize_dec_eq(x_207, x_208);
if (x_209 == 0)
{
lean_dec_ref(x_195);
x_10 = x_154;
x_11 = x_206;
x_12 = x_205;
x_13 = x_202;
x_14 = x_196;
x_15 = x_197;
x_16 = x_199;
x_17 = x_193;
x_18 = x_209;
goto block_27;
}
else
{
size_t x_210; size_t x_211; uint8_t x_212; 
x_210 = lean_ptr_addr(x_195);
lean_dec_ref(x_195);
x_211 = lean_ptr_addr(x_202);
x_212 = lean_usize_dec_eq(x_210, x_211);
x_10 = x_154;
x_11 = x_206;
x_12 = x_205;
x_13 = x_202;
x_14 = x_196;
x_15 = x_197;
x_16 = x_199;
x_17 = x_193;
x_18 = x_212;
goto block_27;
}
}
else
{
lean_dec(x_202);
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_204;
}
}
else
{
lean_dec(x_199);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_201;
}
}
else
{
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_198;
}
}
case 10:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_154, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_214);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_214);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_215 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_214, x_4, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec_ref(x_215);
x_218 = lean_ptr_addr(x_214);
lean_dec_ref(x_214);
x_219 = lean_ptr_addr(x_216);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
lean_dec_ref(x_154);
x_221 = l_Lean_Expr_mdata___override(x_213, x_216);
x_222 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_221, x_4, x_5, x_6, x_7, x_8, x_217);
return x_222;
}
else
{
lean_object* x_223; 
lean_dec(x_216);
lean_dec(x_213);
x_223 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_154, x_4, x_5, x_6, x_7, x_8, x_217);
return x_223;
}
}
else
{
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_215;
}
}
case 11:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_154, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_154, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_154, 2);
lean_inc_ref(x_226);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_226);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_227 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_1, x_3, x_226, x_4, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; size_t x_230; size_t x_231; uint8_t x_232; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec_ref(x_227);
x_230 = lean_ptr_addr(x_226);
lean_dec_ref(x_226);
x_231 = lean_ptr_addr(x_228);
x_232 = lean_usize_dec_eq(x_230, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
lean_dec_ref(x_154);
x_233 = l_Lean_Expr_proj___override(x_224, x_225, x_228);
x_234 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_233, x_4, x_5, x_6, x_7, x_8, x_229);
return x_234;
}
else
{
lean_object* x_235; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_224);
x_235 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_154, x_4, x_5, x_6, x_7, x_8, x_229);
return x_235;
}
}
else
{
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_154);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_227;
}
}
default: 
{
lean_object* x_236; 
x_236 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_154, x_4, x_5, x_6, x_7, x_8, x_153);
return x_236;
}
}
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_247 = !lean_is_exclusive(x_56);
if (x_247 == 0)
{
return x_56;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_56, 0);
x_249 = lean_ctor_get(x_56, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_56);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
block_27:
{
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_14);
lean_dec_ref(x_10);
x_19 = l_Lean_Expr_letE___override(x_17, x_16, x_13, x_12, x_15);
x_20 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_11);
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_ptr_addr(x_14);
lean_dec_ref(x_14);
x_22 = lean_ptr_addr(x_12);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_10);
x_24 = l_Lean_Expr_letE___override(x_17, x_16, x_13, x_12, x_15);
x_25 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_24, x_4, x_5, x_6, x_7, x_8, x_11);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_26 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_10, x_4, x_5, x_6, x_7, x_8, x_11);
return x_26;
}
}
}
block_41:
{
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_28);
x_35 = l_Lean_Expr_forallE___override(x_33, x_32, x_30, x_31);
x_36 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_35, x_4, x_5, x_6, x_7, x_8, x_29);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_31, x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_28);
x_38 = l_Lean_Expr_forallE___override(x_33, x_32, x_30, x_31);
x_39 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_38, x_4, x_5, x_6, x_7, x_8, x_29);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
x_40 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_28, x_4, x_5, x_6, x_7, x_8, x_29);
return x_40;
}
}
}
block_55:
{
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_42);
x_49 = l_Lean_Expr_lam___override(x_43, x_44, x_46, x_47);
x_50 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8, x_45);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_47, x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_42);
x_52 = l_Lean_Expr_lam___override(x_43, x_44, x_46, x_47);
x_53 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_52, x_4, x_5, x_6, x_7, x_8, x_45);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec_ref(x_46);
lean_dec_ref(x_44);
lean_dec(x_43);
x_54 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__1(x_1, x_3, x_42, x_4, x_5, x_6, x_7, x_8, x_45);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_box(0);
x_21 = lean_array_get_size(x_12);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_usize_sub(x_22, x_2);
x_24 = lean_usize_land(x_3, x_23);
x_25 = lean_array_uget(x_12, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_4, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_12, x_24, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_30);
lean_ctor_set(x_8, 1, x_37);
lean_ctor_set(x_8, 0, x_28);
x_14 = x_8;
goto block_20;
}
else
{
lean_ctor_set(x_8, 1, x_30);
lean_ctor_set(x_8, 0, x_28);
x_14 = x_8;
goto block_20;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_uset(x_12, x_24, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_4, x_5, x_25);
x_41 = lean_array_uset(x_39, x_24, x_40);
lean_ctor_set(x_8, 1, x_41);
x_14 = x_8;
goto block_20;
}
block_20:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_set(x_1, x_14, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_box(0);
x_51 = lean_array_get_size(x_43);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = lean_usize_sub(x_52, x_2);
x_54 = lean_usize_land(x_3, x_53);
x_55 = lean_array_uget(x_43, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_4, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_42, x_57);
lean_dec(x_42);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_array_uset(x_43, x_54, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_45 = x_68;
goto block_50;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
x_45 = x_69;
goto block_50;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = lean_array_uset(x_43, x_54, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_4, x_5, x_55);
x_73 = lean_array_uset(x_71, x_54, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_73);
x_45 = x_74;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_st_ref_set(x_1, x_45, x_9);
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
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_4);
x_11 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), x_10, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_Expr_hash(x_3);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
lean_dec_ref(x_15);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_3, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_11);
lean_inc_ref(x_3);
x_31 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1), 9, 3);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_3);
lean_closure_set(x_31, 2, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_32 = l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__4___redArg(x_31, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___boxed__const__1;
x_36 = lean_box_usize(x_24);
lean_inc(x_33);
x_37 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__2___boxed), 6, 5);
lean_closure_set(x_37, 0, x_4);
lean_closure_set(x_37, 1, x_35);
lean_closure_set(x_37, 2, x_36);
lean_closure_set(x_37, 3, x_3);
lean_closure_set(x_37, 4, x_33);
x_38 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), x_37, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_33);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_32;
}
}
else
{
lean_object* x_43; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec_ref(x_30);
lean_ctor_set(x_11, 0, x_43);
return x_11;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_46);
x_48 = l_Lean_Expr_hash(x_3);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_46, x_59);
lean_dec_ref(x_46);
x_61 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_3, x_60);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_inc_ref(x_3);
x_62 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1), 9, 3);
lean_closure_set(x_62, 0, x_1);
lean_closure_set(x_62, 1, x_3);
lean_closure_set(x_62, 2, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_63 = l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__4___redArg(x_62, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___boxed__const__1;
x_67 = lean_box_usize(x_55);
lean_inc(x_64);
x_68 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__2___boxed), 6, 5);
lean_closure_set(x_68, 0, x_4);
lean_closure_set(x_68, 1, x_66);
lean_closure_set(x_68, 2, x_67);
lean_closure_set(x_68, 3, x_3);
lean_closure_set(x_68, 4, x_64);
x_69 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), x_68, x_5, x_6, x_7, x_8, x_65);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_63;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
lean_dec_ref(x_61);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_45);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__4;
x_2 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__5;
x_10 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___lam__0(lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_13 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0(x_2, x_3, x_1, x_11, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_11);
x_17 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___lam__0(lean_box(0), x_16, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_8);
x_9 = l_Lean_isReducible___at_____private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_spec__0(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
x_21 = l_Lean_Meta_Grind_isGrindGadget(x_8);
lean_dec(x_8);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_9);
x_22 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_21, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_37 = x_23;
} else {
 lean_dec_ref(x_23);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_44 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_dec(x_9);
x_46 = l_Lean_Meta_Grind_isGrindGadget(x_8);
lean_dec(x_8);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_46, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_61 = x_47;
} else {
 lean_dec_ref(x_47);
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
lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_45);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_6);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec_ref(x_7);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lam__0___boxed), 6, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lam__1), 6, 0);
x_17 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0(x_1, x_16, x_15, x_2, x_3, x_4, x_5, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_unfoldReducible___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_unfoldReducible___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_MVarId_unfoldReducible___closed__0;
x_8 = l_Lean_MVarId_transformTarget(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_betaReduce(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_betaReduce___lam__0___boxed), 6, 0);
x_8 = l_Lean_MVarId_transformTarget(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_betaReduce___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_byContra_x3f___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byContra_x3f___lam__0___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Classical", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("byContradiction", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_byContra_x3f___lam__0___closed__4;
x_2 = l_Lean_MVarId_byContra_x3f___lam__0___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byContra_x3f___lam__0___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_14 = l_Lean_Expr_isFalse(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_10);
lean_inc(x_12);
x_15 = l_Lean_mkNot(x_12);
x_16 = l_Lean_MVarId_byContra_x3f___lam__0___closed__2;
x_17 = l_Lean_mkArrow___redArg(x_15, x_16, x_6, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_1);
x_20 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_18, x_21, x_3, x_4, x_5, x_6, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_MVarId_byContra_x3f___lam__0___closed__6;
lean_inc(x_24);
x_27 = l_Lean_mkAppB(x_26, x_12, x_24);
x_28 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_27, x_4, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l_Lean_Expr_mvarId_x21(x_24);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Lean_Expr_mvarId_x21(x_24);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_1);
x_41 = lean_box(0);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
lean_inc(x_42);
x_44 = l_Lean_Expr_isFalse(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc(x_42);
x_45 = l_Lean_mkNot(x_42);
x_46 = l_Lean_MVarId_byContra_x3f___lam__0___closed__2;
x_47 = l_Lean_mkArrow___redArg(x_45, x_46, x_6, x_43);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
lean_inc(x_1);
x_50 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_48, x_51, x_3, x_4, x_5, x_6, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_MVarId_byContra_x3f___lam__0___closed__6;
lean_inc(x_54);
x_57 = l_Lean_mkAppB(x_56, x_42, x_54);
x_58 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_57, x_4, x_55);
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
x_61 = l_Lean_Expr_mvarId_x21(x_54);
lean_dec(x_54);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_48);
lean_dec(x_42);
lean_dec_ref(x_3);
lean_dec(x_1);
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_66 = x_50;
} else {
 lean_dec_ref(x_50);
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
lean_object* x_68; lean_object* x_69; 
lean_dec(x_42);
lean_dec_ref(x_3);
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_43);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_10);
if (x_70 == 0)
{
return x_10;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_10, 0);
x_72 = lean_ctor_get(x_10, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_10);
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
lean_dec_ref(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_8);
if (x_74 == 0)
{
return x_8;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_8, 0);
x_76 = lean_ctor_get(x_8, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_8);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("by_contra", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_byContra_x3f___closed__0;
x_2 = l_Lean_MVarId_ensureNoMVar___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_byContra_x3f___closed__1;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_byContra_x3f___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_byContra_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_35);
x_37 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0(x_1, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_35);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec_ref(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec_ref(x_38);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
x_11 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_35);
x_37 = lean_apply_7(x_1, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_35);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec_ref(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec_ref(x_38);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
x_11 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = l_Lean_LocalDecl_isAuxDecl(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_ctor_set(x_1, 0, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_8 = x_19;
goto block_12;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_LocalDecl_isAuxDecl(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_8 = x_24;
goto block_12;
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_array_size(x_10);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__0(x_1, x_11, x_10, x_13, x_14, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_20);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_free_object(x_2);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec_ref(x_17);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec_ref(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_2);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_array_size(x_34);
x_38 = 0;
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__0(x_1, x_35, x_34, x_37, x_38, x_36, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_40);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec_ref(x_41);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_53 = x_39;
} else {
 lean_dec_ref(x_39);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___lam__0___boxed), 7, 0);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
x_60 = lean_array_size(x_56);
x_61 = 0;
x_62 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__1(x_57, x_58, x_56, x_60, x_61, x_59, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
lean_ctor_set(x_2, 0, x_67);
lean_ctor_set(x_62, 0, x_2);
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
lean_ctor_set(x_2, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_63);
lean_free_object(x_2);
x_71 = !lean_is_exclusive(x_62);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_62, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
lean_dec_ref(x_64);
lean_ctor_set(x_62, 0, x_73);
return x_62;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec_ref(x_64);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_free_object(x_2);
x_77 = !lean_is_exclusive(x_62);
if (x_77 == 0)
{
return x_62;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_62, 0);
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_62);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
lean_dec(x_2);
x_82 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___lam__0___boxed), 7, 0);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_3);
x_85 = lean_array_size(x_81);
x_86 = 0;
x_87 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__1(x_82, x_83, x_81, x_85, x_86, x_84, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_81);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_88);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
lean_dec_ref(x_89);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_101 = x_87;
} else {
 lean_dec_ref(x_87);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_27 = x_19;
} else {
 lean_dec_ref(x_19);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec_ref(x_18);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_11 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_39);
x_41 = lean_apply_7(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec_ref(x_41);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec_ref(x_42);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_5, x_53);
x_5 = x_54;
x_6 = x_52;
x_11 = x_50;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = l_Lean_LocalDecl_isAuxDecl(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_ctor_set(x_1, 0, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_8 = x_19;
goto block_12;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_LocalDecl_isAuxDecl(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_8 = x_24;
goto block_12;
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_10 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0(x_2, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec_ref(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec_ref(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec_ref(x_11);
x_20 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0___lam__0___boxed), 7, 0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_size(x_9);
x_24 = 0;
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__3(x_20, x_21, x_9, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_18);
lean_dec_ref(x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_26);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec_ref(x_27);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec_ref(x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the goal mentions the declaration `", 35, 35);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`, which is being defined. To avoid circular reasoning, try rewriting the goal to eliminate `", 93, 93);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` before using `grind`.", 23, 23);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_31; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_10);
lean_inc(x_3);
x_31 = l_Lean_MVarId_clear(x_3, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_2 = x_11;
x_3 = x_32;
x_8 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_47; 
lean_dec(x_11);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
x_47 = l_Lean_Exception_isInterrupt(x_35);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Exception_isRuntime(x_35);
lean_dec(x_35);
x_37 = x_48;
goto block_46;
}
else
{
lean_dec(x_35);
x_37 = x_47;
goto block_46;
}
block_46:
{
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_31);
lean_inc_ref(x_4);
x_38 = l_Lean_FVarId_getDecl___redArg(x_10, x_4, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_39, 2);
lean_inc(x_41);
lean_dec(x_39);
x_13 = x_40;
x_14 = x_41;
goto block_30;
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_31;
}
}
}
block_30:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_15 = l_Lean_Name_mkStr1(x_1);
x_16 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__1;
x_17 = l_Lean_MessageData_ofName(x_14);
lean_inc_ref(x_17);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(7, 2, 0);
} else {
 x_18 = x_12;
 lean_ctor_set_tag(x_18, 7);
}
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
x_22 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__5;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Meta_throwTacticEx___redArg(x_15, x_3, x_24, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_10);
x_13 = lean_box(0);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_14 = l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0(x_12, x_13, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_List_isEmpty___redArg(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_14);
x_19 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg(x_3, x_16, x_1, x_4, x_5, x_6, x_7, x_17);
return x_19;
}
else
{
lean_dec(x_16);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = l_List_isEmpty___redArg(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg(x_3, x_20, x_1, x_4, x_5, x_6, x_7, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_clearAuxDecls___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clear_aux_decls", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_clearAuxDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_clearAuxDecls___closed__0;
x_2 = l_Lean_MVarId_ensureNoMVar___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_MVarId_ensureNoMVar___closed__0;
x_8 = l_Lean_MVarId_clearAuxDecls___closed__1;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_clearAuxDecls___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_7);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0_spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at___Lean_MVarId_clearAuxDecls_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isMData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
case 8:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
case 10:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed), 1, 0);
x_6 = lean_find_expr(x_5, x_1);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lam__2___boxed), 4, 0);
x_10 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_8, x_9, x_2, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_foldProjs___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isProj(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__0;
x_2 = l_Lean_MVarId_ensureNoMVar___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found `Expr.proj` but `", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is not marked as structure", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found `Expr.proj` with invalid field index `", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__12() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; 
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_17);
x_18 = lean_st_ref_get(x_5, x_6);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
lean_dec(x_20);
lean_inc(x_15);
x_23 = l_Lean_getStructureInfo_x3f(x_22, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec_ref(x_17);
lean_dec(x_16);
x_24 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__1;
x_25 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_24, x_4, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_free_object(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec_ref(x_25);
x_7 = x_28;
goto block_10;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__3;
x_33 = l_Lean_MessageData_ofName(x_15);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_33);
lean_ctor_set(x_25, 0, x_32);
x_34 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__5;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_25);
lean_inc_ref(x_1);
x_35 = l_Lean_indentExpr(x_1);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_24, x_38, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_7 = x_40;
goto block_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_dec(x_25);
x_42 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__3;
x_43 = l_Lean_MessageData_ofName(x_15);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__5;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_45);
lean_ctor_set(x_18, 0, x_44);
lean_inc_ref(x_1);
x_46 = l_Lean_indentExpr(x_1);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_18);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_24, x_49, x_2, x_3, x_4, x_5, x_41);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
x_7 = x_51;
goto block_10;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_15);
x_52 = !lean_is_exclusive(x_23);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_54);
lean_dec(x_53);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_16, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec_ref(x_54);
lean_dec_ref(x_17);
x_57 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__1;
x_58 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_57, x_4, x_21);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_free_object(x_23);
lean_free_object(x_18);
lean_dec(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec_ref(x_58);
x_11 = x_61;
goto block_14;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_58, 1);
x_64 = lean_ctor_get(x_58, 0);
lean_dec(x_64);
x_65 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__9;
x_66 = l_Nat_reprFast(x_16);
lean_ctor_set_tag(x_23, 3);
lean_ctor_set(x_23, 0, x_66);
x_67 = l_Lean_MessageData_ofFormat(x_23);
lean_ctor_set_tag(x_58, 7);
lean_ctor_set(x_58, 1, x_67);
lean_ctor_set(x_58, 0, x_65);
x_68 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__11;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_68);
lean_ctor_set(x_18, 0, x_58);
lean_inc_ref(x_1);
x_69 = l_Lean_indentExpr(x_1);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_57, x_72, x_2, x_3, x_4, x_5, x_63);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_11 = x_74;
goto block_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_dec(x_58);
x_76 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__9;
x_77 = l_Nat_reprFast(x_16);
lean_ctor_set_tag(x_23, 3);
lean_ctor_set(x_23, 0, x_77);
x_78 = l_Lean_MessageData_ofFormat(x_23);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__11;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_80);
lean_ctor_set(x_18, 0, x_79);
lean_inc_ref(x_1);
x_81 = l_Lean_indentExpr(x_1);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_18);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_57, x_84, x_2, x_3, x_4, x_5, x_75);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_11 = x_86;
goto block_14;
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_free_object(x_18);
lean_dec_ref(x_1);
x_87 = l_Lean_Meta_Context_config(x_2);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; uint8_t x_99; uint64_t x_100; uint8_t x_101; 
x_89 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_2, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_2, 6);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_97 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_98 = lean_array_fget(x_54, x_16);
lean_dec(x_16);
lean_dec_ref(x_54);
x_99 = 1;
lean_ctor_set_uint8(x_87, 9, x_99);
x_100 = l_Lean_Meta_Context_configKey(x_2);
x_101 = !lean_is_exclusive(x_2);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; lean_object* x_114; lean_object* x_115; 
x_102 = lean_ctor_get(x_2, 6);
lean_dec(x_102);
x_103 = lean_ctor_get(x_2, 5);
lean_dec(x_103);
x_104 = lean_ctor_get(x_2, 4);
lean_dec(x_104);
x_105 = lean_ctor_get(x_2, 3);
lean_dec(x_105);
x_106 = lean_ctor_get(x_2, 2);
lean_dec(x_106);
x_107 = lean_ctor_get(x_2, 1);
lean_dec(x_107);
x_108 = lean_ctor_get(x_2, 0);
lean_dec(x_108);
x_109 = 2;
x_110 = lean_uint64_shift_right(x_100, x_109);
x_111 = lean_uint64_shift_left(x_110, x_109);
x_112 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__12;
x_113 = lean_uint64_lor(x_111, x_112);
x_114 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_114, 0, x_87);
lean_ctor_set_uint64(x_114, sizeof(void*)*1, x_113);
lean_ctor_set(x_2, 0, x_114);
x_115 = l_Lean_Meta_mkProjection(x_17, x_98, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_ctor_set(x_23, 0, x_117);
lean_ctor_set(x_115, 0, x_23);
return x_115;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_115, 0);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_115);
lean_ctor_set(x_23, 0, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_23);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_free_object(x_23);
x_121 = !lean_is_exclusive(x_115);
if (x_121 == 0)
{
return x_115;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_115, 0);
x_123 = lean_ctor_get(x_115, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_115);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_2);
x_125 = 2;
x_126 = lean_uint64_shift_right(x_100, x_125);
x_127 = lean_uint64_shift_left(x_126, x_125);
x_128 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__12;
x_129 = lean_uint64_lor(x_127, x_128);
x_130 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_130, 0, x_87);
lean_ctor_set_uint64(x_130, sizeof(void*)*1, x_129);
x_131 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_90);
lean_ctor_set(x_131, 2, x_91);
lean_ctor_set(x_131, 3, x_92);
lean_ctor_set(x_131, 4, x_93);
lean_ctor_set(x_131, 5, x_94);
lean_ctor_set(x_131, 6, x_95);
lean_ctor_set_uint8(x_131, sizeof(void*)*7, x_89);
lean_ctor_set_uint8(x_131, sizeof(void*)*7 + 1, x_96);
lean_ctor_set_uint8(x_131, sizeof(void*)*7 + 2, x_97);
x_132 = l_Lean_Meta_mkProjection(x_17, x_98, x_131, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
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
lean_ctor_set(x_23, 0, x_133);
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_23);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_23);
x_137 = lean_ctor_get(x_132, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; uint64_t x_171; lean_object* x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; uint64_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_141 = lean_ctor_get_uint8(x_87, 0);
x_142 = lean_ctor_get_uint8(x_87, 1);
x_143 = lean_ctor_get_uint8(x_87, 2);
x_144 = lean_ctor_get_uint8(x_87, 3);
x_145 = lean_ctor_get_uint8(x_87, 4);
x_146 = lean_ctor_get_uint8(x_87, 5);
x_147 = lean_ctor_get_uint8(x_87, 6);
x_148 = lean_ctor_get_uint8(x_87, 7);
x_149 = lean_ctor_get_uint8(x_87, 8);
x_150 = lean_ctor_get_uint8(x_87, 10);
x_151 = lean_ctor_get_uint8(x_87, 11);
x_152 = lean_ctor_get_uint8(x_87, 12);
x_153 = lean_ctor_get_uint8(x_87, 13);
x_154 = lean_ctor_get_uint8(x_87, 14);
x_155 = lean_ctor_get_uint8(x_87, 15);
x_156 = lean_ctor_get_uint8(x_87, 16);
x_157 = lean_ctor_get_uint8(x_87, 17);
x_158 = lean_ctor_get_uint8(x_87, 18);
lean_dec(x_87);
x_159 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_160 = lean_ctor_get(x_2, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_2, 4);
lean_inc(x_163);
x_164 = lean_ctor_get(x_2, 5);
lean_inc(x_164);
x_165 = lean_ctor_get(x_2, 6);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_167 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_168 = lean_array_fget(x_54, x_16);
lean_dec(x_16);
lean_dec_ref(x_54);
x_169 = 1;
x_170 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_170, 0, x_141);
lean_ctor_set_uint8(x_170, 1, x_142);
lean_ctor_set_uint8(x_170, 2, x_143);
lean_ctor_set_uint8(x_170, 3, x_144);
lean_ctor_set_uint8(x_170, 4, x_145);
lean_ctor_set_uint8(x_170, 5, x_146);
lean_ctor_set_uint8(x_170, 6, x_147);
lean_ctor_set_uint8(x_170, 7, x_148);
lean_ctor_set_uint8(x_170, 8, x_149);
lean_ctor_set_uint8(x_170, 9, x_169);
lean_ctor_set_uint8(x_170, 10, x_150);
lean_ctor_set_uint8(x_170, 11, x_151);
lean_ctor_set_uint8(x_170, 12, x_152);
lean_ctor_set_uint8(x_170, 13, x_153);
lean_ctor_set_uint8(x_170, 14, x_154);
lean_ctor_set_uint8(x_170, 15, x_155);
lean_ctor_set_uint8(x_170, 16, x_156);
lean_ctor_set_uint8(x_170, 17, x_157);
lean_ctor_set_uint8(x_170, 18, x_158);
x_171 = l_Lean_Meta_Context_configKey(x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_172 = x_2;
} else {
 lean_dec_ref(x_2);
 x_172 = lean_box(0);
}
x_173 = 2;
x_174 = lean_uint64_shift_right(x_171, x_173);
x_175 = lean_uint64_shift_left(x_174, x_173);
x_176 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__12;
x_177 = lean_uint64_lor(x_175, x_176);
x_178 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_178, 0, x_170);
lean_ctor_set_uint64(x_178, sizeof(void*)*1, x_177);
if (lean_is_scalar(x_172)) {
 x_179 = lean_alloc_ctor(0, 7, 3);
} else {
 x_179 = x_172;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_160);
lean_ctor_set(x_179, 2, x_161);
lean_ctor_set(x_179, 3, x_162);
lean_ctor_set(x_179, 4, x_163);
lean_ctor_set(x_179, 5, x_164);
lean_ctor_set(x_179, 6, x_165);
lean_ctor_set_uint8(x_179, sizeof(void*)*7, x_159);
lean_ctor_set_uint8(x_179, sizeof(void*)*7 + 1, x_166);
lean_ctor_set_uint8(x_179, sizeof(void*)*7 + 2, x_167);
x_180 = l_Lean_Meta_mkProjection(x_17, x_168, x_179, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
lean_ctor_set(x_23, 0, x_181);
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_23);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_free_object(x_23);
x_185 = lean_ctor_get(x_180, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_187 = x_180;
} else {
 lean_dec_ref(x_180);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_23, 0);
lean_inc(x_189);
lean_dec(x_23);
x_190 = lean_ctor_get(x_189, 1);
lean_inc_ref(x_190);
lean_dec(x_189);
x_191 = lean_array_get_size(x_190);
x_192 = lean_nat_dec_lt(x_16, x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec_ref(x_190);
lean_dec_ref(x_17);
x_193 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__1;
x_194 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_193, x_4, x_21);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_free_object(x_18);
lean_dec(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec_ref(x_194);
x_11 = x_197;
goto block_14;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_199 = x_194;
} else {
 lean_dec_ref(x_194);
 x_199 = lean_box(0);
}
x_200 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__9;
x_201 = l_Nat_reprFast(x_16);
x_202 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = l_Lean_MessageData_ofFormat(x_202);
if (lean_is_scalar(x_199)) {
 x_204 = lean_alloc_ctor(7, 2, 0);
} else {
 x_204 = x_199;
 lean_ctor_set_tag(x_204, 7);
}
lean_ctor_set(x_204, 0, x_200);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__11;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_205);
lean_ctor_set(x_18, 0, x_204);
lean_inc_ref(x_1);
x_206 = l_Lean_indentExpr(x_1);
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_18);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_193, x_209, x_2, x_3, x_4, x_5, x_198);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec_ref(x_210);
x_11 = x_211;
goto block_14;
}
}
else
{
lean_object* x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; uint64_t x_244; lean_object* x_245; uint64_t x_246; uint64_t x_247; uint64_t x_248; uint64_t x_249; uint64_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_free_object(x_18);
lean_dec_ref(x_1);
x_212 = l_Lean_Meta_Context_config(x_2);
x_213 = lean_ctor_get_uint8(x_212, 0);
x_214 = lean_ctor_get_uint8(x_212, 1);
x_215 = lean_ctor_get_uint8(x_212, 2);
x_216 = lean_ctor_get_uint8(x_212, 3);
x_217 = lean_ctor_get_uint8(x_212, 4);
x_218 = lean_ctor_get_uint8(x_212, 5);
x_219 = lean_ctor_get_uint8(x_212, 6);
x_220 = lean_ctor_get_uint8(x_212, 7);
x_221 = lean_ctor_get_uint8(x_212, 8);
x_222 = lean_ctor_get_uint8(x_212, 10);
x_223 = lean_ctor_get_uint8(x_212, 11);
x_224 = lean_ctor_get_uint8(x_212, 12);
x_225 = lean_ctor_get_uint8(x_212, 13);
x_226 = lean_ctor_get_uint8(x_212, 14);
x_227 = lean_ctor_get_uint8(x_212, 15);
x_228 = lean_ctor_get_uint8(x_212, 16);
x_229 = lean_ctor_get_uint8(x_212, 17);
x_230 = lean_ctor_get_uint8(x_212, 18);
if (lean_is_exclusive(x_212)) {
 x_231 = x_212;
} else {
 lean_dec_ref(x_212);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_233 = lean_ctor_get(x_2, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_234);
x_235 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_235);
x_236 = lean_ctor_get(x_2, 4);
lean_inc(x_236);
x_237 = lean_ctor_get(x_2, 5);
lean_inc(x_237);
x_238 = lean_ctor_get(x_2, 6);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_240 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_241 = lean_array_fget(x_190, x_16);
lean_dec(x_16);
lean_dec_ref(x_190);
x_242 = 1;
if (lean_is_scalar(x_231)) {
 x_243 = lean_alloc_ctor(0, 0, 19);
} else {
 x_243 = x_231;
}
lean_ctor_set_uint8(x_243, 0, x_213);
lean_ctor_set_uint8(x_243, 1, x_214);
lean_ctor_set_uint8(x_243, 2, x_215);
lean_ctor_set_uint8(x_243, 3, x_216);
lean_ctor_set_uint8(x_243, 4, x_217);
lean_ctor_set_uint8(x_243, 5, x_218);
lean_ctor_set_uint8(x_243, 6, x_219);
lean_ctor_set_uint8(x_243, 7, x_220);
lean_ctor_set_uint8(x_243, 8, x_221);
lean_ctor_set_uint8(x_243, 9, x_242);
lean_ctor_set_uint8(x_243, 10, x_222);
lean_ctor_set_uint8(x_243, 11, x_223);
lean_ctor_set_uint8(x_243, 12, x_224);
lean_ctor_set_uint8(x_243, 13, x_225);
lean_ctor_set_uint8(x_243, 14, x_226);
lean_ctor_set_uint8(x_243, 15, x_227);
lean_ctor_set_uint8(x_243, 16, x_228);
lean_ctor_set_uint8(x_243, 17, x_229);
lean_ctor_set_uint8(x_243, 18, x_230);
x_244 = l_Lean_Meta_Context_configKey(x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_245 = x_2;
} else {
 lean_dec_ref(x_2);
 x_245 = lean_box(0);
}
x_246 = 2;
x_247 = lean_uint64_shift_right(x_244, x_246);
x_248 = lean_uint64_shift_left(x_247, x_246);
x_249 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__12;
x_250 = lean_uint64_lor(x_248, x_249);
x_251 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set_uint64(x_251, sizeof(void*)*1, x_250);
if (lean_is_scalar(x_245)) {
 x_252 = lean_alloc_ctor(0, 7, 3);
} else {
 x_252 = x_245;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_233);
lean_ctor_set(x_252, 2, x_234);
lean_ctor_set(x_252, 3, x_235);
lean_ctor_set(x_252, 4, x_236);
lean_ctor_set(x_252, 5, x_237);
lean_ctor_set(x_252, 6, x_238);
lean_ctor_set_uint8(x_252, sizeof(void*)*7, x_232);
lean_ctor_set_uint8(x_252, sizeof(void*)*7 + 1, x_239);
lean_ctor_set_uint8(x_252, sizeof(void*)*7 + 2, x_240);
x_253 = l_Lean_Meta_mkProjection(x_17, x_241, x_252, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_254);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_255);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_253, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_253, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_261 = x_253;
} else {
 lean_dec_ref(x_253);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_18, 0);
x_264 = lean_ctor_get(x_18, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_18);
x_265 = lean_ctor_get(x_263, 0);
lean_inc_ref(x_265);
lean_dec(x_263);
lean_inc(x_15);
x_266 = l_Lean_getStructureInfo_x3f(x_265, x_15);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
lean_dec_ref(x_17);
lean_dec(x_16);
x_267 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__1;
x_268 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_267, x_4, x_264);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_unbox(x_269);
lean_dec(x_269);
if (x_270 == 0)
{
lean_object* x_271; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec_ref(x_268);
x_7 = x_271;
goto block_10;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_272 = lean_ctor_get(x_268, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_273 = x_268;
} else {
 lean_dec_ref(x_268);
 x_273 = lean_box(0);
}
x_274 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__3;
x_275 = l_Lean_MessageData_ofName(x_15);
if (lean_is_scalar(x_273)) {
 x_276 = lean_alloc_ctor(7, 2, 0);
} else {
 x_276 = x_273;
 lean_ctor_set_tag(x_276, 7);
}
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__5;
x_278 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
lean_inc_ref(x_1);
x_279 = l_Lean_indentExpr(x_1);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_267, x_282, x_2, x_3, x_4, x_5, x_272);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec_ref(x_283);
x_7 = x_284;
goto block_10;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_15);
x_285 = lean_ctor_get(x_266, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_286 = x_266;
} else {
 lean_dec_ref(x_266);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_285, 1);
lean_inc_ref(x_287);
lean_dec(x_285);
x_288 = lean_array_get_size(x_287);
x_289 = lean_nat_dec_lt(x_16, x_288);
lean_dec(x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_dec_ref(x_287);
lean_dec_ref(x_17);
x_290 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__1;
x_291 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_290, x_4, x_264);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_286);
lean_dec(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec_ref(x_291);
x_11 = x_294;
goto block_14;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_296 = x_291;
} else {
 lean_dec_ref(x_291);
 x_296 = lean_box(0);
}
x_297 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__9;
x_298 = l_Nat_reprFast(x_16);
if (lean_is_scalar(x_286)) {
 x_299 = lean_alloc_ctor(3, 1, 0);
} else {
 x_299 = x_286;
 lean_ctor_set_tag(x_299, 3);
}
lean_ctor_set(x_299, 0, x_298);
x_300 = l_Lean_MessageData_ofFormat(x_299);
if (lean_is_scalar(x_296)) {
 x_301 = lean_alloc_ctor(7, 2, 0);
} else {
 x_301 = x_296;
 lean_ctor_set_tag(x_301, 7);
}
lean_ctor_set(x_301, 0, x_297);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__11;
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
lean_inc_ref(x_1);
x_304 = l_Lean_indentExpr(x_1);
x_305 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__7;
x_307 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_290, x_307, x_2, x_3, x_4, x_5, x_295);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec_ref(x_308);
x_11 = x_309;
goto block_14;
}
}
else
{
lean_object* x_310; uint8_t x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; uint8_t x_316; uint8_t x_317; uint8_t x_318; uint8_t x_319; uint8_t x_320; uint8_t x_321; uint8_t x_322; uint8_t x_323; uint8_t x_324; uint8_t x_325; uint8_t x_326; uint8_t x_327; uint8_t x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; uint8_t x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; uint64_t x_342; lean_object* x_343; uint64_t x_344; uint64_t x_345; uint64_t x_346; uint64_t x_347; uint64_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec_ref(x_1);
x_310 = l_Lean_Meta_Context_config(x_2);
x_311 = lean_ctor_get_uint8(x_310, 0);
x_312 = lean_ctor_get_uint8(x_310, 1);
x_313 = lean_ctor_get_uint8(x_310, 2);
x_314 = lean_ctor_get_uint8(x_310, 3);
x_315 = lean_ctor_get_uint8(x_310, 4);
x_316 = lean_ctor_get_uint8(x_310, 5);
x_317 = lean_ctor_get_uint8(x_310, 6);
x_318 = lean_ctor_get_uint8(x_310, 7);
x_319 = lean_ctor_get_uint8(x_310, 8);
x_320 = lean_ctor_get_uint8(x_310, 10);
x_321 = lean_ctor_get_uint8(x_310, 11);
x_322 = lean_ctor_get_uint8(x_310, 12);
x_323 = lean_ctor_get_uint8(x_310, 13);
x_324 = lean_ctor_get_uint8(x_310, 14);
x_325 = lean_ctor_get_uint8(x_310, 15);
x_326 = lean_ctor_get_uint8(x_310, 16);
x_327 = lean_ctor_get_uint8(x_310, 17);
x_328 = lean_ctor_get_uint8(x_310, 18);
if (lean_is_exclusive(x_310)) {
 x_329 = x_310;
} else {
 lean_dec_ref(x_310);
 x_329 = lean_box(0);
}
x_330 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_331 = lean_ctor_get(x_2, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_332);
x_333 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_333);
x_334 = lean_ctor_get(x_2, 4);
lean_inc(x_334);
x_335 = lean_ctor_get(x_2, 5);
lean_inc(x_335);
x_336 = lean_ctor_get(x_2, 6);
lean_inc(x_336);
x_337 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_338 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_339 = lean_array_fget(x_287, x_16);
lean_dec(x_16);
lean_dec_ref(x_287);
x_340 = 1;
if (lean_is_scalar(x_329)) {
 x_341 = lean_alloc_ctor(0, 0, 19);
} else {
 x_341 = x_329;
}
lean_ctor_set_uint8(x_341, 0, x_311);
lean_ctor_set_uint8(x_341, 1, x_312);
lean_ctor_set_uint8(x_341, 2, x_313);
lean_ctor_set_uint8(x_341, 3, x_314);
lean_ctor_set_uint8(x_341, 4, x_315);
lean_ctor_set_uint8(x_341, 5, x_316);
lean_ctor_set_uint8(x_341, 6, x_317);
lean_ctor_set_uint8(x_341, 7, x_318);
lean_ctor_set_uint8(x_341, 8, x_319);
lean_ctor_set_uint8(x_341, 9, x_340);
lean_ctor_set_uint8(x_341, 10, x_320);
lean_ctor_set_uint8(x_341, 11, x_321);
lean_ctor_set_uint8(x_341, 12, x_322);
lean_ctor_set_uint8(x_341, 13, x_323);
lean_ctor_set_uint8(x_341, 14, x_324);
lean_ctor_set_uint8(x_341, 15, x_325);
lean_ctor_set_uint8(x_341, 16, x_326);
lean_ctor_set_uint8(x_341, 17, x_327);
lean_ctor_set_uint8(x_341, 18, x_328);
x_342 = l_Lean_Meta_Context_configKey(x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_343 = x_2;
} else {
 lean_dec_ref(x_2);
 x_343 = lean_box(0);
}
x_344 = 2;
x_345 = lean_uint64_shift_right(x_342, x_344);
x_346 = lean_uint64_shift_left(x_345, x_344);
x_347 = l_Lean_Meta_Grind_foldProjs___lam__2___closed__12;
x_348 = lean_uint64_lor(x_346, x_347);
x_349 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_349, 0, x_341);
lean_ctor_set_uint64(x_349, sizeof(void*)*1, x_348);
if (lean_is_scalar(x_343)) {
 x_350 = lean_alloc_ctor(0, 7, 3);
} else {
 x_350 = x_343;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_331);
lean_ctor_set(x_350, 2, x_332);
lean_ctor_set(x_350, 3, x_333);
lean_ctor_set(x_350, 4, x_334);
lean_ctor_set(x_350, 5, x_335);
lean_ctor_set(x_350, 6, x_336);
lean_ctor_set_uint8(x_350, sizeof(void*)*7, x_330);
lean_ctor_set_uint8(x_350, sizeof(void*)*7 + 1, x_337);
lean_ctor_set_uint8(x_350, sizeof(void*)*7 + 2, x_338);
x_351 = l_Lean_Meta_mkProjection(x_17, x_339, x_350, x_3, x_4, x_5, x_264);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_355 = lean_alloc_ctor(1, 1, 0);
} else {
 x_355 = x_286;
}
lean_ctor_set(x_355, 0, x_352);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_353);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_286);
x_357 = lean_ctor_get(x_351, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_351, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_359 = x_351;
} else {
 lean_dec_ref(x_351);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
}
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_361, 0, x_1);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_6);
return x_362;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_foldProjs___lam__0___boxed), 1, 0);
x_8 = lean_find_expr(x_7, x_1);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_dec_ref(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_foldProjs___lam__1___boxed), 6, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_foldProjs___lam__2), 6, 0);
x_12 = 0;
x_13 = l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(x_1, x_10, x_11, x_12, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_foldProjs___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_foldProjs___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_normalizeLevels_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Level_normalize(x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Level_normalize(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; 
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = l_Lean_Level_normalize(x_13);
x_15 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_16 = lean_ptr_addr(x_14);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_1);
x_18 = l_Lean_Expr_sort___override(x_14);
x_5 = x_18;
goto block_8;
}
else
{
lean_dec(x_14);
x_5 = x_1;
goto block_8;
}
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_box(0);
lean_inc(x_20);
x_22 = l_List_mapTR_loop___at___Lean_Meta_Grind_normalizeLevels_spec__0(x_20, x_21);
x_23 = l_ptrEqList___redArg(x_20, x_22);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_1);
x_24 = l_Lean_Expr_const___override(x_19, x_22);
x_9 = x_24;
goto block_12;
}
else
{
lean_dec(x_22);
lean_dec(x_19);
x_9 = x_1;
goto block_12;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_1);
x_25 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeLevels___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lam__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_normalizeLevels___lam__0___boxed), 4, 0);
x_6 = l_Lean_Meta_Grind_normalizeLevels___closed__0;
x_7 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_normalizeLevels___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_grind_normalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MatchCond", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_markAsMatchCond___closed__0;
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_3 = l_Lean_Meta_Grind_isGrindGadget___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_markAsMatchCond___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_markAsMatchCond___closed__2;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Grind_markAsMatchCond___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isMatchCond(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PreMatchCond", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__0;
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_3 = l_Lean_Meta_Grind_isGrindGadget___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isPreMatchCond(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_1);
x_4 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_11 = l_Lean_Expr_cleanupAnnotations(x_5);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_1);
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
lean_dec_ref(x_13);
if (x_15 == 0)
{
lean_dec_ref(x_1);
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0;
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(0, 2, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_reducePreMatchCond___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_reducePreMatchCond___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_reducePreMatchCond(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__0____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reducePreMatchCond", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__2____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__0____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_4 = l_Lean_Meta_Grind_isGrindGadget___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__3____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__4____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__5____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__3____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_2 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__4____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__6____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__5____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__2____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_3 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__6____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__2____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_;
x_6 = 0;
x_7 = l_Lean_Meta_Simp_Simprocs_add(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_addPreMatchCondSimproc(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_1);
x_11 = l_Lean_Expr_cleanupAnnotations(x_1);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_15 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec_ref(x_14);
if (x_16 == 0)
{
lean_dec_ref(x_13);
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_1);
x_17 = l_Lean_Meta_Grind_markAsMatchCond(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_isPreMatchCond___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lam__0___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Grind_replacePreMatchCond___closed__0;
x_8 = lean_find_expr(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed), 6, 0);
x_15 = l_Lean_Meta_Grind_replacePreMatchCond___closed__1;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_16 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0(x_1, x_14, x_15, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_17);
x_19 = l_Lean_Meta_mkEqRefl(x_17, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_inc(x_17);
x_22 = l_Lean_Meta_mkEq(x_1, x_17, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = 1;
x_26 = l_Lean_Meta_mkExpectedPropHint(x_20, x_24);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_25);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = 1;
x_31 = l_Lean_Meta_mkExpectedPropHint(x_20, x_28);
lean_ctor_set(x_8, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_8);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_8);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
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
lean_dec(x_17);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
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
lean_free_object(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_16);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed), 6, 0);
x_47 = l_Lean_Meta_Grind_replacePreMatchCond___closed__1;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_48 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0(x_1, x_46, x_47, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_49);
x_51 = l_Lean_Meta_mkEqRefl(x_49, x_2, x_3, x_4, x_5, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
lean_inc(x_49);
x_54 = l_Lean_Meta_mkEq(x_1, x_49, x_2, x_3, x_4, x_5, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = 1;
x_59 = l_Lean_Meta_mkExpectedPropHint(x_52, x_55);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_58);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_52);
lean_dec(x_49);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
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
lean_dec(x_49);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_51, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_69 = x_51;
} else {
 lean_dec_ref(x_51);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_48, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_48, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_73 = x_48;
} else {
 lean_dec_ref(x_48);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isIte___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isIte___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_isIte___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_isIte___closed__1;
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(5u);
x_5 = l_Lean_Expr_getAppNumArgs(x_1);
x_6 = lean_nat_dec_le(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isIte(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isDIte___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isDIte___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_isDIte___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_isDIte___closed__1;
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(5u);
x_5 = l_Lean_Expr_getAppNumArgs(x_1);
x_6 = lean_nat_dec_le(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isDIte(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isApp(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_appFn_x21(x_1);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_4);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_appFn_x21(x_4);
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_getBinOp(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractNestedProofs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_ensureNoMVar___closed__0 = _init_l_Lean_MVarId_ensureNoMVar___closed__0();
lean_mark_persistent(l_Lean_MVarId_ensureNoMVar___closed__0);
l_Lean_MVarId_ensureNoMVar___closed__1 = _init_l_Lean_MVarId_ensureNoMVar___closed__1();
lean_mark_persistent(l_Lean_MVarId_ensureNoMVar___closed__1);
l_Lean_MVarId_ensureNoMVar___closed__2 = _init_l_Lean_MVarId_ensureNoMVar___closed__2();
lean_mark_persistent(l_Lean_MVarId_ensureNoMVar___closed__2);
l_Lean_MVarId_ensureNoMVar___closed__3 = _init_l_Lean_MVarId_ensureNoMVar___closed__3();
lean_mark_persistent(l_Lean_MVarId_ensureNoMVar___closed__3);
l_Lean_MVarId_ensureNoMVar___closed__4 = _init_l_Lean_MVarId_ensureNoMVar___closed__4();
lean_mark_persistent(l_Lean_MVarId_ensureNoMVar___closed__4);
l_Lean_MVarId_ensureNoMVar___closed__5 = _init_l_Lean_MVarId_ensureNoMVar___closed__5();
lean_mark_persistent(l_Lean_MVarId_ensureNoMVar___closed__5);
l_Lean_Meta_Grind_isGrindGadget___closed__0 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__0);
l_Lean_Meta_Grind_isGrindGadget___closed__1 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__1);
l_Lean_Meta_Grind_isGrindGadget___closed__2 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__2);
l_Lean_Meta_Grind_isGrindGadget___closed__3 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__3);
l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1___closed__0 = _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1___closed__0();
lean_mark_persistent(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___lam__1___closed__0);
l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___boxed__const__1 = _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___boxed__const__1();
lean_mark_persistent(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0_spec__0___boxed__const__1);
l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__0 = _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__0();
lean_mark_persistent(l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__0);
l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__1 = _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__1();
lean_mark_persistent(l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__1);
l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__2 = _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__2();
lean_mark_persistent(l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__2);
l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__3 = _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__3();
lean_mark_persistent(l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__3);
l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__4 = _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__4();
lean_mark_persistent(l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__4);
l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__5 = _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__5();
lean_mark_persistent(l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_spec__0___closed__5);
l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0 = _init_l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_unfoldReducible___lam__1___closed__0);
l_Lean_MVarId_unfoldReducible___closed__0 = _init_l_Lean_MVarId_unfoldReducible___closed__0();
lean_mark_persistent(l_Lean_MVarId_unfoldReducible___closed__0);
l_Lean_MVarId_byContra_x3f___lam__0___closed__0 = _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lam__0___closed__0);
l_Lean_MVarId_byContra_x3f___lam__0___closed__1 = _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lam__0___closed__1);
l_Lean_MVarId_byContra_x3f___lam__0___closed__2 = _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lam__0___closed__2);
l_Lean_MVarId_byContra_x3f___lam__0___closed__3 = _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__3();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lam__0___closed__3);
l_Lean_MVarId_byContra_x3f___lam__0___closed__4 = _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__4();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lam__0___closed__4);
l_Lean_MVarId_byContra_x3f___lam__0___closed__5 = _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__5();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lam__0___closed__5);
l_Lean_MVarId_byContra_x3f___lam__0___closed__6 = _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lam__0___closed__6);
l_Lean_MVarId_byContra_x3f___closed__0 = _init_l_Lean_MVarId_byContra_x3f___closed__0();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___closed__0);
l_Lean_MVarId_byContra_x3f___closed__1 = _init_l_Lean_MVarId_byContra_x3f___closed__1();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___closed__1);
l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__0);
l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__1);
l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__2);
l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__3);
l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__4 = _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__4);
l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__5 = _init_l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_MVarId_clearAuxDecls_spec__5___redArg___closed__5);
l_Lean_MVarId_clearAuxDecls___closed__0 = _init_l_Lean_MVarId_clearAuxDecls___closed__0();
lean_mark_persistent(l_Lean_MVarId_clearAuxDecls___closed__0);
l_Lean_MVarId_clearAuxDecls___closed__1 = _init_l_Lean_MVarId_clearAuxDecls___closed__1();
lean_mark_persistent(l_Lean_MVarId_clearAuxDecls___closed__1);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__0 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__0);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__1 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__1);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__2 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__2);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__3 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__3);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__4 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__4);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__5 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__5);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__6 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__6);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__7 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__7);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__8 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__8);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__9 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__9);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__10 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__10);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__11 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lam__2___closed__11);
l_Lean_Meta_Grind_foldProjs___lam__2___closed__12 = _init_l_Lean_Meta_Grind_foldProjs___lam__2___closed__12();
l_Lean_Meta_Grind_normalizeLevels___closed__0 = _init_l_Lean_Meta_Grind_normalizeLevels___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeLevels___closed__0);
l_Lean_Meta_Grind_markAsMatchCond___closed__0 = _init_l_Lean_Meta_Grind_markAsMatchCond___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_markAsMatchCond___closed__0);
l_Lean_Meta_Grind_markAsMatchCond___closed__1 = _init_l_Lean_Meta_Grind_markAsMatchCond___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markAsMatchCond___closed__1);
l_Lean_Meta_Grind_markAsMatchCond___closed__2 = _init_l_Lean_Meta_Grind_markAsMatchCond___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_markAsMatchCond___closed__2);
l_Lean_Meta_Grind_markAsPreMatchCond___closed__0 = _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_markAsPreMatchCond___closed__0);
l_Lean_Meta_Grind_markAsPreMatchCond___closed__1 = _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1);
l_Lean_Meta_Grind_markAsPreMatchCond___closed__2 = _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__0____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_ = _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__0____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__0____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_);
l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_ = _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_);
l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__2____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_ = _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__2____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__2____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_);
l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__3____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_ = _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__3____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__3____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_);
l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__4____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_ = _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__4____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__4____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_);
l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__5____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_ = _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__5____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__5____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_);
l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__6____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_ = _init_l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__6____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57___closed__6____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__57____x40_Lean_Meta_Tactic_Grind_Util___hyg_2170_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_replacePreMatchCond___closed__0 = _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_replacePreMatchCond___closed__0);
l_Lean_Meta_Grind_replacePreMatchCond___closed__1 = _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_replacePreMatchCond___closed__1);
l_Lean_Meta_Grind_isIte___closed__0 = _init_l_Lean_Meta_Grind_isIte___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_isIte___closed__0);
l_Lean_Meta_Grind_isIte___closed__1 = _init_l_Lean_Meta_Grind_isIte___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_isIte___closed__1);
l_Lean_Meta_Grind_isDIte___closed__0 = _init_l_Lean_Meta_Grind_isDIte___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_isDIte___closed__0);
l_Lean_Meta_Grind_isDIte___closed__1 = _init_l_Lean_Meta_Grind_isDIte___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_isDIte___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
