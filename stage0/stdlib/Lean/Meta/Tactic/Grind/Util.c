// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Util
// Imports: Init.Simproc Lean.Meta.AbstractNestedProofs Lean.Meta.Transform Lean.Meta.Tactic.Util Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Simp.Simproc
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_betaReduce___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__7;
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_normalizeLevels___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___closed__2;
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__3;
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__2;
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_replacePreMatchCond___closed__1;
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__1;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_MVarId_ensureProp___closed__4;
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__4;
static lean_object* l_Lean_MVarId_unfoldReducible___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__4;
static lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___closed__5;
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__9;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isGrindGadget(lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object*);
static lean_object* l_Lean_MVarId_clearAuxDecls___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_betaReduce___closed__1;
static lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__2;
static lean_object* l_Lean_MVarId_byContra_x3f___closed__1;
static lean_object* l_Lean_MVarId_ensureProp___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___closed__1;
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__4;
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___closed__2;
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__6;
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reducePreMatchCond___closed__1;
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709_(lean_object*);
static lean_object* l_Lean_Meta_Grind_isGrindGadget___closed__3;
static lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__2;
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__7;
static lean_object* l_Lean_MVarId_ensureProp___closed__2;
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__6;
static lean_object* l_Lean_MVarId_betaReduce___lambda__1___closed__2;
static uint64_t l_Lean_Meta_Grind_foldProjs___lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_clearAuxDecls___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__2;
uint8_t l_Lean_Expr_isFalse(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__1;
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__5;
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_MVarId_ensureProp___closed__3;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_unfoldReducible___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Elab_Term_exposeLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__11;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGrindGadget___boxed(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_replacePreMatchCond___closed__2;
lean_object* l_Lean_Level_normalize(lean_object*);
static lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___closed__7;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__5;
static lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4;
static lean_object* l_Lean_Meta_Grind_unfoldReducible___closed__2;
static lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
lean_object* l_Lean_Core_betaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_Meta_Grind_normalizeLevels___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_ensureNoMVar___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goal contains metavariables", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__5;
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
lean_dec(x_7);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_16 = l_Lean_MVarId_ensureNoMVar___closed__2;
x_17 = l_Lean_MVarId_ensureNoMVar___closed__6;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_16, x_1, x_17, x_2, x_3, x_4, x_5, x_13);
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
x_24 = l_Lean_MVarId_ensureNoMVar___closed__2;
x_25 = l_Lean_MVarId_ensureNoMVar___closed__6;
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_24, x_1, x_25, x_2, x_3, x_4, x_5, x_20);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_ensureProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goal is not a proposition", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_ensureProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureProp___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_ensureProp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureProp___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_ensureProp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_ensureProp___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_isProp(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_MVarId_ensureNoMVar___closed__2;
x_15 = l_Lean_MVarId_ensureProp___closed__4;
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_14, x_1, x_15, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_apply_6(x_3, x_15, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_4);
x_20 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_18, x_12, x_4, x_5, x_6, x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_21, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_8 = l_Lean_MVarId_ensureNoMVar___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_transformTarget___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("EqMatch", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_isGrindGadget___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__2;
x_3 = l_Lean_Meta_Grind_isGrindGadget___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isGrindGadget(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__4;
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
static lean_object* _init_l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Meta_Grind_isGrindGadget(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Meta_Grind_unfoldReducible___lambda__1(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Grind_unfoldReducible___lambda__2(x_1, x_8, x_19, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_8);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_Grind_unfoldReducible___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__3), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_unfoldReducible___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__4___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_Grind_unfoldReducible___closed__1;
x_8 = l_Lean_Meta_Grind_unfoldReducible___closed__2;
x_9 = l_Lean_Core_transform___at_Lean_Elab_Term_exposeLevelMVars___spec__1(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_unfoldReducible___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_unfoldReducible___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_unfoldReducible___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_unfoldReducible___closed__1() {
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
x_7 = l_Lean_MVarId_unfoldReducible___closed__1;
x_8 = l_Lean_MVarId_transformTarget(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractNestedProofs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_abstractNestedProofs), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_MVarId_transformTarget(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_MVarId_betaReduce___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_betaReduce___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_betaReduce___lambda__1___closed__1;
x_8 = l_Lean_MVarId_betaReduce___lambda__1___closed__2;
x_9 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_MVarId_betaReduce___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_betaReduce___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_MVarId_betaReduce___closed__1;
x_8 = l_Lean_MVarId_transformTarget(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_betaReduce___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byContra_x3f___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byContra_x3f___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Classical", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("byContradiction", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_byContra_x3f___lambda__1___closed__4;
x_2 = l_Lean_MVarId_byContra_x3f___lambda__1___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byContra_x3f___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_9 = l_Lean_mkNot(x_1);
x_10 = l_Lean_MVarId_byContra_x3f___lambda__1___closed__3;
x_11 = l_Lean_mkArrow(x_9, x_10, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_MVarId_getTag(x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_4);
x_17 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_12, x_15, x_4, x_5, x_6, x_7, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MVarId_byContra_x3f___lambda__1___closed__7;
lean_inc(x_18);
x_21 = l_Lean_mkAppB(x_20, x_1, x_18);
x_22 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_2, x_21, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = l_Lean_Expr_mvarId_x21(x_18);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_Expr_mvarId_x21(x_18);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_8);
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
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_10);
x_15 = lean_box(0);
x_16 = l_Lean_MVarId_byContra_x3f___lambda__1(x_12, x_1, x_15, x_3, x_4, x_5, x_6, x_13);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
lean_inc(x_18);
x_20 = l_Lean_Expr_isFalse(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_MVarId_byContra_x3f___lambda__1(x_18, x_1, x_21, x_3, x_4, x_5, x_6, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
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
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("by_contra", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__1;
x_2 = l_Lean_MVarId_byContra_x3f___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_byContra_x3f___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_byContra_x3f___lambda__2___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_byContra_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_byContra_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
lean_inc(x_18);
x_20 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2(x_1, x_16, x_18, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_8, 0, x_24);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_4);
x_30 = 1;
x_31 = lean_usize_add(x_7, x_30);
x_7 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_dec(x_8);
lean_inc(x_33);
x_34 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2(x_1, x_16, x_33, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_33);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
lean_inc(x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_42);
x_44 = 1;
x_45 = lean_usize_add(x_7, x_44);
x_7 = x_45;
x_8 = x_43;
x_13 = x_41;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_18 = 1;
x_19 = lean_usize_add(x_6, x_18);
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_6 = x_24;
x_7 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_LocalDecl_isAuxDecl(x_29);
if (x_30 == 0)
{
size_t x_31; size_t x_32; 
lean_dec(x_29);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_31 = 1;
x_32 = lean_usize_add(x_6, x_31);
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_34 = l_Lean_LocalDecl_fvarId(x_29);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_3);
x_36 = 1;
x_37 = lean_usize_add(x_6, x_36);
x_6 = x_37;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = l_Lean_LocalDecl_isAuxDecl(x_40);
if (x_41 == 0)
{
lean_object* x_42; size_t x_43; size_t x_44; 
lean_dec(x_40);
lean_inc(x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_39);
x_43 = 1;
x_44 = lean_usize_add(x_6, x_43);
x_6 = x_44;
x_7 = x_42;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_46 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
lean_inc(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_47);
x_49 = 1;
x_50 = lean_usize_add(x_6, x_49);
x_6 = x_50;
x_7 = x_48;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_array_size(x_9);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__3(x_1, x_9, x_10, x_11, x_9, x_13, x_14, x_12, x_4, x_5, x_6, x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___lambda__1(x_19, x_20, x_4, x_5, x_6, x_7, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
x_32 = lean_array_size(x_28);
x_33 = 0;
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__4(x_28, x_29, x_30, x_28, x_32, x_33, x_31, x_4, x_5, x_6, x_7, x_8);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___lambda__1(x_38, x_39, x_4, x_5, x_6, x_7, x_37);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_18 = 1;
x_19 = lean_usize_add(x_6, x_18);
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_6 = x_24;
x_7 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_LocalDecl_isAuxDecl(x_29);
if (x_30 == 0)
{
size_t x_31; size_t x_32; 
lean_dec(x_29);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_31 = 1;
x_32 = lean_usize_add(x_6, x_31);
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_34 = l_Lean_LocalDecl_fvarId(x_29);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_3);
x_36 = 1;
x_37 = lean_usize_add(x_6, x_36);
x_6 = x_37;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = l_Lean_LocalDecl_isAuxDecl(x_40);
if (x_41 == 0)
{
lean_object* x_42; size_t x_43; size_t x_44; 
lean_dec(x_40);
lean_inc(x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_39);
x_43 = 1;
x_44 = lean_usize_add(x_6, x_43);
x_6 = x_44;
x_7 = x_42;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_46 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
lean_inc(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_47);
x_49 = 1;
x_50 = lean_usize_add(x_6, x_49);
x_6 = x_50;
x_7 = x_48;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_9 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2(x_2, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_array_size(x_20);
x_24 = 0;
x_25 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__5(x_19, x_20, x_21, x_20, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_17);
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
lean_dec(x_27);
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
lean_dec(x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to clear local auxiliary declaration", 43, 43);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_16 = l_Lean_MVarId_clear(x_6, x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_15;
x_6 = x_17;
x_7 = lean_box(0);
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_16);
lean_dec(x_21);
x_25 = l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__4;
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_6, x_25, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = l_Lean_Exception_isInterrupt(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Exception_isRuntime(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
x_35 = l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__4;
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_6, x_35, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_32);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_32);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
lean_inc(x_2);
x_11 = l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6(x_1, x_2, x_10, x_2, x_2, x_3, lean_box(0), x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1(x_12, x_10, x_3, x_4, x_5, x_6, x_9);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_List_isEmpty___rarg(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_13);
x_18 = lean_box(0);
x_19 = l_Lean_MVarId_clearAuxDecls___lambda__1(x_2, x_15, x_1, x_18, x_3, x_4, x_5, x_6, x_16);
return x_19;
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_List_isEmpty___rarg(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_MVarId_clearAuxDecls___lambda__1(x_2, x_20, x_1, x_23, x_3, x_4, x_5, x_6, x_21);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_clearAuxDecls___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clear_aux_decls", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_clearAuxDecls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__1;
x_2 = l_Lean_MVarId_clearAuxDecls___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_clearAuxDecls___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_clearAuxDecls___lambda__2), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__4(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_clearAuxDecls___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_clearAuxDecls___spec__5(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_clearAuxDecls___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearAuxDecls___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_clearAuxDecls___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_9);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1;
x_6 = l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_ensureNoMVar___closed__1;
x_2 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found `Expr.proj` but `", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is not marked as structure", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found `Expr.proj` with invalid field index `", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__13() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
x_15 = l_Lean_getStructureInfo_x3f(x_14, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
x_16 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2;
x_17 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_16, x_2, x_3, x_4, x_5, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_10);
lean_dec(x_7);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_21, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = l_Lean_MessageData_ofName(x_7);
x_27 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
x_28 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_28);
lean_ctor_set(x_10, 0, x_17);
lean_inc(x_1);
x_29 = l_Lean_indentExpr(x_1);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_16, x_32, x_2, x_3, x_4, x_5, x_24);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_34, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_dec(x_17);
x_38 = l_Lean_MessageData_ofName(x_7);
x_39 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_41);
lean_ctor_set(x_10, 0, x_40);
lean_inc(x_1);
x_42 = l_Lean_indentExpr(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_16, x_45, x_2, x_3, x_4, x_5, x_37);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_47, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_47);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_8, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_52);
lean_dec(x_9);
x_55 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2;
x_56 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_55, x_2, x_3, x_4, x_5, x_13);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_15);
lean_free_object(x_10);
lean_dec(x_8);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_60, x_2, x_3, x_4, x_5, x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_56);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_56, 1);
x_64 = lean_ctor_get(x_56, 0);
lean_dec(x_64);
x_65 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 0, x_65);
x_66 = l_Lean_MessageData_ofFormat(x_15);
x_67 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10;
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_66);
lean_ctor_set(x_56, 0, x_67);
x_68 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_68);
lean_ctor_set(x_10, 0, x_56);
lean_inc(x_1);
x_69 = l_Lean_indentExpr(x_1);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_10);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_55, x_72, x_2, x_3, x_4, x_5, x_63);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_74, x_2, x_3, x_4, x_5, x_75);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
lean_dec(x_56);
x_78 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 0, x_78);
x_79 = l_Lean_MessageData_ofFormat(x_15);
x_80 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_82);
lean_ctor_set(x_10, 0, x_81);
lean_inc(x_1);
x_83 = l_Lean_indentExpr(x_1);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_10);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_55, x_86, x_2, x_3, x_4, x_5, x_77);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_88, x_2, x_3, x_4, x_5, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
lean_free_object(x_10);
lean_dec(x_1);
x_91 = lean_array_fget(x_52, x_8);
lean_dec(x_8);
lean_dec(x_52);
x_92 = lean_ctor_get(x_2, 0);
x_93 = lean_ctor_get_uint8(x_92, 0);
x_94 = lean_ctor_get_uint8(x_92, 1);
x_95 = lean_ctor_get_uint8(x_92, 2);
x_96 = lean_ctor_get_uint8(x_92, 3);
x_97 = lean_ctor_get_uint8(x_92, 4);
x_98 = lean_ctor_get_uint8(x_92, 5);
x_99 = lean_ctor_get_uint8(x_92, 6);
x_100 = lean_ctor_get_uint8(x_92, 7);
x_101 = lean_ctor_get_uint8(x_92, 8);
x_102 = lean_ctor_get_uint8(x_92, 10);
x_103 = lean_ctor_get_uint8(x_92, 11);
x_104 = lean_ctor_get_uint8(x_92, 12);
x_105 = lean_ctor_get_uint8(x_92, 13);
x_106 = lean_ctor_get_uint8(x_92, 14);
x_107 = lean_ctor_get_uint8(x_92, 15);
x_108 = lean_ctor_get_uint8(x_92, 16);
x_109 = lean_ctor_get_uint8(x_92, 17);
x_110 = 1;
x_111 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_111, 0, x_93);
lean_ctor_set_uint8(x_111, 1, x_94);
lean_ctor_set_uint8(x_111, 2, x_95);
lean_ctor_set_uint8(x_111, 3, x_96);
lean_ctor_set_uint8(x_111, 4, x_97);
lean_ctor_set_uint8(x_111, 5, x_98);
lean_ctor_set_uint8(x_111, 6, x_99);
lean_ctor_set_uint8(x_111, 7, x_100);
lean_ctor_set_uint8(x_111, 8, x_101);
lean_ctor_set_uint8(x_111, 9, x_110);
lean_ctor_set_uint8(x_111, 10, x_102);
lean_ctor_set_uint8(x_111, 11, x_103);
lean_ctor_set_uint8(x_111, 12, x_104);
lean_ctor_set_uint8(x_111, 13, x_105);
lean_ctor_set_uint8(x_111, 14, x_106);
lean_ctor_set_uint8(x_111, 15, x_107);
lean_ctor_set_uint8(x_111, 16, x_108);
lean_ctor_set_uint8(x_111, 17, x_109);
x_112 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_113 = 2;
x_114 = lean_uint64_shift_right(x_112, x_113);
x_115 = lean_uint64_shift_left(x_114, x_113);
x_116 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__13;
x_117 = lean_uint64_lor(x_115, x_116);
x_118 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_119 = lean_ctor_get(x_2, 1);
x_120 = lean_ctor_get(x_2, 2);
x_121 = lean_ctor_get(x_2, 3);
x_122 = lean_ctor_get(x_2, 4);
x_123 = lean_ctor_get(x_2, 5);
x_124 = lean_ctor_get(x_2, 6);
x_125 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_126 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
x_127 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_127, 0, x_111);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set(x_127, 4, x_122);
lean_ctor_set(x_127, 5, x_123);
lean_ctor_set(x_127, 6, x_124);
lean_ctor_set_uint64(x_127, sizeof(void*)*7, x_117);
lean_ctor_set_uint8(x_127, sizeof(void*)*7 + 8, x_118);
lean_ctor_set_uint8(x_127, sizeof(void*)*7 + 9, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*7 + 10, x_126);
x_128 = l_Lean_Meta_mkProjection(x_9, x_91, x_127, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_130);
lean_ctor_set(x_128, 0, x_15);
return x_128;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_128, 0);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_128);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_15);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
else
{
uint8_t x_134; 
lean_free_object(x_15);
x_134 = !lean_is_exclusive(x_128);
if (x_134 == 0)
{
return x_128;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_128, 0);
x_136 = lean_ctor_get(x_128, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_128);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_15, 0);
lean_inc(x_138);
lean_dec(x_15);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_array_get_size(x_139);
x_141 = lean_nat_dec_lt(x_8, x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_139);
lean_dec(x_9);
x_142 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2;
x_143 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_142, x_2, x_3, x_4, x_5, x_13);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_free_object(x_10);
lean_dec(x_8);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_box(0);
x_148 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_147, x_2, x_3, x_4, x_5, x_146);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_149 = lean_ctor_get(x_143, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_150 = x_143;
} else {
 lean_dec_ref(x_143);
 x_150 = lean_box(0);
}
x_151 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = l_Lean_MessageData_ofFormat(x_152);
x_154 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10;
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_150;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_156);
lean_ctor_set(x_10, 0, x_155);
lean_inc(x_1);
x_157 = l_Lean_indentExpr(x_1);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_10);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_142, x_160, x_2, x_3, x_4, x_5, x_149);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_162, x_2, x_3, x_4, x_5, x_163);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; lean_object* x_185; uint64_t x_186; uint64_t x_187; uint64_t x_188; uint64_t x_189; uint64_t x_190; uint64_t x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; 
lean_free_object(x_10);
lean_dec(x_1);
x_165 = lean_array_fget(x_139, x_8);
lean_dec(x_8);
lean_dec(x_139);
x_166 = lean_ctor_get(x_2, 0);
x_167 = lean_ctor_get_uint8(x_166, 0);
x_168 = lean_ctor_get_uint8(x_166, 1);
x_169 = lean_ctor_get_uint8(x_166, 2);
x_170 = lean_ctor_get_uint8(x_166, 3);
x_171 = lean_ctor_get_uint8(x_166, 4);
x_172 = lean_ctor_get_uint8(x_166, 5);
x_173 = lean_ctor_get_uint8(x_166, 6);
x_174 = lean_ctor_get_uint8(x_166, 7);
x_175 = lean_ctor_get_uint8(x_166, 8);
x_176 = lean_ctor_get_uint8(x_166, 10);
x_177 = lean_ctor_get_uint8(x_166, 11);
x_178 = lean_ctor_get_uint8(x_166, 12);
x_179 = lean_ctor_get_uint8(x_166, 13);
x_180 = lean_ctor_get_uint8(x_166, 14);
x_181 = lean_ctor_get_uint8(x_166, 15);
x_182 = lean_ctor_get_uint8(x_166, 16);
x_183 = lean_ctor_get_uint8(x_166, 17);
x_184 = 1;
x_185 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_185, 0, x_167);
lean_ctor_set_uint8(x_185, 1, x_168);
lean_ctor_set_uint8(x_185, 2, x_169);
lean_ctor_set_uint8(x_185, 3, x_170);
lean_ctor_set_uint8(x_185, 4, x_171);
lean_ctor_set_uint8(x_185, 5, x_172);
lean_ctor_set_uint8(x_185, 6, x_173);
lean_ctor_set_uint8(x_185, 7, x_174);
lean_ctor_set_uint8(x_185, 8, x_175);
lean_ctor_set_uint8(x_185, 9, x_184);
lean_ctor_set_uint8(x_185, 10, x_176);
lean_ctor_set_uint8(x_185, 11, x_177);
lean_ctor_set_uint8(x_185, 12, x_178);
lean_ctor_set_uint8(x_185, 13, x_179);
lean_ctor_set_uint8(x_185, 14, x_180);
lean_ctor_set_uint8(x_185, 15, x_181);
lean_ctor_set_uint8(x_185, 16, x_182);
lean_ctor_set_uint8(x_185, 17, x_183);
x_186 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_187 = 2;
x_188 = lean_uint64_shift_right(x_186, x_187);
x_189 = lean_uint64_shift_left(x_188, x_187);
x_190 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__13;
x_191 = lean_uint64_lor(x_189, x_190);
x_192 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_193 = lean_ctor_get(x_2, 1);
x_194 = lean_ctor_get(x_2, 2);
x_195 = lean_ctor_get(x_2, 3);
x_196 = lean_ctor_get(x_2, 4);
x_197 = lean_ctor_get(x_2, 5);
x_198 = lean_ctor_get(x_2, 6);
x_199 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_200 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
x_201 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_201, 0, x_185);
lean_ctor_set(x_201, 1, x_193);
lean_ctor_set(x_201, 2, x_194);
lean_ctor_set(x_201, 3, x_195);
lean_ctor_set(x_201, 4, x_196);
lean_ctor_set(x_201, 5, x_197);
lean_ctor_set(x_201, 6, x_198);
lean_ctor_set_uint64(x_201, sizeof(void*)*7, x_191);
lean_ctor_set_uint8(x_201, sizeof(void*)*7 + 8, x_192);
lean_ctor_set_uint8(x_201, sizeof(void*)*7 + 9, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*7 + 10, x_200);
x_202 = l_Lean_Meta_mkProjection(x_9, x_165, x_201, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_203);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_202, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_210 = x_202;
} else {
 lean_dec_ref(x_202);
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
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_10, 0);
x_213 = lean_ctor_get(x_10, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_10);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_7);
x_215 = l_Lean_getStructureInfo_x3f(x_214, x_7);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
lean_dec(x_9);
lean_dec(x_8);
x_216 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2;
x_217 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_216, x_2, x_3, x_4, x_5, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_7);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_box(0);
x_222 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_221, x_2, x_3, x_4, x_5, x_220);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_224 = x_217;
} else {
 lean_dec_ref(x_217);
 x_224 = lean_box(0);
}
x_225 = l_Lean_MessageData_ofName(x_7);
x_226 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4;
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(7, 2, 0);
} else {
 x_227 = x_224;
 lean_ctor_set_tag(x_227, 7);
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6;
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
lean_inc(x_1);
x_230 = l_Lean_indentExpr(x_1);
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_216, x_233, x_2, x_3, x_4, x_5, x_223);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_235, x_2, x_3, x_4, x_5, x_236);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
lean_dec(x_7);
x_238 = lean_ctor_get(x_215, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_239 = x_215;
} else {
 lean_dec_ref(x_215);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_array_get_size(x_240);
x_242 = lean_nat_dec_lt(x_8, x_241);
lean_dec(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
lean_dec(x_240);
lean_dec(x_9);
x_243 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2;
x_244 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_243, x_2, x_3, x_4, x_5, x_213);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_unbox(x_245);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_239);
lean_dec(x_8);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_248 = lean_box(0);
x_249 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_248, x_2, x_3, x_4, x_5, x_247);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
x_252 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
if (lean_is_scalar(x_239)) {
 x_253 = lean_alloc_ctor(3, 1, 0);
} else {
 x_253 = x_239;
 lean_ctor_set_tag(x_253, 3);
}
lean_ctor_set(x_253, 0, x_252);
x_254 = l_Lean_MessageData_ofFormat(x_253);
x_255 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10;
if (lean_is_scalar(x_251)) {
 x_256 = lean_alloc_ctor(7, 2, 0);
} else {
 x_256 = x_251;
 lean_ctor_set_tag(x_256, 7);
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12;
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
lean_inc(x_1);
x_259 = l_Lean_indentExpr(x_1);
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8;
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_243, x_262, x_2, x_3, x_4, x_5, x_250);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_264, x_2, x_3, x_4, x_5, x_265);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint8_t x_286; lean_object* x_287; uint64_t x_288; uint64_t x_289; uint64_t x_290; uint64_t x_291; uint64_t x_292; uint64_t x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_1);
x_267 = lean_array_fget(x_240, x_8);
lean_dec(x_8);
lean_dec(x_240);
x_268 = lean_ctor_get(x_2, 0);
x_269 = lean_ctor_get_uint8(x_268, 0);
x_270 = lean_ctor_get_uint8(x_268, 1);
x_271 = lean_ctor_get_uint8(x_268, 2);
x_272 = lean_ctor_get_uint8(x_268, 3);
x_273 = lean_ctor_get_uint8(x_268, 4);
x_274 = lean_ctor_get_uint8(x_268, 5);
x_275 = lean_ctor_get_uint8(x_268, 6);
x_276 = lean_ctor_get_uint8(x_268, 7);
x_277 = lean_ctor_get_uint8(x_268, 8);
x_278 = lean_ctor_get_uint8(x_268, 10);
x_279 = lean_ctor_get_uint8(x_268, 11);
x_280 = lean_ctor_get_uint8(x_268, 12);
x_281 = lean_ctor_get_uint8(x_268, 13);
x_282 = lean_ctor_get_uint8(x_268, 14);
x_283 = lean_ctor_get_uint8(x_268, 15);
x_284 = lean_ctor_get_uint8(x_268, 16);
x_285 = lean_ctor_get_uint8(x_268, 17);
x_286 = 1;
x_287 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_287, 0, x_269);
lean_ctor_set_uint8(x_287, 1, x_270);
lean_ctor_set_uint8(x_287, 2, x_271);
lean_ctor_set_uint8(x_287, 3, x_272);
lean_ctor_set_uint8(x_287, 4, x_273);
lean_ctor_set_uint8(x_287, 5, x_274);
lean_ctor_set_uint8(x_287, 6, x_275);
lean_ctor_set_uint8(x_287, 7, x_276);
lean_ctor_set_uint8(x_287, 8, x_277);
lean_ctor_set_uint8(x_287, 9, x_286);
lean_ctor_set_uint8(x_287, 10, x_278);
lean_ctor_set_uint8(x_287, 11, x_279);
lean_ctor_set_uint8(x_287, 12, x_280);
lean_ctor_set_uint8(x_287, 13, x_281);
lean_ctor_set_uint8(x_287, 14, x_282);
lean_ctor_set_uint8(x_287, 15, x_283);
lean_ctor_set_uint8(x_287, 16, x_284);
lean_ctor_set_uint8(x_287, 17, x_285);
x_288 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_289 = 2;
x_290 = lean_uint64_shift_right(x_288, x_289);
x_291 = lean_uint64_shift_left(x_290, x_289);
x_292 = l_Lean_Meta_Grind_foldProjs___lambda__2___closed__13;
x_293 = lean_uint64_lor(x_291, x_292);
x_294 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_295 = lean_ctor_get(x_2, 1);
x_296 = lean_ctor_get(x_2, 2);
x_297 = lean_ctor_get(x_2, 3);
x_298 = lean_ctor_get(x_2, 4);
x_299 = lean_ctor_get(x_2, 5);
x_300 = lean_ctor_get(x_2, 6);
x_301 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_302 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
x_303 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_303, 0, x_287);
lean_ctor_set(x_303, 1, x_295);
lean_ctor_set(x_303, 2, x_296);
lean_ctor_set(x_303, 3, x_297);
lean_ctor_set(x_303, 4, x_298);
lean_ctor_set(x_303, 5, x_299);
lean_ctor_set(x_303, 6, x_300);
lean_ctor_set_uint64(x_303, sizeof(void*)*7, x_293);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 8, x_294);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 9, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 10, x_302);
x_304 = l_Lean_Meta_mkProjection(x_9, x_267, x_303, x_3, x_4, x_5, x_213);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_307 = x_304;
} else {
 lean_dec_ref(x_304);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_308 = lean_alloc_ctor(0, 1, 0);
} else {
 x_308 = x_239;
 lean_ctor_set_tag(x_308, 0);
}
lean_ctor_set(x_308, 0, x_305);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_306);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_239);
x_310 = lean_ctor_get(x_304, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_304, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_312 = x_304;
} else {
 lean_dec_ref(x_304);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
}
}
else
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_314, 0, x_1);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_6);
return x_315;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_foldProjs___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_foldProjs___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_Grind_foldProjs___closed__1;
x_8 = l_Lean_Meta_Grind_foldProjs___closed__2;
x_9 = 0;
x_10 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_7, x_8, x_9, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_foldProjs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_foldProjs___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_foldProjs___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_normalizeLevels___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lean_Level_normalize(x_5);
x_7 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = l_Lean_Expr_sort___override(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_box(0);
lean_inc(x_16);
x_18 = l_List_mapTR_loop___at_Lean_Meta_Grind_normalizeLevels___spec__1(x_16, x_17);
x_19 = l_ptrEqList___rarg(x_16, x_18);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_20 = l_Lean_Expr_const___override(x_15, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeLevels___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Meta_Grind_normalizeLevels___closed__1;
x_6 = l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_normalizeLevels___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_grind_normalize(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MatchCond", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__2;
x_3 = l_Lean_Meta_Grind_markAsMatchCond___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_markAsMatchCond___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_markAsMatchCond___closed__3;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Grind_markAsMatchCond___closed__2;
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
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PreMatchCond", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_2 = l_Lean_Meta_Grind_isGrindGadget___closed__2;
x_3 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__3;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
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
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reducePreMatchCond___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___lambda__2___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Grind_reducePreMatchCond___closed__1;
x_14 = l_Lean_Expr_cleanupAnnotations(x_11);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_9(x_13, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Expr_appFnCleanup(x_14, lean_box(0));
x_19 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_apply_9(x_13, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Meta_Grind_reducePreMatchCond___lambda__1(x_1, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_reducePreMatchCond___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_reducePreMatchCond___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reducePreMatchCond", 18, 18);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_isGrindGadget___closed__1;
x_2 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__1;
x_3 = l_Lean_Meta_Grind_isGrindGadget___closed__2;
x_4 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__4;
x_2 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__6;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__3;
x_3 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__7;
x_4 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__8;
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__3;
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_Grind_markAsMatchCond(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Grind_replacePreMatchCond___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_replacePreMatchCond___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_Grind_replacePreMatchCond___lambda__3___closed__1;
lean_inc(x_1);
x_8 = l_Lean_Expr_cleanupAnnotations(x_1);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = l_Lean_Meta_Grind_replacePreMatchCond___lambda__2(x_1, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Expr_appArg(x_8, lean_box(0));
x_13 = l_Lean_Expr_appFnCleanup(x_8, lean_box(0));
x_14 = l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Grind_replacePreMatchCond___lambda__2(x_1, x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_apply_6(x_7, x_12, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_isPreMatchCond___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_replacePreMatchCond___lambda__3), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Grind_replacePreMatchCond___closed__1;
x_8 = lean_find_expr(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Grind_replacePreMatchCond___closed__2;
x_16 = l_Lean_Meta_Grind_unfoldReducible___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Core_transform___at_Lean_Elab_Term_exposeLevelMVars___spec__1(x_1, x_15, x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
x_20 = l_Lean_Meta_mkEqRefl(x_18, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
x_23 = l_Lean_Meta_mkEq(x_1, x_18, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_mkExpectedTypeHint(x_21, x_24, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_8, 0, x_28);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_8);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
lean_ctor_set(x_8, 0, x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_18);
lean_free_object(x_8);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
return x_17;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_17, 0);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_17);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
x_52 = l_Lean_Meta_Grind_replacePreMatchCond___closed__2;
x_53 = l_Lean_Meta_Grind_unfoldReducible___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_Core_transform___at_Lean_Elab_Term_exposeLevelMVars___spec__1(x_1, x_52, x_53, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_55);
x_57 = l_Lean_Meta_mkEqRefl(x_55, x_2, x_3, x_4, x_5, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_55);
x_60 = l_Lean_Meta_mkEq(x_1, x_55, x_2, x_3, x_4, x_5, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_mkExpectedTypeHint(x_58, x_61, x_2, x_3, x_4, x_5, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
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
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_68 = 1;
x_69 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_68);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_55);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_77 = x_60;
} else {
 lean_dec_ref(x_60);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_57, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_57, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_81 = x_57;
} else {
 lean_dec_ref(x_57);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_54, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_54, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_85 = x_54;
} else {
 lean_dec_ref(x_54);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_replacePreMatchCond___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_replacePreMatchCond___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
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
l_Lean_MVarId_ensureNoMVar___closed__6 = _init_l_Lean_MVarId_ensureNoMVar___closed__6();
lean_mark_persistent(l_Lean_MVarId_ensureNoMVar___closed__6);
l_Lean_MVarId_ensureProp___closed__1 = _init_l_Lean_MVarId_ensureProp___closed__1();
lean_mark_persistent(l_Lean_MVarId_ensureProp___closed__1);
l_Lean_MVarId_ensureProp___closed__2 = _init_l_Lean_MVarId_ensureProp___closed__2();
lean_mark_persistent(l_Lean_MVarId_ensureProp___closed__2);
l_Lean_MVarId_ensureProp___closed__3 = _init_l_Lean_MVarId_ensureProp___closed__3();
lean_mark_persistent(l_Lean_MVarId_ensureProp___closed__3);
l_Lean_MVarId_ensureProp___closed__4 = _init_l_Lean_MVarId_ensureProp___closed__4();
lean_mark_persistent(l_Lean_MVarId_ensureProp___closed__4);
l_Lean_Meta_Grind_isGrindGadget___closed__1 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__1);
l_Lean_Meta_Grind_isGrindGadget___closed__2 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__2);
l_Lean_Meta_Grind_isGrindGadget___closed__3 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__3);
l_Lean_Meta_Grind_isGrindGadget___closed__4 = _init_l_Lean_Meta_Grind_isGrindGadget___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_isGrindGadget___closed__4);
l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_unfoldReducible___lambda__1___closed__1);
l_Lean_Meta_Grind_unfoldReducible___closed__1 = _init_l_Lean_Meta_Grind_unfoldReducible___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_unfoldReducible___closed__1);
l_Lean_Meta_Grind_unfoldReducible___closed__2 = _init_l_Lean_Meta_Grind_unfoldReducible___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_unfoldReducible___closed__2);
l_Lean_MVarId_unfoldReducible___closed__1 = _init_l_Lean_MVarId_unfoldReducible___closed__1();
lean_mark_persistent(l_Lean_MVarId_unfoldReducible___closed__1);
l_Lean_MVarId_betaReduce___lambda__1___closed__1 = _init_l_Lean_MVarId_betaReduce___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_betaReduce___lambda__1___closed__1);
l_Lean_MVarId_betaReduce___lambda__1___closed__2 = _init_l_Lean_MVarId_betaReduce___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_betaReduce___lambda__1___closed__2);
l_Lean_MVarId_betaReduce___closed__1 = _init_l_Lean_MVarId_betaReduce___closed__1();
lean_mark_persistent(l_Lean_MVarId_betaReduce___closed__1);
l_Lean_MVarId_byContra_x3f___lambda__1___closed__1 = _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lambda__1___closed__1);
l_Lean_MVarId_byContra_x3f___lambda__1___closed__2 = _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lambda__1___closed__2);
l_Lean_MVarId_byContra_x3f___lambda__1___closed__3 = _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lambda__1___closed__3);
l_Lean_MVarId_byContra_x3f___lambda__1___closed__4 = _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lambda__1___closed__4);
l_Lean_MVarId_byContra_x3f___lambda__1___closed__5 = _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__5();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lambda__1___closed__5);
l_Lean_MVarId_byContra_x3f___lambda__1___closed__6 = _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__6();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lambda__1___closed__6);
l_Lean_MVarId_byContra_x3f___lambda__1___closed__7 = _init_l_Lean_MVarId_byContra_x3f___lambda__1___closed__7();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___lambda__1___closed__7);
l_Lean_MVarId_byContra_x3f___closed__1 = _init_l_Lean_MVarId_byContra_x3f___closed__1();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___closed__1);
l_Lean_MVarId_byContra_x3f___closed__2 = _init_l_Lean_MVarId_byContra_x3f___closed__2();
lean_mark_persistent(l_Lean_MVarId_byContra_x3f___closed__2);
l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__1);
l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__2);
l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__3);
l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_MVarId_clearAuxDecls___spec__6___closed__4);
l_Lean_MVarId_clearAuxDecls___closed__1 = _init_l_Lean_MVarId_clearAuxDecls___closed__1();
lean_mark_persistent(l_Lean_MVarId_clearAuxDecls___closed__1);
l_Lean_MVarId_clearAuxDecls___closed__2 = _init_l_Lean_MVarId_clearAuxDecls___closed__2();
lean_mark_persistent(l_Lean_MVarId_clearAuxDecls___closed__2);
l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1 = _init_l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1);
l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2 = _init_l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__1);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__2);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__3);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__4);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__5);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__6);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__7 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__7);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__8);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__9 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__9);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__10);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__11 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__11);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___lambda__2___closed__12);
l_Lean_Meta_Grind_foldProjs___lambda__2___closed__13 = _init_l_Lean_Meta_Grind_foldProjs___lambda__2___closed__13();
l_Lean_Meta_Grind_foldProjs___closed__1 = _init_l_Lean_Meta_Grind_foldProjs___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___closed__1);
l_Lean_Meta_Grind_foldProjs___closed__2 = _init_l_Lean_Meta_Grind_foldProjs___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_foldProjs___closed__2);
l_Lean_Meta_Grind_normalizeLevels___closed__1 = _init_l_Lean_Meta_Grind_normalizeLevels___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_normalizeLevels___closed__1);
l_Lean_Meta_Grind_markAsMatchCond___closed__1 = _init_l_Lean_Meta_Grind_markAsMatchCond___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markAsMatchCond___closed__1);
l_Lean_Meta_Grind_markAsMatchCond___closed__2 = _init_l_Lean_Meta_Grind_markAsMatchCond___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_markAsMatchCond___closed__2);
l_Lean_Meta_Grind_markAsMatchCond___closed__3 = _init_l_Lean_Meta_Grind_markAsMatchCond___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_markAsMatchCond___closed__3);
l_Lean_Meta_Grind_markAsPreMatchCond___closed__1 = _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1);
l_Lean_Meta_Grind_markAsPreMatchCond___closed__2 = _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
l_Lean_Meta_Grind_markAsPreMatchCond___closed__3 = _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_markAsPreMatchCond___closed__3);
l_Lean_Meta_Grind_reducePreMatchCond___closed__1 = _init_l_Lean_Meta_Grind_reducePreMatchCond___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_reducePreMatchCond___closed__1);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__1 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__1);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__2 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__2);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__3 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__3);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__4 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__4);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__5 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__5);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__6 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__6);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__7 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__7);
l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__8 = _init_l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709____closed__8);
if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__1____x40_Lean_Meta_Tactic_Grind_Util___hyg_1709_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_replacePreMatchCond___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_replacePreMatchCond___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_replacePreMatchCond___lambda__3___closed__1);
l_Lean_Meta_Grind_replacePreMatchCond___closed__1 = _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_replacePreMatchCond___closed__1);
l_Lean_Meta_Grind_replacePreMatchCond___closed__2 = _init_l_Lean_Meta_Grind_replacePreMatchCond___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_replacePreMatchCond___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
