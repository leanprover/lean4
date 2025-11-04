// Lean compiler output
// Module: Lean.Elab.Tactic.Simpa
// Imports: public import Lean.Meta.Tactic.TryThis public import Lean.Elab.Tactic.Simp public import Lean.Elab.App
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
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3;
LEAN_EXPORT lean_object* l_linter_unnecessarySimpa;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1;
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0;
static lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4;
static lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6;
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__2;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__0;
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3;
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object**);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1;
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5;
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3;
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object*);
extern lean_object* l_Lean_warningAsError;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17;
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__20;
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12;
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7;
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7;
lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object**);
static lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__3;
static lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14;
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___closed__0;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__19;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__1;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___boxed(lean_object*);
static lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__3;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linter", 6, 6);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unnecessarySimpa", 16, 16);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
x_2 = l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enable the 'unnecessary simpa' linter", 37, 37);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
x_2 = l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
x_3 = l_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
x_4 = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(x_2, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_linter_unnecessarySimpa;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_3 = l_Lean_Linter_getLinterValue(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_11;
}
}
static lean_object* _init_l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Linter_linterSetsExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0;
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_9, x_6, x_5, x_8, x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__0;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
x_14 = lean_string_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__3;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__4;
x_18 = lean_string_dec_eq(x_9, x_17);
if (x_18 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
static lean_object* _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_109; uint8_t x_125; 
x_100 = 2;
x_125 = l_Lean_instBEqMessageSeverity_beq(x_3, x_100);
if (x_125 == 0)
{
x_109 = x_125;
goto block_124;
}
else
{
uint8_t x_126; 
lean_inc_ref(x_2);
x_126 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_109 = x_126;
goto block_124;
}
block_49:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_18);
x_21 = lean_ctor_get(x_17, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 7);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_20, 6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_11);
lean_ctor_set(x_27, 3, x_15);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = l_Lean_MessageLog_add(x_27, x_24);
lean_ctor_set(x_20, 6, x_28);
x_29 = lean_st_ref_set(x_18, x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_ctor_get(x_20, 5);
x_38 = lean_ctor_get(x_20, 6);
x_39 = lean_ctor_get(x_20, 7);
x_40 = lean_ctor_get(x_20, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_22);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_13);
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_14);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_15);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_4);
x_44 = l_Lean_MessageLog_add(x_43, x_38);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_44);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
x_46 = lean_st_ref_set(x_18, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_76:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_59 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(x_58, x_5, x_6, x_7, x_8);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_53);
x_62 = l_Lean_FileMap_toPosition(x_53, x_55);
lean_dec(x_55);
x_63 = l_Lean_FileMap_toPosition(x_53, x_57);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
if (x_52 == 0)
{
lean_free_object(x_59);
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_64;
x_12 = x_54;
x_13 = x_61;
x_14 = x_56;
x_15 = x_65;
x_16 = x_62;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_66; 
lean_inc(x_61);
x_66 = l_Lean_MessageData_hasTag(x_50, x_61);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_56);
lean_dec_ref(x_7);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_free_object(x_59);
x_10 = x_51;
x_11 = x_64;
x_12 = x_54;
x_13 = x_61;
x_14 = x_56;
x_15 = x_65;
x_16 = x_62;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
lean_inc_ref(x_53);
x_69 = l_Lean_FileMap_toPosition(x_53, x_55);
lean_dec(x_55);
x_70 = l_Lean_FileMap_toPosition(x_53, x_57);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
if (x_52 == 0)
{
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_71;
x_12 = x_54;
x_13 = x_68;
x_14 = x_56;
x_15 = x_72;
x_16 = x_69;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_73; 
lean_inc(x_68);
x_73 = l_Lean_MessageData_hasTag(x_50, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_56);
lean_dec_ref(x_7);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
x_10 = x_51;
x_11 = x_71;
x_12 = x_54;
x_13 = x_68;
x_14 = x_56;
x_15 = x_72;
x_16 = x_69;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
}
block_87:
{
lean_object* x_85; 
x_85 = l_Lean_Syntax_getTailPos_x3f(x_81, x_78);
lean_dec(x_81);
if (lean_obj_tag(x_85) == 0)
{
lean_inc(x_84);
x_50 = x_77;
x_51 = x_78;
x_52 = x_80;
x_53 = x_79;
x_54 = x_82;
x_55 = x_84;
x_56 = x_83;
x_57 = x_84;
goto block_76;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_50 = x_77;
x_51 = x_78;
x_52 = x_80;
x_53 = x_79;
x_54 = x_82;
x_55 = x_84;
x_56 = x_83;
x_57 = x_86;
goto block_76;
}
}
block_99:
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_replaceRef(x_1, x_93);
lean_dec(x_93);
x_96 = l_Lean_Syntax_getPos_x3f(x_95, x_89);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_unsigned_to_nat(0u);
x_77 = x_88;
x_78 = x_89;
x_79 = x_91;
x_80 = x_90;
x_81 = x_95;
x_82 = x_94;
x_83 = x_92;
x_84 = x_97;
goto block_87;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_77 = x_88;
x_78 = x_89;
x_79 = x_91;
x_80 = x_90;
x_81 = x_95;
x_82 = x_94;
x_83 = x_92;
x_84 = x_98;
goto block_87;
}
}
block_108:
{
if (x_107 == 0)
{
x_88 = x_104;
x_89 = x_106;
x_90 = x_102;
x_91 = x_101;
x_92 = x_103;
x_93 = x_105;
x_94 = x_3;
goto block_99;
}
else
{
x_88 = x_104;
x_89 = x_106;
x_90 = x_102;
x_91 = x_101;
x_92 = x_103;
x_93 = x_105;
x_94 = x_100;
goto block_99;
}
}
block_124:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
x_112 = lean_ctor_get(x_7, 2);
x_113 = lean_ctor_get(x_7, 5);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_115 = lean_box(x_109);
x_116 = lean_box(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = 1;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_118);
if (x_119 == 0)
{
lean_inc(x_113);
lean_inc_ref(x_110);
lean_inc_ref(x_111);
x_101 = x_111;
x_102 = x_114;
x_103 = x_110;
x_104 = x_117;
x_105 = x_113;
x_106 = x_109;
x_107 = x_119;
goto block_108;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___closed__0;
x_121 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(x_112, x_120);
lean_inc(x_113);
lean_inc_ref(x_110);
lean_inc_ref(x_111);
x_101 = x_111;
x_102 = x_114;
x_103 = x_110;
x_104 = x_117;
x_105 = x_113;
x_106 = x_109;
x_107 = x_121;
goto block_108;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = 0;
x_14 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_12, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("This linter can be disabled with `set_option ", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" false`", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1;
lean_inc(x_14);
x_17 = l_Lean_MessageData_ofName(x_14);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
x_18 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_MessageData_note(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1;
lean_inc(x_24);
x_26 = l_Lean_MessageData_ofName(x_24);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_note(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_2, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_33;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10_spec__10___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
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
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10_spec__10___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10_spec__10___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10_spec__10___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Expr_hash(x_2);
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
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10_spec__10___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_6, x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___redArg(x_1, x_2, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_6, x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___redArg(x_1, x_2, x_8);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_instBEqMVarId_beq(x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___redArg(x_2, x_3, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___redArg(x_2, x_18, x_9);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 0);
x_23 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0;
lean_ctor_set(x_21, 0, x_26);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_19);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_2 = x_32;
x_3 = x_31;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_34, 0);
x_36 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
x_39 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_2 = x_44;
x_3 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_17);
lean_dec(x_2);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_dec(x_15);
x_47 = lean_ctor_get(x_17, 0);
lean_inc(x_47);
lean_dec_ref(x_17);
x_48 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(x_1, x_47, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_49 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_3);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_22; 
x_22 = l_Lean_Expr_hasExprMVar(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_2);
x_23 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___redArg(x_3, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
lean_inc_ref(x_2);
x_28 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__10___redArg(x_3, x_2, x_27);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec_ref(x_2);
x_30 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14(x_1, x_29, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_30;
}
case 5:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_2);
x_33 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(x_1, x_31, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_34);
lean_dec_ref(x_32);
return x_33;
}
else
{
lean_object* x_36; 
lean_dec_ref(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_2 = x_32;
x_3 = x_36;
goto _start;
}
}
case 6:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_2);
x_13 = x_38;
x_14 = x_39;
x_15 = x_28;
goto block_21;
}
case 7:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_41);
lean_dec_ref(x_2);
x_13 = x_40;
x_14 = x_41;
x_15 = x_28;
goto block_21;
}
case 8:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_44);
lean_dec_ref(x_2);
x_45 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(x_1, x_42, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_46);
lean_dec_ref(x_44);
lean_dec_ref(x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(x_1, x_43, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_50);
lean_dec_ref(x_44);
return x_49;
}
else
{
lean_object* x_52; 
lean_dec_ref(x_49);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_2 = x_44;
x_3 = x_52;
goto _start;
}
}
}
case 10:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_54);
lean_dec_ref(x_2);
x_2 = x_54;
x_3 = x_28;
goto _start;
}
case 11:
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_56);
lean_dec_ref(x_2);
x_2 = x_56;
x_3 = x_28;
goto _start;
}
default: 
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_2);
x_58 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_28);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_2);
x_61 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(x_1, x_13, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_17);
lean_dec_ref(x_14);
return x_16;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_2 = x_14;
x_3 = x_19;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasExprMVar(x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_2);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__4;
x_17 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec_ref(x_20);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_20);
x_23 = lean_box(x_12);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_25);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_25);
x_29 = lean_box(x_12);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l_Lean_instBEqMVarId_beq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l_Lean_instBEqMVarId_beq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19_spec__19___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19_spec__19___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l_Lean_instBEqMVarId_beq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l_Lean_instBEqMVarId_beq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__19___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 7);
x_10 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19___redArg(x_9, x_1, x_2);
lean_ctor_set(x_7, 7, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_23 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19___redArg(x_21, x_1, x_2);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set(x_24, 7, x_23);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set(x_5, 0, x_24);
x_25 = lean_st_ref_set(x_3, x_5);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_28, 5);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_28, 6);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_28, 7);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_28, 8);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
x_43 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19___redArg(x_40, x_1, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 9, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_44, 5, x_38);
lean_ctor_set(x_44, 6, x_39);
lean_ctor_set(x_44, 7, x_43);
lean_ctor_set(x_44, 8, x_41);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_30);
lean_ctor_set(x_45, 3, x_31);
lean_ctor_set(x_45, 4, x_32);
x_46 = lean_st_ref_set(x_3, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___redArg(x_1, x_2, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__0;
x_4 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 2);
lean_dec(x_10);
x_11 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2;
lean_ctor_set(x_8, 2, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_14);
lean_ctor_set(x_6, 7, x_18);
x_19 = lean_st_ref_set(x_1, x_6);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_6, 7);
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
x_24 = lean_ctor_get(x_6, 2);
x_25 = lean_ctor_get(x_6, 3);
x_26 = lean_ctor_get(x_6, 4);
x_27 = lean_ctor_get(x_6, 5);
x_28 = lean_ctor_get(x_6, 6);
x_29 = lean_ctor_get(x_6, 8);
lean_inc(x_29);
lean_inc(x_21);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_30 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_31 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 3, 1);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_30);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set(x_36, 4, x_26);
lean_ctor_set(x_36, 5, x_27);
lean_ctor_set(x_36, 6, x_28);
lean_ctor_set(x_36, 7, x_35);
lean_ctor_set(x_36, 8, x_29);
x_37 = lean_st_ref_set(x_1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_get(x_1);
x_14 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_14);
lean_inc(x_1);
x_16 = lean_apply_10(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_st_ref_take(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 2);
lean_dec(x_23);
x_24 = l_Lean_PersistentArray_push___redArg(x_10, x_18);
lean_ctor_set(x_21, 2, x_24);
x_25 = lean_st_ref_set(x_1, x_19);
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = l_Lean_PersistentArray_push___redArg(x_10, x_18);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_27);
lean_ctor_set(x_19, 7, x_31);
x_32 = lean_st_ref_set(x_1, x_19);
lean_dec(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_16, 0, x_33);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_19, 7);
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
x_37 = lean_ctor_get(x_19, 2);
x_38 = lean_ctor_get(x_19, 3);
x_39 = lean_ctor_get(x_19, 4);
x_40 = lean_ctor_get(x_19, 5);
x_41 = lean_ctor_get(x_19, 6);
x_42 = lean_ctor_get(x_19, 8);
lean_inc(x_42);
lean_inc(x_34);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_43 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_44 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_45);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_46 = x_34;
} else {
 lean_dec_ref(x_34);
 x_46 = lean_box(0);
}
x_47 = l_Lean_PersistentArray_push___redArg(x_10, x_18);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 3, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_43);
x_49 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_49, 2, x_37);
lean_ctor_set(x_49, 3, x_38);
lean_ctor_set(x_49, 4, x_39);
lean_ctor_set(x_49, 5, x_40);
lean_ctor_set(x_49, 6, x_41);
lean_ctor_set(x_49, 7, x_48);
lean_ctor_set(x_49, 8, x_42);
x_50 = lean_st_ref_set(x_1, x_49);
lean_dec(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_16, 0, x_51);
return x_16;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_52 = lean_ctor_get(x_16, 0);
lean_inc(x_52);
lean_dec(x_16);
x_53 = lean_st_ref_take(x_1);
x_54 = lean_ctor_get(x_53, 7);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 2);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_53, 3);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_53, 4);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_53, 5);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_53, 6);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_53, 8);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 lean_ctor_release(x_53, 5);
 lean_ctor_release(x_53, 6);
 lean_ctor_release(x_53, 7);
 lean_ctor_release(x_53, 8);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get_uint8(x_54, sizeof(void*)*3);
x_65 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 x_67 = x_54;
} else {
 lean_dec_ref(x_54);
 x_67 = lean_box(0);
}
x_68 = l_Lean_PersistentArray_push___redArg(x_10, x_52);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 3, 1);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_64);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 9, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_56);
lean_ctor_set(x_70, 2, x_57);
lean_ctor_set(x_70, 3, x_58);
lean_ctor_set(x_70, 4, x_59);
lean_ctor_set(x_70, 5, x_60);
lean_ctor_set(x_70, 6, x_61);
lean_ctor_set(x_70, 7, x_69);
lean_ctor_set(x_70, 8, x_62);
x_71 = lean_st_ref_set(x_1, x_70);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec_ref(x_10);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_16);
if (x_74 == 0)
{
return x_16;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_16, 0);
lean_inc(x_75);
lean_dec(x_16);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_st_ref_get(x_10);
x_13 = lean_ctor_get(x_12, 7);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
lean_dec_ref(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_2);
x_15 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_18 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_ctor_set_tag(x_18, 1);
x_21 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_18);
lean_dec_ref(x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_20);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_29);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_31 = x_30;
} else {
 lean_dec_ref(x_30);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec_ref(x_18);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; 
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec_ref(x_2);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Type mismatch: After simplification, term", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
lean_inc(x_1);
x_19 = l_Lean_MVarId_getType(x_1, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_mk_syntax_ident(x_2);
lean_inc(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_23 = l_Lean_Elab_Term_elabTerm(x_21, x_22, x_3, x_3, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_49; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_49 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_4, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_50 = x_49;
} else {
 lean_dec_ref(x_49);
 x_50 = lean_box(0);
}
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_24);
x_51 = lean_infer_type(x_24, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_63; uint8_t x_64; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_63 = l_Lean_Meta_Context_config(x_14);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get_uint8(x_14, sizeof(void*)*7);
x_66 = lean_ctor_get(x_14, 1);
x_67 = lean_ctor_get(x_14, 2);
x_68 = lean_ctor_get(x_14, 3);
x_69 = lean_ctor_get(x_14, 4);
x_70 = lean_ctor_get(x_14, 5);
x_71 = lean_ctor_get(x_14, 6);
x_72 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 1);
x_73 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_63, 7, x_9);
x_74 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_63);
x_75 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set_uint64(x_75, sizeof(void*)*1, x_74);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
x_76 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_66);
lean_ctor_set(x_76, 2, x_67);
lean_ctor_set(x_76, 3, x_68);
lean_ctor_set(x_76, 4, x_69);
lean_ctor_set(x_76, 5, x_70);
lean_ctor_set(x_76, 6, x_71);
lean_ctor_set_uint8(x_76, sizeof(void*)*7, x_65);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 1, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 2, x_73);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_52);
lean_inc(x_20);
x_77 = l_Lean_Meta_isExprDefEq(x_20, x_52, x_76, x_15, x_16, x_17);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
x_53 = x_79;
x_54 = lean_box(0);
goto block_62;
}
else
{
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec_ref(x_77);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
x_53 = x_81;
x_54 = lean_box(0);
goto block_62;
}
else
{
uint8_t x_82; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
else
{
uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; uint64_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_85 = lean_ctor_get_uint8(x_63, 0);
x_86 = lean_ctor_get_uint8(x_63, 1);
x_87 = lean_ctor_get_uint8(x_63, 2);
x_88 = lean_ctor_get_uint8(x_63, 3);
x_89 = lean_ctor_get_uint8(x_63, 4);
x_90 = lean_ctor_get_uint8(x_63, 5);
x_91 = lean_ctor_get_uint8(x_63, 6);
x_92 = lean_ctor_get_uint8(x_63, 8);
x_93 = lean_ctor_get_uint8(x_63, 9);
x_94 = lean_ctor_get_uint8(x_63, 10);
x_95 = lean_ctor_get_uint8(x_63, 11);
x_96 = lean_ctor_get_uint8(x_63, 12);
x_97 = lean_ctor_get_uint8(x_63, 13);
x_98 = lean_ctor_get_uint8(x_63, 14);
x_99 = lean_ctor_get_uint8(x_63, 15);
x_100 = lean_ctor_get_uint8(x_63, 16);
x_101 = lean_ctor_get_uint8(x_63, 17);
x_102 = lean_ctor_get_uint8(x_63, 18);
lean_dec(x_63);
x_103 = lean_ctor_get_uint8(x_14, sizeof(void*)*7);
x_104 = lean_ctor_get(x_14, 1);
x_105 = lean_ctor_get(x_14, 2);
x_106 = lean_ctor_get(x_14, 3);
x_107 = lean_ctor_get(x_14, 4);
x_108 = lean_ctor_get(x_14, 5);
x_109 = lean_ctor_get(x_14, 6);
x_110 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 1);
x_111 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 2);
x_112 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_112, 0, x_85);
lean_ctor_set_uint8(x_112, 1, x_86);
lean_ctor_set_uint8(x_112, 2, x_87);
lean_ctor_set_uint8(x_112, 3, x_88);
lean_ctor_set_uint8(x_112, 4, x_89);
lean_ctor_set_uint8(x_112, 5, x_90);
lean_ctor_set_uint8(x_112, 6, x_91);
lean_ctor_set_uint8(x_112, 7, x_9);
lean_ctor_set_uint8(x_112, 8, x_92);
lean_ctor_set_uint8(x_112, 9, x_93);
lean_ctor_set_uint8(x_112, 10, x_94);
lean_ctor_set_uint8(x_112, 11, x_95);
lean_ctor_set_uint8(x_112, 12, x_96);
lean_ctor_set_uint8(x_112, 13, x_97);
lean_ctor_set_uint8(x_112, 14, x_98);
lean_ctor_set_uint8(x_112, 15, x_99);
lean_ctor_set_uint8(x_112, 16, x_100);
lean_ctor_set_uint8(x_112, 17, x_101);
lean_ctor_set_uint8(x_112, 18, x_102);
x_113 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_112);
x_114 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint64(x_114, sizeof(void*)*1, x_113);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc_ref(x_105);
lean_inc(x_104);
x_115 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_104);
lean_ctor_set(x_115, 2, x_105);
lean_ctor_set(x_115, 3, x_106);
lean_ctor_set(x_115, 4, x_107);
lean_ctor_set(x_115, 5, x_108);
lean_ctor_set(x_115, 6, x_109);
lean_ctor_set_uint8(x_115, sizeof(void*)*7, x_103);
lean_ctor_set_uint8(x_115, sizeof(void*)*7 + 1, x_110);
lean_ctor_set_uint8(x_115, sizeof(void*)*7 + 2, x_111);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_52);
lean_inc(x_20);
x_116 = l_Lean_Meta_isExprDefEq(x_20, x_52, x_115, x_15, x_16, x_17);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
x_53 = x_118;
x_54 = lean_box(0);
goto block_62;
}
else
{
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec_ref(x_116);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
x_53 = x_120;
x_54 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_1);
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_122 = x_116;
} else {
 lean_dec_ref(x_116);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
}
block_62:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1;
lean_inc_ref(x_5);
x_56 = l_Lean_indentExpr(x_5);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_50)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_50;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_59);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_24);
x_61 = l_Lean_Elab_Term_throwTypeMismatchError___redArg(x_60, x_20, x_52, x_24, x_8, x_14, x_15, x_16, x_17);
lean_dec_ref(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = lean_box(0);
goto block_48;
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_61;
}
}
else
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_20);
lean_dec(x_8);
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = lean_box(0);
goto block_48;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_50);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_51);
if (x_124 == 0)
{
return x_51;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_51, 0);
lean_inc(x_125);
lean_dec(x_51);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_49;
}
block_48:
{
lean_object* x_34; 
x_34 = l_Lean_Meta_getMVars(x_5, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Elab_Tactic_filterOldMVars___redArg(x_35, x_6, x_30);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
x_38 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_37, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_38);
x_39 = l_Lean_Elab_Tactic_pushGoal___redArg(x_1, x_26);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_39);
x_40 = l_Lean_Name_mkStr1(x_7);
x_41 = l_Lean_Elab_Tactic_closeMainGoal___redArg(x_40, x_24, x_4, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_41;
}
else
{
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_7);
return x_39;
}
}
else
{
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_38;
}
}
else
{
uint8_t x_42; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_7);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_7);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_23);
if (x_127 == 0)
{
return x_23;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_23, 0);
lean_inc(x_128);
lean_dec(x_23);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_19);
if (x_130 == 0)
{
return x_19;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_19, 0);
lean_inc(x_131);
lean_dec(x_19);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_take(x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 2);
lean_dec(x_15);
lean_ctor_set(x_13, 2, x_1);
x_16 = lean_st_ref_set(x_9, x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_1);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_19);
lean_ctor_set(x_11, 7, x_22);
x_23 = lean_st_ref_set(x_9, x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_26 = lean_ctor_get(x_11, 7);
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
x_31 = lean_ctor_get(x_11, 4);
x_32 = lean_ctor_get(x_11, 5);
x_33 = lean_ctor_get(x_11, 6);
x_34 = lean_ctor_get(x_11, 8);
lean_inc(x_34);
lean_inc(x_26);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_35 = lean_ctor_get_uint8(x_26, sizeof(void*)*3);
x_36 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_37);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_38 = x_26;
} else {
 lean_dec_ref(x_26);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 3, 1);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_1);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_35);
x_40 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_29);
lean_ctor_set(x_40, 3, x_30);
lean_ctor_set(x_40, 4, x_31);
lean_ctor_set(x_40, 5, x_32);
lean_ctor_set(x_40, 6, x_33);
lean_ctor_set(x_40, 7, x_39);
lean_ctor_set(x_40, 8, x_34);
x_41 = lean_st_ref_set(x_9, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("this", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Occurs check failed: Expression", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ncontains the goal ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try `simp at ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` instead of `simpa using ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_10);
x_68 = lean_ctor_get(x_18, 2);
x_69 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1;
x_70 = l_Lean_LocalContext_findFromUserName_x3f(x_68, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_71 = l_Lean_MVarId_assumption(x_2, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_3);
return x_71;
}
else
{
lean_object* x_74; 
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_3);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec_ref(x_3);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
lean_dec(x_71);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec_ref(x_70);
x_79 = l_Lean_LocalDecl_fvarId(x_78);
lean_dec(x_78);
x_80 = lean_mk_empty_array_with_capacity(x_4);
x_81 = lean_array_push(x_80, x_79);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc_ref(x_3);
x_82 = l_Lean_Meta_simpGoal(x_2, x_5, x_6, x_7, x_8, x_81, x_3, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_84, 0);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_84);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_ctor_set(x_82, 0, x_3);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_82);
lean_dec_ref(x_3);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_MVarId_assumption(x_88, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
else
{
lean_object* x_92; 
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_87);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_87);
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
return x_89;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_82, 0);
lean_inc(x_96);
lean_dec(x_82);
x_97 = lean_ctor_get(x_96, 0);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
lean_dec(x_96);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_3);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_3);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_MVarId_assumption(x_101, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_103 = x_102;
} else {
 lean_dec_ref(x_102);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_100);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_100);
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_105);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_3);
x_108 = !lean_is_exclusive(x_82);
if (x_108 == 0)
{
return x_82;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_82, 0);
lean_inc(x_109);
lean_dec(x_82);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
lean_dec_ref(x_1);
x_257 = lean_st_ref_get(x_21);
x_258 = lean_ctor_get(x_257, 7);
lean_inc_ref(x_258);
lean_dec_ref(x_257);
x_259 = lean_ctor_get_uint8(x_258, sizeof(void*)*3);
lean_dec_ref(x_258);
if (x_259 == 0)
{
lean_dec_ref(x_13);
x_112 = x_14;
x_113 = x_15;
x_114 = x_16;
x_115 = x_17;
x_116 = x_18;
x_117 = x_19;
x_118 = x_20;
x_119 = x_21;
x_120 = lean_box(0);
goto block_256;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg(x_21);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
lean_dec_ref(x_260);
x_262 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 10, 1);
lean_closure_set(x_262, 0, x_261);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_263 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg(x_262, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_263) == 0)
{
lean_dec_ref(x_263);
x_112 = x_14;
x_113 = x_15;
x_114 = x_16;
x_115 = x_17;
x_116 = x_18;
x_117 = x_19;
x_118 = x_20;
x_119 = x_21;
x_120 = lean_box(0);
goto block_256;
}
else
{
uint8_t x_264; 
lean_dec(x_111);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
return x_263;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
return x_266;
}
}
}
block_256:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_st_ref_get(x_117);
x_122 = lean_box(0);
lean_inc(x_119);
lean_inc_ref(x_118);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_115);
lean_inc_ref(x_114);
lean_inc(x_113);
lean_inc_ref(x_112);
x_123 = l_Lean_Elab_Tactic_elabTerm(x_111, x_122, x_9, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
lean_inc(x_124);
x_125 = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(x_2, x_124, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
x_126 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_126);
lean_dec_ref(x_121);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec_ref(x_126);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_129 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3;
x_130 = l_Lean_indentExpr(x_124);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5;
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Expr_mvar___override(x_2);
x_135 = l_Lean_MessageData_ofExpr(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___redArg(x_136, x_116, x_117, x_118, x_119);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_126, 2);
lean_inc(x_141);
lean_dec_ref(x_126);
lean_inc(x_2);
x_142 = l_Lean_MVarId_getType(x_2, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc(x_2);
x_144 = l_Lean_MVarId_getTag(x_2, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
lean_inc_ref(x_116);
x_146 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_143, x_145, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = l_Lean_Expr_mvarId_x21(x_147);
x_149 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7;
lean_inc(x_119);
lean_inc_ref(x_118);
lean_inc(x_117);
lean_inc_ref(x_116);
lean_inc(x_124);
x_150 = l_Lean_MVarId_note(x_148, x_149, x_124, x_122, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_151, 1);
x_155 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_153);
x_156 = lean_array_push(x_155, x_153);
lean_inc(x_119);
lean_inc_ref(x_118);
lean_inc(x_117);
lean_inc_ref(x_116);
x_157 = l_Lean_Meta_simpGoal(x_154, x_5, x_6, x_7, x_8, x_156, x_3, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_ctor_get(x_158, 0);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
lean_dec(x_153);
lean_dec(x_141);
lean_dec_ref(x_10);
x_160 = !lean_is_exclusive(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_161 = lean_ctor_get(x_158, 1);
x_162 = lean_ctor_get(x_158, 0);
lean_dec(x_162);
lean_inc_ref(x_118);
x_163 = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_free_object(x_158);
lean_free_object(x_151);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_161;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
if (lean_obj_tag(x_124) == 1)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_124, 0);
x_167 = lean_ctor_get(x_116, 2);
lean_inc(x_166);
lean_inc_ref(x_167);
x_168 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_167, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_free_object(x_158);
lean_free_object(x_151);
lean_dec_ref(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_161;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_168);
if (x_11 == 0)
{
lean_free_object(x_158);
lean_free_object(x_151);
lean_dec_ref(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_161;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_169 = lean_ctor_get(x_118, 5);
lean_inc(x_169);
x_170 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_171 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9;
x_172 = l_Lean_MessageData_ofExpr(x_124);
lean_inc_ref(x_172);
lean_ctor_set_tag(x_158, 7);
lean_ctor_set(x_158, 1, x_172);
lean_ctor_set(x_158, 0, x_171);
x_173 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11;
lean_ctor_set_tag(x_151, 7);
lean_ctor_set(x_151, 1, x_173);
lean_ctor_set(x_151, 0, x_158);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_151);
lean_ctor_set(x_174, 1, x_172);
x_175 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13;
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_170, x_169, x_176, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
lean_dec(x_119);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_169);
lean_dec_ref(x_177);
x_23 = x_161;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
}
}
else
{
lean_free_object(x_158);
lean_free_object(x_151);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_161;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_ctor_get(x_158, 1);
lean_inc(x_178);
lean_dec(x_158);
lean_inc_ref(x_118);
x_179 = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_free_object(x_151);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_178;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
if (lean_obj_tag(x_124) == 1)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_124, 0);
x_183 = lean_ctor_get(x_116, 2);
lean_inc(x_182);
lean_inc_ref(x_183);
x_184 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_183, x_182);
if (lean_obj_tag(x_184) == 0)
{
lean_free_object(x_151);
lean_dec_ref(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_178;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_184);
if (x_11 == 0)
{
lean_free_object(x_151);
lean_dec_ref(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_178;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_185 = lean_ctor_get(x_118, 5);
lean_inc(x_185);
x_186 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_187 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9;
x_188 = l_Lean_MessageData_ofExpr(x_124);
lean_inc_ref(x_188);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11;
lean_ctor_set_tag(x_151, 7);
lean_ctor_set(x_151, 1, x_190);
lean_ctor_set(x_151, 0, x_189);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_151);
lean_ctor_set(x_191, 1, x_188);
x_192 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13;
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_186, x_185, x_193, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
lean_dec(x_119);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_185);
lean_dec_ref(x_194);
x_23 = x_178;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
}
}
else
{
lean_free_object(x_151);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_178;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_free_object(x_151);
x_195 = lean_ctor_get(x_159, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_158, 1);
lean_inc(x_196);
lean_dec(x_158);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_array_get_size(x_197);
x_200 = lean_nat_dec_lt(x_12, x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_dec(x_197);
x_32 = x_124;
x_33 = x_141;
x_34 = x_122;
x_35 = x_149;
x_36 = x_113;
x_37 = x_118;
x_38 = x_114;
x_39 = x_112;
x_40 = lean_box(0);
x_41 = x_147;
x_42 = x_116;
x_43 = x_117;
x_44 = x_198;
x_45 = x_119;
x_46 = x_196;
x_47 = x_115;
x_48 = x_153;
goto block_67;
}
else
{
lean_object* x_201; 
lean_dec(x_153);
x_201 = lean_array_fget(x_197, x_12);
lean_dec(x_197);
x_32 = x_124;
x_33 = x_141;
x_34 = x_122;
x_35 = x_149;
x_36 = x_113;
x_37 = x_118;
x_38 = x_114;
x_39 = x_112;
x_40 = lean_box(0);
x_41 = x_147;
x_42 = x_116;
x_43 = x_117;
x_44 = x_198;
x_45 = x_119;
x_46 = x_196;
x_47 = x_115;
x_48 = x_201;
goto block_67;
}
}
}
else
{
uint8_t x_202; 
lean_free_object(x_151);
lean_dec(x_153);
lean_dec(x_147);
lean_dec(x_141);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_2);
x_202 = !lean_is_exclusive(x_157);
if (x_202 == 0)
{
return x_157;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_157, 0);
lean_inc(x_203);
lean_dec(x_157);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_151, 0);
x_206 = lean_ctor_get(x_151, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_151);
x_207 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_205);
x_208 = lean_array_push(x_207, x_205);
lean_inc(x_119);
lean_inc_ref(x_118);
lean_inc(x_117);
lean_inc_ref(x_116);
x_209 = l_Lean_Meta_simpGoal(x_206, x_5, x_6, x_7, x_8, x_208, x_3, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = lean_ctor_get(x_210, 0);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_dec(x_205);
lean_dec(x_141);
lean_dec_ref(x_10);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
lean_inc_ref(x_118);
x_214 = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec_ref(x_214);
x_216 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_215);
lean_dec(x_215);
if (x_216 == 0)
{
lean_dec(x_213);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_212;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
if (lean_obj_tag(x_124) == 1)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_124, 0);
x_218 = lean_ctor_get(x_116, 2);
lean_inc(x_217);
lean_inc_ref(x_218);
x_219 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_218, x_217);
if (lean_obj_tag(x_219) == 0)
{
lean_dec(x_213);
lean_dec_ref(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_212;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_219);
if (x_11 == 0)
{
lean_dec(x_213);
lean_dec_ref(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_212;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_220 = lean_ctor_get(x_118, 5);
lean_inc(x_220);
x_221 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_222 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9;
x_223 = l_Lean_MessageData_ofExpr(x_124);
lean_inc_ref(x_223);
if (lean_is_scalar(x_213)) {
 x_224 = lean_alloc_ctor(7, 2, 0);
} else {
 x_224 = x_213;
 lean_ctor_set_tag(x_224, 7);
}
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11;
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_223);
x_228 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13;
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_221, x_220, x_229, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
lean_dec(x_119);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_220);
lean_dec_ref(x_230);
x_23 = x_212;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
}
}
else
{
lean_dec(x_213);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
x_23 = x_212;
x_24 = x_147;
x_25 = x_117;
x_26 = lean_box(0);
goto block_31;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_231 = lean_ctor_get(x_211, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_210, 1);
lean_inc(x_232);
lean_dec(x_210);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
x_235 = lean_array_get_size(x_233);
x_236 = lean_nat_dec_lt(x_12, x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_dec(x_233);
x_32 = x_124;
x_33 = x_141;
x_34 = x_122;
x_35 = x_149;
x_36 = x_113;
x_37 = x_118;
x_38 = x_114;
x_39 = x_112;
x_40 = lean_box(0);
x_41 = x_147;
x_42 = x_116;
x_43 = x_117;
x_44 = x_234;
x_45 = x_119;
x_46 = x_232;
x_47 = x_115;
x_48 = x_205;
goto block_67;
}
else
{
lean_object* x_237; 
lean_dec(x_205);
x_237 = lean_array_fget(x_233, x_12);
lean_dec(x_233);
x_32 = x_124;
x_33 = x_141;
x_34 = x_122;
x_35 = x_149;
x_36 = x_113;
x_37 = x_118;
x_38 = x_114;
x_39 = x_112;
x_40 = lean_box(0);
x_41 = x_147;
x_42 = x_116;
x_43 = x_117;
x_44 = x_234;
x_45 = x_119;
x_46 = x_232;
x_47 = x_115;
x_48 = x_237;
goto block_67;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_205);
lean_dec(x_147);
lean_dec(x_141);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_2);
x_238 = lean_ctor_get(x_209, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_239 = x_209;
} else {
 lean_dec_ref(x_209);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_147);
lean_dec(x_141);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_241 = !lean_is_exclusive(x_150);
if (x_241 == 0)
{
return x_150;
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_150, 0);
lean_inc(x_242);
lean_dec(x_150);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_242);
return x_243;
}
}
}
else
{
uint8_t x_244; 
lean_dec(x_141);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_244 = !lean_is_exclusive(x_146);
if (x_244 == 0)
{
return x_146;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_146, 0);
lean_inc(x_245);
lean_dec(x_146);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_247 = !lean_is_exclusive(x_144);
if (x_247 == 0)
{
return x_144;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_144, 0);
lean_inc(x_248);
lean_dec(x_144);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_141);
lean_dec(x_124);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_250 = !lean_is_exclusive(x_142);
if (x_250 == 0)
{
return x_142;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_142, 0);
lean_inc(x_251);
lean_dec(x_142);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
return x_252;
}
}
}
}
else
{
uint8_t x_253; 
lean_dec_ref(x_121);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_253 = !lean_is_exclusive(x_123);
if (x_253 == 0)
{
return x_123;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_123, 0);
lean_inc(x_254);
lean_dec(x_123);
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
}
}
}
block_31:
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___redArg(x_2, x_24, x_25);
lean_dec(x_25);
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
lean_object* x_30; 
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
}
block_67:
{
lean_object* x_49; 
lean_inc(x_45);
lean_inc_ref(x_37);
x_49 = l_Lean_Core_mkFreshUserName(x_35, x_37, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_45);
lean_inc_ref(x_37);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_50);
x_51 = l_Lean_MVarId_rename(x_44, x_48, x_50, x_42, x_43, x_37, x_45);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_box(x_9);
x_54 = lean_box(x_8);
x_55 = lean_box(x_11);
lean_inc(x_52);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed), 18, 9);
lean_closure_set(x_56, 0, x_52);
lean_closure_set(x_56, 1, x_50);
lean_closure_set(x_56, 2, x_53);
lean_closure_set(x_56, 3, x_54);
lean_closure_set(x_56, 4, x_32);
lean_closure_set(x_56, 5, x_33);
lean_closure_set(x_56, 6, x_10);
lean_closure_set(x_56, 7, x_34);
lean_closure_set(x_56, 8, x_55);
lean_inc(x_43);
x_57 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg(x_52, x_56, x_39, x_36, x_38, x_47, x_42, x_43, x_37, x_45);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
x_23 = x_46;
x_24 = x_41;
x_25 = x_43;
x_26 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_58; 
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_10);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_10);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_49);
if (x_64 == 0)
{
return x_49;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
lean_dec(x_49);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try 'simp' instead of 'simpa'", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_24; 
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_105; 
x_105 = lean_box(0);
x_24 = x_105;
goto block_104;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_13, 0);
lean_inc(x_106);
lean_dec_ref(x_13);
x_24 = x_106;
goto block_104;
}
block_104:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_mk_empty_array_with_capacity(x_1);
x_26 = lean_array_push(x_25, x_2);
x_27 = lean_array_push(x_26, x_24);
x_28 = lean_box(2);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_27);
x_30 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_29, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_16, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_mk_empty_array_with_capacity(x_4);
x_35 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1;
lean_inc(x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
x_37 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2;
x_38 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3;
x_39 = 5;
lean_inc_n(x_4, 2);
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_4);
lean_ctor_set(x_40, 3, x_4);
lean_ctor_set_usize(x_40, 4, x_39);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc_ref(x_42);
lean_inc(x_14);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_43 = l_Lean_Meta_simpGoal(x_33, x_5, x_6, x_14, x_7, x_34, x_42, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_ctor_get(x_44, 0);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_44);
lean_dec(x_31);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_inc_ref(x_21);
x_46 = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_46, 0, x_42);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_46);
x_50 = lean_ctor_get(x_21, 5);
lean_inc(x_50);
x_51 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_52 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6;
x_53 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_51, x_50, x_52, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_50);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_42);
return x_53;
}
else
{
lean_object* x_56; 
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_42);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_46, 0);
lean_inc(x_57);
lean_dec(x_46);
x_58 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_42);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_21, 5);
lean_inc(x_60);
x_61 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_62 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6;
x_63 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_61, x_60, x_62, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_60);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_64 = x_63;
} else {
 lean_dec_ref(x_63);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_42);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec_ref(x_42);
x_66 = lean_ctor_get(x_45, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 1);
lean_inc(x_67);
lean_dec(x_44);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_66, 1);
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_inc(x_69);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_71);
lean_ctor_set(x_66, 0, x_69);
x_72 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_66, x_16, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_72);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed), 11, 1);
lean_closure_set(x_73, 0, x_31);
x_74 = lean_box(x_10);
x_75 = lean_box(x_7);
x_76 = lean_box(x_12);
lean_inc(x_69);
x_77 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 22, 13);
lean_closure_set(x_77, 0, x_8);
lean_closure_set(x_77, 1, x_69);
lean_closure_set(x_77, 2, x_67);
lean_closure_set(x_77, 3, x_9);
lean_closure_set(x_77, 4, x_5);
lean_closure_set(x_77, 5, x_6);
lean_closure_set(x_77, 6, x_14);
lean_closure_set(x_77, 7, x_74);
lean_closure_set(x_77, 8, x_75);
lean_closure_set(x_77, 9, x_11);
lean_closure_set(x_77, 10, x_76);
lean_closure_set(x_77, 11, x_4);
lean_closure_set(x_77, 12, x_73);
x_78 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg(x_69, x_77, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_72);
if (x_79 == 0)
{
return x_72;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
lean_dec(x_72);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
lean_dec(x_66);
x_83 = lean_box(0);
lean_inc(x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_84, x_16, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_85);
x_86 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed), 11, 1);
lean_closure_set(x_86, 0, x_31);
x_87 = lean_box(x_10);
x_88 = lean_box(x_7);
x_89 = lean_box(x_12);
lean_inc(x_82);
x_90 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 22, 13);
lean_closure_set(x_90, 0, x_8);
lean_closure_set(x_90, 1, x_82);
lean_closure_set(x_90, 2, x_67);
lean_closure_set(x_90, 3, x_9);
lean_closure_set(x_90, 4, x_5);
lean_closure_set(x_90, 5, x_6);
lean_closure_set(x_90, 6, x_14);
lean_closure_set(x_90, 7, x_87);
lean_closure_set(x_90, 8, x_88);
lean_closure_set(x_90, 9, x_11);
lean_closure_set(x_90, 10, x_89);
lean_closure_set(x_90, 11, x_4);
lean_closure_set(x_90, 12, x_86);
x_91 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg(x_82, x_90, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_93 = x_85;
} else {
 lean_dec_ref(x_85);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_42);
lean_dec(x_31);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_43);
if (x_95 == 0)
{
return x_43;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_43, 0);
lean_inc(x_96);
lean_dec(x_43);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_31);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_98 = !lean_is_exclusive(x_32);
if (x_98 == 0)
{
return x_32;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_32, 0);
lean_inc(x_99);
lean_dec(x_32);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_30);
if (x_101 == 0)
{
return x_30;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_30, 0);
lean_inc(x_102);
lean_dec(x_30);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this:", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("using", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSimpa!_", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpa!", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17;
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(116u);
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16;
x_5 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tactic_simp_trace;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_464; lean_object* x_465; lean_object* x_478; 
x_64 = lean_ctor_get(x_31, 2);
x_65 = lean_ctor_get(x_31, 5);
x_66 = 0;
x_67 = l_Lean_SourceInfo_fromRef(x_65, x_66);
x_68 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3;
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_69 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_68);
lean_inc(x_67);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5;
x_72 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6;
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_488; 
x_488 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_478 = x_488;
goto block_487;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_24, 0);
lean_inc(x_489);
lean_dec_ref(x_24);
x_490 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_491 = lean_array_push(x_490, x_489);
x_478 = x_491;
goto block_487;
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
block_56:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_45 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set(x_48, 5, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_42);
x_50 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2;
x_51 = 4;
x_52 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_48, x_49, x_50, x_47, x_51, x_41, x_43);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_34 = x_39;
x_35 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_53; 
lean_dec_ref(x_39);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
block_63:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 5);
lean_inc(x_62);
x_39 = x_57;
x_40 = x_58;
x_41 = x_59;
x_42 = x_62;
x_43 = x_60;
x_44 = lean_box(0);
goto block_56;
}
block_89:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = l_Array_append___redArg(x_72, x_84);
lean_dec_ref(x_84);
lean_inc(x_77);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_71);
lean_ctor_set(x_86, 2, x_85);
lean_inc(x_77);
x_87 = l_Lean_Syntax_node5(x_77, x_5, x_79, x_78, x_83, x_73, x_86);
lean_inc(x_76);
x_88 = l_Lean_Syntax_node4(x_77, x_7, x_80, x_76, x_76, x_87);
x_57 = x_74;
x_58 = x_88;
x_59 = x_75;
x_60 = x_81;
x_61 = lean_box(0);
goto block_63;
}
block_109:
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Array_append___redArg(x_72, x_101);
lean_dec_ref(x_101);
lean_inc(x_93);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_71);
lean_ctor_set(x_103, 2, x_102);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_104; 
x_104 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_73 = x_103;
x_74 = x_92;
x_75 = x_91;
x_76 = x_90;
x_77 = x_93;
x_78 = x_94;
x_79 = x_95;
x_80 = x_96;
x_81 = x_97;
x_82 = lean_box(0);
x_83 = x_100;
x_84 = x_104;
goto block_89;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
lean_dec_ref(x_99);
x_106 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8;
lean_inc(x_93);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_93);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Array_mkArray2___redArg(x_107, x_105);
x_73 = x_103;
x_74 = x_92;
x_75 = x_91;
x_76 = x_90;
x_77 = x_93;
x_78 = x_94;
x_79 = x_95;
x_80 = x_96;
x_81 = x_97;
x_82 = lean_box(0);
x_83 = x_100;
x_84 = x_108;
goto block_89;
}
}
block_136:
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Array_append___redArg(x_72, x_121);
lean_dec_ref(x_121);
lean_inc(x_114);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_114);
lean_ctor_set(x_123, 1, x_71);
lean_ctor_set(x_123, 2, x_122);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_124; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_124 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_90 = x_113;
x_91 = x_112;
x_92 = x_111;
x_93 = x_114;
x_94 = x_115;
x_95 = x_116;
x_96 = x_117;
x_97 = x_118;
x_98 = lean_box(0);
x_99 = x_120;
x_100 = x_123;
x_101 = x_124;
goto block_109;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
lean_dec_ref(x_110);
x_126 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9;
x_127 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_126);
x_128 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10;
lean_inc(x_114);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_114);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Array_append___redArg(x_72, x_125);
lean_dec(x_125);
lean_inc(x_114);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_114);
lean_ctor_set(x_131, 1, x_71);
lean_ctor_set(x_131, 2, x_130);
x_132 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11;
lean_inc(x_114);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_114);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_114);
x_134 = l_Lean_Syntax_node3(x_114, x_127, x_129, x_131, x_133);
x_135 = l_Array_mkArray1___redArg(x_134);
x_90 = x_113;
x_91 = x_112;
x_92 = x_111;
x_93 = x_114;
x_94 = x_115;
x_95 = x_116;
x_96 = x_117;
x_97 = x_118;
x_98 = lean_box(0);
x_99 = x_120;
x_100 = x_123;
x_101 = x_135;
goto block_109;
}
}
block_157:
{
lean_object* x_149; lean_object* x_150; 
x_149 = l_Array_append___redArg(x_72, x_148);
lean_dec_ref(x_148);
lean_inc(x_141);
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_71);
lean_ctor_set(x_150, 2, x_149);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_151; 
x_151 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_110 = x_140;
x_111 = x_139;
x_112 = x_138;
x_113 = x_137;
x_114 = x_141;
x_115 = x_150;
x_116 = x_142;
x_117 = x_143;
x_118 = x_145;
x_119 = lean_box(0);
x_120 = x_147;
x_121 = x_151;
goto block_136;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_144, 0);
lean_inc(x_152);
lean_dec_ref(x_144);
x_153 = l_Lean_SourceInfo_fromRef(x_152, x_6);
lean_dec(x_152);
x_154 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12;
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Array_mkArray1___redArg(x_155);
x_110 = x_140;
x_111 = x_139;
x_112 = x_138;
x_113 = x_137;
x_114 = x_141;
x_115 = x_150;
x_116 = x_142;
x_117 = x_143;
x_118 = x_145;
x_119 = lean_box(0);
x_120 = x_147;
x_121 = x_156;
goto block_136;
}
}
block_184:
{
lean_object* x_173; 
lean_inc(x_164);
lean_inc_ref(x_167);
x_173 = lean_apply_9(x_8, x_172, x_163, x_162, x_165, x_158, x_169, x_167, x_164, lean_box(0));
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
lean_inc(x_174);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_9);
lean_inc(x_174);
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_71);
lean_ctor_set(x_176, 2, x_72);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_177; 
x_177 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_137 = x_176;
x_138 = x_167;
x_139 = x_159;
x_140 = x_160;
x_141 = x_174;
x_142 = x_170;
x_143 = x_175;
x_144 = x_171;
x_145 = x_164;
x_146 = lean_box(0);
x_147 = x_166;
x_148 = x_177;
goto block_157;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_168, 0);
lean_inc(x_178);
lean_dec_ref(x_168);
x_179 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_180 = lean_array_push(x_179, x_178);
x_137 = x_176;
x_138 = x_167;
x_139 = x_159;
x_140 = x_160;
x_141 = x_174;
x_142 = x_170;
x_143 = x_175;
x_144 = x_171;
x_145 = x_164;
x_146 = lean_box(0);
x_147 = x_166;
x_148 = x_180;
goto block_157;
}
}
else
{
uint8_t x_181; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_168);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_173);
if (x_181 == 0)
{
return x_173;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_173, 0);
lean_inc(x_182);
lean_dec(x_173);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
}
block_201:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = l_Array_append___redArg(x_72, x_196);
lean_dec_ref(x_196);
lean_inc(x_190);
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_71);
lean_ctor_set(x_198, 2, x_197);
lean_inc(x_190);
x_199 = l_Lean_Syntax_node5(x_190, x_5, x_188, x_189, x_187, x_194, x_198);
x_200 = l_Lean_Syntax_node2(x_190, x_195, x_193, x_199);
x_57 = x_185;
x_58 = x_200;
x_59 = x_186;
x_60 = x_192;
x_61 = lean_box(0);
goto block_63;
}
block_221:
{
lean_object* x_214; lean_object* x_215; 
x_214 = l_Array_append___redArg(x_72, x_213);
lean_dec_ref(x_213);
lean_inc(x_207);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_207);
lean_ctor_set(x_215, 1, x_71);
lean_ctor_set(x_215, 2, x_214);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_216; 
x_216 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_185 = x_203;
x_186 = x_202;
x_187 = x_204;
x_188 = x_205;
x_189 = x_206;
x_190 = x_207;
x_191 = lean_box(0);
x_192 = x_210;
x_193 = x_209;
x_194 = x_215;
x_195 = x_212;
x_196 = x_216;
goto block_201;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_211, 0);
lean_inc(x_217);
lean_dec_ref(x_211);
x_218 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8;
lean_inc(x_207);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_207);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Array_mkArray2___redArg(x_219, x_217);
x_185 = x_203;
x_186 = x_202;
x_187 = x_204;
x_188 = x_205;
x_189 = x_206;
x_190 = x_207;
x_191 = lean_box(0);
x_192 = x_210;
x_193 = x_209;
x_194 = x_215;
x_195 = x_212;
x_196 = x_220;
goto block_201;
}
}
block_248:
{
lean_object* x_234; lean_object* x_235; 
x_234 = l_Array_append___redArg(x_72, x_233);
lean_dec_ref(x_233);
lean_inc(x_227);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_71);
lean_ctor_set(x_235, 2, x_234);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_236; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_236 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_202 = x_224;
x_203 = x_223;
x_204 = x_235;
x_205 = x_225;
x_206 = x_226;
x_207 = x_227;
x_208 = lean_box(0);
x_209 = x_230;
x_210 = x_229;
x_211 = x_231;
x_212 = x_232;
x_213 = x_236;
goto block_221;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_237 = lean_ctor_get(x_222, 0);
lean_inc(x_237);
lean_dec_ref(x_222);
x_238 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9;
x_239 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_238);
x_240 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10;
lean_inc(x_227);
x_241 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_241, 0, x_227);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Array_append___redArg(x_72, x_237);
lean_dec(x_237);
lean_inc(x_227);
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_227);
lean_ctor_set(x_243, 1, x_71);
lean_ctor_set(x_243, 2, x_242);
x_244 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11;
lean_inc(x_227);
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_227);
lean_ctor_set(x_245, 1, x_244);
lean_inc(x_227);
x_246 = l_Lean_Syntax_node3(x_227, x_239, x_241, x_243, x_245);
x_247 = l_Array_mkArray1___redArg(x_246);
x_202 = x_224;
x_203 = x_223;
x_204 = x_235;
x_205 = x_225;
x_206 = x_226;
x_207 = x_227;
x_208 = lean_box(0);
x_209 = x_230;
x_210 = x_229;
x_211 = x_231;
x_212 = x_232;
x_213 = x_247;
goto block_221;
}
}
block_269:
{
lean_object* x_261; lean_object* x_262; 
x_261 = l_Array_append___redArg(x_72, x_260);
lean_dec_ref(x_260);
lean_inc(x_253);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_253);
lean_ctor_set(x_262, 1, x_71);
lean_ctor_set(x_262, 2, x_261);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_263; 
x_263 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_222 = x_251;
x_223 = x_250;
x_224 = x_249;
x_225 = x_252;
x_226 = x_262;
x_227 = x_253;
x_228 = lean_box(0);
x_229 = x_257;
x_230 = x_256;
x_231 = x_258;
x_232 = x_259;
x_233 = x_263;
goto block_248;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_254, 0);
lean_inc(x_264);
lean_dec_ref(x_254);
x_265 = l_Lean_SourceInfo_fromRef(x_264, x_6);
lean_dec(x_264);
x_266 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12;
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Array_mkArray1___redArg(x_267);
x_222 = x_251;
x_223 = x_250;
x_224 = x_249;
x_225 = x_252;
x_226 = x_262;
x_227 = x_253;
x_228 = lean_box(0);
x_229 = x_257;
x_230 = x_256;
x_231 = x_258;
x_232 = x_259;
x_233 = x_268;
goto block_248;
}
}
block_299:
{
if (lean_obj_tag(x_10) == 0)
{
x_158 = x_270;
x_159 = x_271;
x_160 = x_272;
x_161 = lean_box(0);
x_162 = x_275;
x_163 = x_276;
x_164 = x_277;
x_165 = x_278;
x_166 = x_279;
x_167 = x_280;
x_168 = x_285;
x_169 = x_281;
x_170 = x_282;
x_171 = x_283;
x_172 = x_284;
goto block_184;
}
else
{
if (x_274 == 0)
{
x_158 = x_270;
x_159 = x_271;
x_160 = x_272;
x_161 = lean_box(0);
x_162 = x_275;
x_163 = x_276;
x_164 = x_277;
x_165 = x_278;
x_166 = x_279;
x_167 = x_280;
x_168 = x_285;
x_169 = x_281;
x_170 = x_282;
x_171 = x_283;
x_172 = x_284;
goto block_184;
}
else
{
lean_object* x_286; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_inc(x_277);
lean_inc_ref(x_280);
x_286 = lean_apply_9(x_8, x_284, x_276, x_275, x_278, x_270, x_281, x_280, x_277, lean_box(0));
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
x_288 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13;
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_289 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_288);
x_290 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14;
lean_inc(x_287);
x_291 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_290);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_292; 
x_292 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_249 = x_280;
x_250 = x_271;
x_251 = x_272;
x_252 = x_282;
x_253 = x_287;
x_254 = x_283;
x_255 = lean_box(0);
x_256 = x_291;
x_257 = x_277;
x_258 = x_279;
x_259 = x_289;
x_260 = x_292;
goto block_269;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_285, 0);
lean_inc(x_293);
lean_dec_ref(x_285);
x_294 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_295 = lean_array_push(x_294, x_293);
x_249 = x_280;
x_250 = x_271;
x_251 = x_272;
x_252 = x_282;
x_253 = x_287;
x_254 = x_283;
x_255 = lean_box(0);
x_256 = x_291;
x_257 = x_277;
x_258 = x_279;
x_259 = x_289;
x_260 = x_295;
goto block_269;
}
}
else
{
uint8_t x_296; 
lean_dec(x_285);
lean_dec(x_283);
lean_dec(x_282);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_286);
if (x_296 == 0)
{
return x_286;
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_286, 0);
lean_inc(x_297);
lean_dec(x_286);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
}
}
}
}
block_331:
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_317 = lean_unsigned_to_nat(5u);
x_318 = l_Lean_Syntax_getArg(x_302, x_317);
lean_dec(x_302);
x_319 = l_Lean_Syntax_matchesNull(x_318, x_11);
lean_dec(x_11);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_301);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_320 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18;
lean_inc(x_315);
lean_inc_ref(x_314);
x_321 = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(x_320, x_308, x_309, x_310, x_311, x_312, x_313, x_314, x_315);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec_ref(x_321);
x_57 = x_300;
x_58 = x_322;
x_59 = x_314;
x_60 = x_315;
x_61 = lean_box(0);
goto block_63;
}
else
{
uint8_t x_323; 
lean_dec(x_315);
lean_dec_ref(x_314);
lean_dec_ref(x_300);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_321);
if (x_323 == 0)
{
return x_321;
}
else
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_321, 0);
lean_inc(x_324);
lean_dec(x_321);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
return x_325;
}
}
}
else
{
lean_object* x_326; 
x_326 = l_Lean_Syntax_getOptional_x3f(x_301);
lean_dec(x_301);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_box(0);
x_270 = x_312;
x_271 = x_300;
x_272 = x_307;
x_273 = lean_box(0);
x_274 = x_304;
x_275 = x_310;
x_276 = x_309;
x_277 = x_315;
x_278 = x_311;
x_279 = x_306;
x_280 = x_314;
x_281 = x_313;
x_282 = x_303;
x_283 = x_305;
x_284 = x_308;
x_285 = x_327;
goto block_299;
}
else
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_326);
if (x_328 == 0)
{
x_270 = x_312;
x_271 = x_300;
x_272 = x_307;
x_273 = lean_box(0);
x_274 = x_304;
x_275 = x_310;
x_276 = x_309;
x_277 = x_315;
x_278 = x_311;
x_279 = x_306;
x_280 = x_314;
x_281 = x_313;
x_282 = x_303;
x_283 = x_305;
x_284 = x_308;
x_285 = x_326;
goto block_299;
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_326, 0);
lean_inc(x_329);
lean_dec(x_326);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_329);
x_270 = x_312;
x_271 = x_300;
x_272 = x_307;
x_273 = lean_box(0);
x_274 = x_304;
x_275 = x_310;
x_276 = x_309;
x_277 = x_315;
x_278 = x_311;
x_279 = x_306;
x_280 = x_314;
x_281 = x_313;
x_282 = x_303;
x_283 = x_305;
x_284 = x_308;
x_285 = x_330;
goto block_299;
}
}
}
}
block_361:
{
lean_object* x_348; uint8_t x_349; 
x_348 = l_Lean_Syntax_getArg(x_333, x_12);
x_349 = l_Lean_Syntax_isNone(x_348);
if (x_349 == 0)
{
uint8_t x_350; 
lean_inc(x_348);
x_350 = l_Lean_Syntax_matchesNull(x_348, x_13);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_348);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_351 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18;
lean_inc(x_346);
lean_inc_ref(x_345);
x_352 = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(x_351, x_339, x_340, x_341, x_342, x_343, x_344, x_345, x_346);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_57 = x_332;
x_58 = x_353;
x_59 = x_345;
x_60 = x_346;
x_61 = lean_box(0);
goto block_63;
}
else
{
uint8_t x_354; 
lean_dec(x_346);
lean_dec_ref(x_345);
lean_dec_ref(x_332);
lean_dec(x_1);
x_354 = !lean_is_exclusive(x_352);
if (x_354 == 0)
{
return x_352;
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
lean_dec(x_352);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = l_Lean_Syntax_getArg(x_348, x_14);
lean_dec(x_14);
lean_dec(x_348);
x_358 = l_Lean_Syntax_getArgs(x_357);
lean_dec(x_357);
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_358);
x_300 = x_332;
x_301 = x_334;
x_302 = x_333;
x_303 = x_335;
x_304 = x_336;
x_305 = x_338;
x_306 = x_337;
x_307 = x_359;
x_308 = x_339;
x_309 = x_340;
x_310 = x_341;
x_311 = x_342;
x_312 = x_343;
x_313 = x_344;
x_314 = x_345;
x_315 = x_346;
x_316 = lean_box(0);
goto block_331;
}
}
else
{
lean_object* x_360; 
lean_dec(x_348);
lean_dec(x_14);
x_360 = lean_box(0);
x_300 = x_332;
x_301 = x_334;
x_302 = x_333;
x_303 = x_335;
x_304 = x_336;
x_305 = x_338;
x_306 = x_337;
x_307 = x_360;
x_308 = x_339;
x_309 = x_340;
x_310 = x_341;
x_311 = x_342;
x_312 = x_343;
x_313 = x_344;
x_314 = x_345;
x_315 = x_346;
x_316 = lean_box(0);
goto block_331;
}
}
block_401:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_362, 0);
x_367 = l_Lean_Syntax_unsetTrailing(x_364);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
x_368 = l_Lean_Elab_Tactic_mkSimpOnly(x_367, x_366, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; uint8_t x_370; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
lean_inc(x_369);
x_370 = l_Lean_Syntax_isOfKind(x_369, x_69);
lean_dec(x_69);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; 
lean_dec(x_369);
lean_dec(x_365);
lean_inc(x_65);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_371 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18;
lean_inc(x_32);
lean_inc_ref(x_31);
x_372 = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(x_371, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
lean_dec_ref(x_372);
x_39 = x_362;
x_40 = x_373;
x_41 = x_31;
x_42 = x_65;
x_43 = x_32;
x_44 = lean_box(0);
goto block_56;
}
else
{
uint8_t x_374; 
lean_dec_ref(x_362);
lean_dec(x_65);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_1);
x_374 = !lean_is_exclusive(x_372);
if (x_374 == 0)
{
return x_372;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
lean_dec(x_372);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
return x_376;
}
}
}
else
{
lean_object* x_377; uint8_t x_378; 
x_377 = l_Lean_Syntax_getArg(x_369, x_14);
lean_inc(x_377);
x_378 = l_Lean_Syntax_isOfKind(x_377, x_15);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_377);
lean_dec(x_369);
lean_dec(x_365);
lean_inc(x_65);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_379 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18;
lean_inc(x_32);
lean_inc_ref(x_31);
x_380 = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(x_379, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
lean_dec_ref(x_380);
x_39 = x_362;
x_40 = x_381;
x_41 = x_31;
x_42 = x_65;
x_43 = x_32;
x_44 = lean_box(0);
goto block_56;
}
else
{
uint8_t x_382; 
lean_dec_ref(x_362);
lean_dec(x_65);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_380);
if (x_382 == 0)
{
return x_380;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_380, 0);
lean_inc(x_383);
lean_dec(x_380);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_385 = l_Lean_Syntax_getArg(x_369, x_16);
lean_dec(x_16);
x_386 = l_Lean_Syntax_getArg(x_369, x_13);
x_387 = l_Lean_Syntax_isNone(x_386);
if (x_387 == 0)
{
uint8_t x_388; 
lean_inc(x_386);
x_388 = l_Lean_Syntax_matchesNull(x_386, x_14);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_377);
lean_dec(x_369);
lean_dec(x_365);
lean_inc(x_65);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_389 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18;
lean_inc(x_32);
lean_inc_ref(x_31);
x_390 = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(x_389, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_39 = x_362;
x_40 = x_391;
x_41 = x_31;
x_42 = x_65;
x_43 = x_32;
x_44 = lean_box(0);
goto block_56;
}
else
{
uint8_t x_392; 
lean_dec_ref(x_362);
lean_dec(x_65);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_1);
x_392 = !lean_is_exclusive(x_390);
if (x_392 == 0)
{
return x_390;
}
else
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_390, 0);
lean_inc(x_393);
lean_dec(x_390);
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_393);
return x_394;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = l_Lean_Syntax_getArg(x_386, x_11);
lean_dec(x_386);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
x_332 = x_362;
x_333 = x_369;
x_334 = x_385;
x_335 = x_377;
x_336 = x_378;
x_337 = x_365;
x_338 = x_396;
x_339 = x_25;
x_340 = x_26;
x_341 = x_27;
x_342 = x_28;
x_343 = x_29;
x_344 = x_30;
x_345 = x_31;
x_346 = x_32;
x_347 = lean_box(0);
goto block_361;
}
}
else
{
lean_object* x_397; 
lean_dec(x_386);
x_397 = lean_box(0);
x_332 = x_362;
x_333 = x_369;
x_334 = x_385;
x_335 = x_377;
x_336 = x_378;
x_337 = x_365;
x_338 = x_397;
x_339 = x_25;
x_340 = x_26;
x_341 = x_27;
x_342 = x_28;
x_343 = x_29;
x_344 = x_30;
x_345 = x_31;
x_346 = x_32;
x_347 = lean_box(0);
goto block_361;
}
}
}
}
else
{
uint8_t x_398; 
lean_dec(x_365);
lean_dec_ref(x_362);
lean_dec(x_69);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_398 = !lean_is_exclusive(x_368);
if (x_398 == 0)
{
return x_368;
}
else
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_368, 0);
lean_inc(x_399);
lean_dec(x_368);
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_399);
return x_400;
}
}
}
block_411:
{
if (lean_obj_tag(x_17) == 0)
{
x_362 = x_402;
x_363 = lean_box(0);
x_364 = x_404;
x_365 = x_17;
goto block_401;
}
else
{
uint8_t x_405; 
x_405 = !lean_is_exclusive(x_17);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_17, 0);
x_407 = l_Lean_Syntax_unsetTrailing(x_406);
lean_ctor_set(x_17, 0, x_407);
x_362 = x_402;
x_363 = lean_box(0);
x_364 = x_404;
x_365 = x_17;
goto block_401;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_17, 0);
lean_inc(x_408);
lean_dec(x_17);
x_409 = l_Lean_Syntax_unsetTrailing(x_408);
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_362 = x_402;
x_363 = lean_box(0);
x_364 = x_404;
x_365 = x_410;
goto block_401;
}
}
}
block_416:
{
if (x_415 == 0)
{
lean_dec(x_414);
lean_dec(x_69);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = x_412;
x_35 = lean_box(0);
goto block_38;
}
else
{
x_402 = x_412;
x_403 = lean_box(0);
x_404 = x_414;
goto block_411;
}
}
block_434:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_422 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_421, x_66);
x_423 = lean_box(x_6);
x_424 = lean_box(x_66);
x_425 = lean_box(x_19);
lean_inc_ref(x_9);
lean_inc(x_14);
lean_inc(x_17);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_16);
x_426 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 23, 13);
lean_closure_set(x_426, 0, x_16);
lean_closure_set(x_426, 1, x_1);
lean_closure_set(x_426, 2, x_71);
lean_closure_set(x_426, 3, x_11);
lean_closure_set(x_426, 4, x_422);
lean_closure_set(x_426, 5, x_417);
lean_closure_set(x_426, 6, x_423);
lean_closure_set(x_426, 7, x_17);
lean_closure_set(x_426, 8, x_14);
lean_closure_set(x_426, 9, x_424);
lean_closure_set(x_426, 10, x_9);
lean_closure_set(x_426, 11, x_425);
lean_closure_set(x_426, 12, x_20);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
x_427 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_418, x_426, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
lean_dec(x_418);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; uint8_t x_430; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
lean_dec_ref(x_427);
x_429 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__19;
x_430 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(x_64, x_429);
if (x_430 == 0)
{
if (lean_obj_tag(x_21) == 0)
{
x_412 = x_428;
x_413 = lean_box(0);
x_414 = x_419;
x_415 = x_430;
goto block_416;
}
else
{
x_412 = x_428;
x_413 = lean_box(0);
x_414 = x_419;
x_415 = x_19;
goto block_416;
}
}
else
{
x_402 = x_428;
x_403 = lean_box(0);
x_404 = x_419;
goto block_411;
}
}
else
{
uint8_t x_431; 
lean_dec(x_419);
lean_dec(x_69);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_431 = !lean_is_exclusive(x_427);
if (x_431 == 0)
{
return x_427;
}
else
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_427, 0);
lean_inc(x_432);
lean_dec(x_427);
x_433 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_433, 0, x_432);
return x_433;
}
}
}
block_463:
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_438 = l_Array_append___redArg(x_72, x_437);
lean_dec_ref(x_437);
lean_inc(x_67);
x_439 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_439, 0, x_67);
lean_ctor_set(x_439, 1, x_71);
lean_ctor_set(x_439, 2, x_438);
lean_inc(x_67);
x_440 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_440, 0, x_67);
lean_ctor_set(x_440, 1, x_71);
lean_ctor_set(x_440, 2, x_72);
lean_inc(x_69);
x_441 = l_Lean_Syntax_node6(x_67, x_69, x_70, x_18, x_436, x_435, x_439, x_440);
x_442 = 0;
x_443 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__20;
x_444 = lean_box(x_66);
x_445 = lean_box(x_442);
x_446 = lean_box(x_66);
lean_inc(x_441);
x_447 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_447, 0, x_441);
lean_closure_set(x_447, 1, x_444);
lean_closure_set(x_447, 2, x_445);
lean_closure_set(x_447, 3, x_446);
lean_closure_set(x_447, 4, x_443);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
x_448 = l_Lean_Elab_Tactic_withMainContext___redArg(x_447, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec_ref(x_448);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc_ref(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc_ref(x_451);
x_452 = lean_ctor_get(x_449, 2);
lean_inc(x_452);
lean_dec(x_449);
x_417 = x_451;
x_418 = x_452;
x_419 = x_441;
x_420 = lean_box(0);
x_421 = x_450;
goto block_434;
}
else
{
if (x_19 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_449, 0);
lean_inc_ref(x_453);
x_454 = lean_ctor_get(x_449, 1);
lean_inc_ref(x_454);
x_455 = lean_ctor_get(x_449, 2);
lean_inc(x_455);
lean_dec(x_449);
x_417 = x_454;
x_418 = x_455;
x_419 = x_441;
x_420 = lean_box(0);
x_421 = x_453;
goto block_434;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_456 = lean_ctor_get(x_449, 0);
lean_inc_ref(x_456);
x_457 = lean_ctor_get(x_449, 1);
lean_inc_ref(x_457);
x_458 = lean_ctor_get(x_449, 2);
lean_inc(x_458);
lean_dec(x_449);
x_459 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_456);
x_417 = x_457;
x_418 = x_458;
x_419 = x_441;
x_420 = lean_box(0);
x_421 = x_459;
goto block_434;
}
}
}
else
{
uint8_t x_460; 
lean_dec(x_441);
lean_dec(x_69);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_460 = !lean_is_exclusive(x_448);
if (x_460 == 0)
{
return x_448;
}
else
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_448, 0);
lean_inc(x_461);
lean_dec(x_448);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
return x_462;
}
}
}
block_477:
{
lean_object* x_466; lean_object* x_467; 
x_466 = l_Array_append___redArg(x_72, x_465);
lean_dec_ref(x_465);
lean_inc(x_67);
x_467 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_467, 0, x_67);
lean_ctor_set(x_467, 1, x_71);
lean_ctor_set(x_467, 2, x_466);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_468; 
x_468 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_435 = x_467;
x_436 = x_464;
x_437 = x_468;
goto block_463;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_469 = lean_ctor_get(x_22, 0);
x_470 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10;
lean_inc(x_67);
x_471 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_471, 0, x_67);
lean_ctor_set(x_471, 1, x_470);
x_472 = l_Array_append___redArg(x_72, x_469);
lean_inc(x_67);
x_473 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_473, 0, x_67);
lean_ctor_set(x_473, 1, x_71);
lean_ctor_set(x_473, 2, x_472);
x_474 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11;
lean_inc(x_67);
x_475 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_475, 0, x_67);
lean_ctor_set(x_475, 1, x_474);
x_476 = l_Array_mkArray3___redArg(x_471, x_473, x_475);
x_435 = x_467;
x_436 = x_464;
x_437 = x_476;
goto block_463;
}
}
block_487:
{
lean_object* x_479; lean_object* x_480; 
x_479 = l_Array_append___redArg(x_72, x_478);
lean_dec_ref(x_478);
lean_inc(x_67);
x_480 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_480, 0, x_67);
lean_ctor_set(x_480, 1, x_71);
lean_ctor_set(x_480, 2, x_479);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_481; 
x_481 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_464 = x_480;
x_465 = x_481;
goto block_477;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_482 = lean_ctor_get(x_23, 0);
x_483 = l_Lean_SourceInfo_fromRef(x_482, x_6);
x_484 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12;
x_485 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
x_486 = l_Array_mkArray1___redArg(x_485);
x_464 = x_480;
x_465 = x_486;
goto block_477;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpa", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_2 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9;
x_2 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpaArgsRest", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5;
x_2 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7;
x_2 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_12 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_13 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
x_14 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_15 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3;
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_197; uint8_t x_198; 
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed), 9, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_197 = l_Lean_Syntax_getArg(x_1, x_21);
x_198 = l_Lean_Syntax_isNone(x_197);
if (x_198 == 0)
{
uint8_t x_199; 
lean_inc(x_197);
x_199 = l_Lean_Syntax_matchesNull(x_197, x_21);
if (x_199 == 0)
{
lean_object* x_200; 
lean_dec(x_197);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_200 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = l_Lean_Syntax_getArg(x_197, x_19);
lean_dec(x_197);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_178 = x_202;
x_179 = x_2;
x_180 = x_3;
x_181 = x_4;
x_182 = x_5;
x_183 = x_6;
x_184 = x_7;
x_185 = x_8;
x_186 = x_9;
x_187 = lean_box(0);
goto block_196;
}
}
else
{
lean_object* x_203; 
lean_dec(x_197);
x_203 = lean_box(0);
x_178 = x_203;
x_179 = x_2;
x_180 = x_3;
x_181 = x_4;
x_182 = x_5;
x_183 = x_6;
x_184 = x_7;
x_185 = x_8;
x_186 = x_9;
x_187 = lean_box(0);
goto block_196;
}
block_50:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_box(x_16);
x_46 = lean_box(x_29);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 33, 24);
lean_closure_set(x_47, 0, x_20);
lean_closure_set(x_47, 1, x_11);
lean_closure_set(x_47, 2, x_12);
lean_closure_set(x_47, 3, x_13);
lean_closure_set(x_47, 4, x_38);
lean_closure_set(x_47, 5, x_45);
lean_closure_set(x_47, 6, x_15);
lean_closure_set(x_47, 7, x_18);
lean_closure_set(x_47, 8, x_14);
lean_closure_set(x_47, 9, x_41);
lean_closure_set(x_47, 10, x_19);
lean_closure_set(x_47, 11, x_25);
lean_closure_set(x_47, 12, x_31);
lean_closure_set(x_47, 13, x_21);
lean_closure_set(x_47, 14, x_22);
lean_closure_set(x_47, 15, x_32);
lean_closure_set(x_47, 16, x_43);
lean_closure_set(x_47, 17, x_36);
lean_closure_set(x_47, 18, x_46);
lean_closure_set(x_47, 19, x_42);
lean_closure_set(x_47, 20, x_26);
lean_closure_set(x_47, 21, x_34);
lean_closure_set(x_47, 22, x_27);
lean_closure_set(x_47, 23, x_44);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = l_Lean_Elab_Tactic_focus___redArg(x_48, x_33, x_39, x_40, x_37, x_28, x_24, x_30, x_35);
return x_49;
}
block_79:
{
lean_object* x_74; 
x_74 = l_Lean_Syntax_getOptional_x3f(x_60);
lean_dec(x_60);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_22 = x_51;
x_23 = lean_box(0);
x_24 = x_53;
x_25 = x_54;
x_26 = x_55;
x_27 = x_56;
x_28 = x_57;
x_29 = x_58;
x_30 = x_59;
x_31 = x_61;
x_32 = x_62;
x_33 = x_63;
x_34 = x_64;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_68;
x_39 = x_69;
x_40 = x_70;
x_41 = x_71;
x_42 = x_72;
x_43 = x_73;
x_44 = x_75;
goto block_50;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
x_22 = x_51;
x_23 = lean_box(0);
x_24 = x_53;
x_25 = x_54;
x_26 = x_55;
x_27 = x_56;
x_28 = x_57;
x_29 = x_58;
x_30 = x_59;
x_31 = x_61;
x_32 = x_62;
x_33 = x_63;
x_34 = x_64;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_68;
x_39 = x_69;
x_40 = x_70;
x_41 = x_71;
x_42 = x_72;
x_43 = x_73;
x_44 = x_74;
goto block_50;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_22 = x_51;
x_23 = lean_box(0);
x_24 = x_53;
x_25 = x_54;
x_26 = x_55;
x_27 = x_56;
x_28 = x_57;
x_29 = x_58;
x_30 = x_59;
x_31 = x_61;
x_32 = x_62;
x_33 = x_63;
x_34 = x_64;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_68;
x_39 = x_69;
x_40 = x_70;
x_41 = x_71;
x_42 = x_72;
x_43 = x_73;
x_44 = x_78;
goto block_50;
}
}
}
block_112:
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_unsigned_to_nat(4u);
x_103 = l_Lean_Syntax_getArg(x_93, x_102);
lean_dec(x_93);
x_104 = l_Lean_Syntax_isNone(x_103);
if (x_104 == 0)
{
uint8_t x_105; 
lean_inc(x_103);
x_105 = l_Lean_Syntax_matchesNull(x_103, x_100);
lean_dec(x_100);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_20);
lean_dec_ref(x_18);
x_106 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = l_Lean_Syntax_getArg(x_103, x_19);
x_108 = l_Lean_Syntax_getArg(x_103, x_21);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_108);
x_51 = x_80;
x_52 = lean_box(0);
x_53 = x_82;
x_54 = x_102;
x_55 = x_83;
x_56 = x_84;
x_57 = x_85;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_101;
x_65 = x_92;
x_66 = x_94;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = x_99;
x_72 = x_109;
x_73 = x_110;
goto block_79;
}
}
else
{
lean_object* x_111; 
lean_dec(x_103);
lean_dec(x_100);
x_111 = lean_box(0);
x_51 = x_80;
x_52 = lean_box(0);
x_53 = x_82;
x_54 = x_102;
x_55 = x_83;
x_56 = x_84;
x_57 = x_85;
x_58 = x_86;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_101;
x_65 = x_92;
x_66 = x_94;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = x_99;
x_72 = x_111;
x_73 = x_111;
goto block_79;
}
}
block_147:
{
lean_object* x_135; uint8_t x_136; 
x_135 = l_Lean_Syntax_getArg(x_121, x_122);
lean_dec(x_122);
x_136 = l_Lean_Syntax_isNone(x_135);
if (x_136 == 0)
{
uint8_t x_137; 
lean_inc(x_135);
x_137 = l_Lean_Syntax_matchesNull(x_135, x_21);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_20);
lean_dec_ref(x_18);
x_138 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = l_Lean_Syntax_getArg(x_135, x_19);
lean_dec(x_135);
x_140 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4;
lean_inc(x_139);
x_141 = l_Lean_Syntax_isOfKind(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_139);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_20);
lean_dec_ref(x_18);
x_142 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = l_Lean_Syntax_getArg(x_139, x_21);
lean_dec(x_139);
x_144 = l_Lean_Syntax_getArgs(x_143);
lean_dec(x_143);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_80 = x_113;
x_81 = lean_box(0);
x_82 = x_131;
x_83 = x_114;
x_84 = x_125;
x_85 = x_130;
x_86 = x_116;
x_87 = x_132;
x_88 = x_124;
x_89 = x_117;
x_90 = x_119;
x_91 = x_126;
x_92 = x_133;
x_93 = x_121;
x_94 = x_120;
x_95 = x_129;
x_96 = x_115;
x_97 = x_127;
x_98 = x_128;
x_99 = x_118;
x_100 = x_123;
x_101 = x_145;
goto block_112;
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_135);
x_146 = lean_box(0);
x_80 = x_113;
x_81 = lean_box(0);
x_82 = x_131;
x_83 = x_114;
x_84 = x_125;
x_85 = x_130;
x_86 = x_116;
x_87 = x_132;
x_88 = x_124;
x_89 = x_117;
x_90 = x_119;
x_91 = x_126;
x_92 = x_133;
x_93 = x_121;
x_94 = x_120;
x_95 = x_129;
x_96 = x_115;
x_97 = x_127;
x_98 = x_128;
x_99 = x_118;
x_100 = x_123;
x_101 = x_146;
goto block_112;
}
}
block_177:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_160 = lean_unsigned_to_nat(3u);
x_161 = l_Lean_Syntax_getArg(x_1, x_160);
lean_dec(x_1);
x_162 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6;
lean_inc(x_161);
x_163 = l_Lean_Syntax_isOfKind(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_20);
lean_dec_ref(x_18);
x_164 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = l_Lean_Syntax_getArg(x_161, x_19);
x_166 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8;
lean_inc(x_165);
x_167 = l_Lean_Syntax_isOfKind(x_165, x_166);
if (x_167 == 0)
{
lean_object* x_168; 
lean_dec(x_165);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_20);
lean_dec_ref(x_18);
x_168 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = l_Lean_Syntax_getArg(x_161, x_21);
x_170 = l_Lean_Syntax_getArg(x_161, x_156);
x_171 = l_Lean_Syntax_isNone(x_170);
if (x_171 == 0)
{
uint8_t x_172; 
lean_inc(x_170);
x_172 = l_Lean_Syntax_matchesNull(x_170, x_21);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_165);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_20);
lean_dec_ref(x_18);
x_173 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = l_Lean_Syntax_getArg(x_170, x_19);
lean_dec(x_170);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
lean_inc(x_156);
x_113 = x_166;
x_114 = x_149;
x_115 = x_162;
x_116 = x_167;
x_117 = x_160;
x_118 = x_159;
x_119 = x_156;
x_120 = x_165;
x_121 = x_161;
x_122 = x_160;
x_123 = x_156;
x_124 = x_169;
x_125 = x_175;
x_126 = x_155;
x_127 = x_157;
x_128 = x_152;
x_129 = x_151;
x_130 = x_154;
x_131 = x_150;
x_132 = x_153;
x_133 = x_148;
x_134 = lean_box(0);
goto block_147;
}
}
else
{
lean_object* x_176; 
lean_dec(x_170);
x_176 = lean_box(0);
lean_inc(x_156);
x_113 = x_166;
x_114 = x_149;
x_115 = x_162;
x_116 = x_167;
x_117 = x_160;
x_118 = x_159;
x_119 = x_156;
x_120 = x_165;
x_121 = x_161;
x_122 = x_160;
x_123 = x_156;
x_124 = x_169;
x_125 = x_176;
x_126 = x_155;
x_127 = x_157;
x_128 = x_152;
x_129 = x_151;
x_130 = x_154;
x_131 = x_150;
x_132 = x_153;
x_133 = x_148;
x_134 = lean_box(0);
goto block_147;
}
}
}
}
block_196:
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = lean_unsigned_to_nat(2u);
x_189 = l_Lean_Syntax_getArg(x_1, x_188);
x_190 = l_Lean_Syntax_isNone(x_189);
if (x_190 == 0)
{
uint8_t x_191; 
lean_inc(x_189);
x_191 = l_Lean_Syntax_matchesNull(x_189, x_21);
if (x_191 == 0)
{
lean_object* x_192; 
lean_dec(x_189);
lean_dec(x_186);
lean_dec_ref(x_185);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_180);
lean_dec_ref(x_179);
lean_dec(x_178);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_1);
x_192 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = l_Lean_Syntax_getArg(x_189, x_19);
lean_dec(x_189);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_148 = x_186;
x_149 = x_178;
x_150 = x_184;
x_151 = x_182;
x_152 = x_181;
x_153 = x_185;
x_154 = x_183;
x_155 = x_179;
x_156 = x_188;
x_157 = x_180;
x_158 = lean_box(0);
x_159 = x_194;
goto block_177;
}
}
else
{
lean_object* x_195; 
lean_dec(x_189);
x_195 = lean_box(0);
x_148 = x_186;
x_149 = x_178;
x_150 = x_184;
x_151 = x_182;
x_152 = x_181;
x_153 = x_185;
x_154 = x_183;
x_155 = x_179;
x_156 = x_188;
x_157 = x_180;
x_158 = lean_box(0);
x_159 = x_195;
goto block_177;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_4);
x_16 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8_spec__8(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__8(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19_spec__21(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_3);
x_20 = lean_unbox(x_4);
x_21 = lean_unbox(x_9);
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_2, x_19, x_20, x_5, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_unbox(x_8);
x_24 = lean_unbox(x_9);
x_25 = lean_unbox(x_11);
x_26 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23, x_24, x_10, x_25, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_12);
lean_dec(x_4);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_unbox(x_7);
x_25 = lean_unbox(x_10);
x_26 = lean_unbox(x_12);
x_27 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_24, x_8, x_9, x_25, x_11, x_26, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_1);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_unbox(x_6);
x_35 = lean_unbox(x_19);
x_36 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(x_1, x_2, x_3, x_4, x_5, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_35, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Simpa_evalSimpa(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simpa", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpa", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1;
x_3 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2;
x_4 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__1;
x_5 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = lean_unsigned_to_nat(90u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(43u);
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(47u);
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = _init_l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
lean_mark_persistent(l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_);
l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = _init_l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
lean_mark_persistent(l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_);
l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = _init_l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
lean_mark_persistent(l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_);
l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = _init_l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
lean_mark_persistent(l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_);
l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = _init_l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
lean_mark_persistent(l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_);
l_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = _init_l_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
lean_mark_persistent(l_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_);
res = l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_linter_unnecessarySimpa = lean_io_result_get_value(res);
lean_mark_persistent(l_linter_unnecessarySimpa);
lean_dec_ref(res);
l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__1);
l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0 = _init_l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0);
l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__0 = _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__0);
l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__1 = _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__1);
l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2 = _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__2);
l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__3 = _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__3);
l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__4 = _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___lam__0___closed__4);
l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___closed__0 = _init_l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___closed__0();
lean_mark_persistent(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___redArg___closed__0);
l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0 = _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0();
lean_mark_persistent(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0);
l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1 = _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1();
lean_mark_persistent(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1);
l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2 = _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2();
lean_mark_persistent(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2);
l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3 = _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3();
lean_mark_persistent(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3);
l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0 = _init_l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0();
lean_mark_persistent(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__0);
l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__1 = _init_l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__1();
lean_mark_persistent(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8_spec__8_spec__14___closed__1);
l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__0 = _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__0();
lean_mark_persistent(l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__0);
l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__1 = _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__1();
lean_mark_persistent(l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__1);
l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__2 = _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__2();
lean_mark_persistent(l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__2);
l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__3 = _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__3();
lean_mark_persistent(l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__3);
l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__4 = _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__4();
lean_mark_persistent(l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___closed__4);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__19_spec__19_spec__19___redArg___closed__2);
l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__0 = _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__0);
l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__1 = _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__1);
l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2 = _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__27___redArg___closed__2);
l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___closed__0 = _init_l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__29___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__19 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__19);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__20 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__20);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
